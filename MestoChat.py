import sys, os, socket, threading, json, time, struct, uuid, random, logging, zipfile, tempfile, shutil, sqlite3, hashlib, html
from datetime import datetime
from collections import defaultdict
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
from urllib.parse import quote
from typing import Optional, Dict, List, Tuple, Any

from PyQt5.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
    QListWidget, QListWidgetItem, QTextEdit, QLineEdit, QPushButton,
    QLabel, QMessageBox, QFileDialog, QSplitter, QSystemTrayIcon, QMenu, QAction,
    QDialog, QFormLayout, QDialogButtonBox, QStyle, QStackedWidget, QInputDialog,
    QSpinBox, QComboBox, QCheckBox
)
from PyQt5.QtCore import Qt, pyqtSignal, QObject, QTimer, QUrl
from PyQt5.QtGui import QFont, QDragEnterEvent, QDropEvent, QTextCursor, QDesktopServices, QPixmap, QDragMoveEvent

# ====================== КОНСТАНТЫ ======================
BUFFER_SIZE = 8192
UDP_BUFFER_SIZE = 4096
MAX_MESSAGE_SIZE = 10 * 1024 * 1024
MAX_PREAMBLE_SIZE = 128
MAX_HEADER_SIZE = 512
HEARTBEAT_INTERVAL = 3
HEARTBEAT_TIMEOUT = 9
PEER_TIMEOUT = 20
RECONNECT_BACKOFF_MAX = 30
MAX_RECONNECT_ATTEMPTS = 5
TRANSFER_TIMEOUT = 30
TRANSFER_PROGRESS_TIMEOUT = 10
MAX_HISTORY_MESSAGES = 10000
INACTIVE_PEER_CLEANUP_SECONDS = 600

class ConnectionState:
    NEW = "new"
    CONNECTING = "connecting"
    CONNECTED = "connected"
    ACTIVE = "active"
    DISCONNECTING = "disconnecting"
    DEAD = "dead"

# ====================== КОНФИГУРАЦИЯ ======================
DATA_DIR = os.path.join(os.getenv('APPDATA', os.path.expanduser('~')), 'MestoChat')
os.makedirs(DATA_DIR, exist_ok=True)
CONFIG_PATH = os.path.join(DATA_DIR, 'config.json')
LOG_PATH = os.path.join(DATA_DIR, 'error.log')
DB_PATH = os.path.join(DATA_DIR, 'mestochat.db')
MACHINE_ID_PATH = os.path.join(DATA_DIR, 'machine_id')
DEFAULT_DOWNLOADS_DIR = os.path.join(os.path.expanduser("~"), "Downloads", "MestoChat")

DEFAULT_CONFIG = {
    "broadcast_port": 0,
    "chat_port": 0,
    "file_port": 0,
    "max_file_mb": 500,
    "history_days": 90,
    "encryption_key_path": "",
    "heartbeat_interval": HEARTBEAT_INTERVAL,
    "heartbeat_timeout": HEARTBEAT_TIMEOUT,
    "download_path": DEFAULT_DOWNLOADS_DIR,
    "shared_secret_hash": "",
    "auto_reconnect": True,
    "discovery_on": True,
    "theme": "dark",
    "font_size": "medium"
}

def load_config() -> dict:
    if os.path.exists(CONFIG_PATH):
        with open(CONFIG_PATH, 'r') as f:
            cfg = json.load(f)
            for k, v in DEFAULT_CONFIG.items():
                cfg.setdefault(k, v)
            return cfg
    else:
        save_config(DEFAULT_CONFIG)
        return DEFAULT_CONFIG.copy()

def save_config(cfg: dict) -> None:
    with open(CONFIG_PATH, 'w') as f:
        json.dump(cfg, f, indent=4)

config = load_config()
os.makedirs(config['download_path'], exist_ok=True)

logging.basicConfig(
    filename=LOG_PATH,
    level=logging.INFO,
    format='%(asctime)s [%(levelname)s] %(message)s'
)
logger = logging.getLogger('mestochat')

if not os.path.exists(MACHINE_ID_PATH):
    machine_id = str(uuid.uuid4())
    with open(MACHINE_ID_PATH, 'w') as f:
        f.write(machine_id)
else:
    with open(MACHINE_ID_PATH, 'r') as f:
        machine_id = f.read().strip()
MY_MACHINE_ID: str = machine_id

# ====================== СЕТЕВЫЕ УТИЛИТЫ ======================
def get_free_port(start: int = 50000, end: int = 50100) -> int:
    for port in range(start, end):
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            try:
                s.bind(('', port))
                return port
            except OSError:
                continue
    return random.randint(49152, 65535)

def get_all_local_ips() -> List[str]:
    ips: set = set()
    hostname = socket.gethostname()
    try:
        for info in socket.getaddrinfo(hostname, None, socket.AF_INET, socket.SOCK_DGRAM):
            ip = info[4][0]
            if not ip.startswith('127.'):
                ips.add(ip)
    except Exception:
        logger.exception("Failed to get local IPs")
    if not ips:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        try:
            s.connect(('10.254.254.254', 1))
            ips.add(s.getsockname()[0])
        except Exception:
            logger.exception("Fallback IP detection failed")
        finally:
            s.close()
    return list(ips)

def safe_close_socket(sock: Optional[socket.socket]) -> None:
    if not sock:
        return
    try:
        sock.shutdown(socket.SHUT_RDWR)
    except OSError:
        pass
    except Exception:
        logger.exception("Error shutting down socket")
    try:
        sock.close()
    except OSError:
        pass
    except Exception:
        logger.exception("Error closing socket")

# ====================== БАЗА ДАННЫХ ======================
class ChatDatabase:
    def __init__(self, db_path: str = DB_PATH) -> None:
        self._lock = threading.RLock()
        self.conn = sqlite3.connect(db_path, check_same_thread=False)
        self.conn.execute("PRAGMA journal_mode=WAL")
        self.conn.execute("PRAGMA busy_timeout=5000")
        self._create_tables()
        self._cleanup_old_messages()
        self._cleanup_temp_files()

    def _retry_execute(self, func, max_retries: int = 5) -> Optional[Any]:
        for i in range(max_retries):
            try:
                return func()
            except sqlite3.OperationalError as e:
                if "locked" in str(e) and i < max_retries - 1:
                    time.sleep(0.1)
                else:
                    logger.exception("DB operational error")
                    raise
            except Exception:
                logger.exception("Unexpected DB error")
                raise
        return None

    def _create_tables(self) -> None:
        def _do() -> None:
            with self._lock:
                cur = self.conn.cursor()
                cur.execute('''
                    CREATE TABLE IF NOT EXISTS messages (
                        id INTEGER PRIMARY KEY AUTOINCREMENT,
                        sender_id TEXT NOT NULL,
                        sender_name TEXT NOT NULL,
                        receiver_id TEXT,
                        message TEXT,
                        file_name TEXT,
                        file_path TEXT,
                        is_folder INTEGER DEFAULT 0,
                        timestamp REAL NOT NULL,
                        pending INTEGER DEFAULT 0
                    )
                ''')
                cur.execute('''
                    CREATE TABLE IF NOT EXISTS contacts (
                        machine_id TEXT PRIMARY KEY,
                        nickname TEXT NOT NULL,
                        last_seen REAL
                    )
                ''')
                cur.execute('''
                    CREATE TABLE IF NOT EXISTS settings (
                        key TEXT PRIMARY KEY,
                        value TEXT
                    )
                ''')
                cur.execute('''
                    CREATE TABLE IF NOT EXISTS unread (
                        machine_id TEXT PRIMARY KEY,
                        count INTEGER DEFAULT 0
                    )
                ''')
                self.conn.commit()
        self._retry_execute(_do)

    def _cleanup_old_messages(self) -> None:
        days = config.get('history_days', 90)
        if days > 0:
            cutoff = time.time() - days * 86400
            def _do() -> None:
                with self._lock:
                    cur = self.conn.cursor()
                    cur.execute("DELETE FROM messages WHERE timestamp < ?", (cutoff,))
                    self.conn.commit()
            self._retry_execute(_do)

        def _trim() -> None:
            with self._lock:
                cur = self.conn.cursor()
                cur.execute("SELECT COUNT(*) FROM messages")
                count = cur.fetchone()[0]
                if count > MAX_HISTORY_MESSAGES:
                    cur.execute("DELETE FROM messages WHERE id IN (SELECT id FROM messages ORDER BY timestamp ASC LIMIT ?)", (count - MAX_HISTORY_MESSAGES,))
                    self.conn.commit()
                    logger.info(f"Trimmed messages to {MAX_HISTORY_MESSAGES}")
        self._retry_execute(_trim)

    def _cleanup_temp_files(self) -> None:
        temp_dir = tempfile.gettempdir()
        try:
            for fname in os.listdir(temp_dir):
                if fname.startswith('folder_') and fname.endswith('.zip'):
                    fpath = os.path.join(temp_dir, fname)
                    try:
                        os.remove(fpath)
                        logger.info(f"Removed stale temp archive {fpath}")
                    except OSError:
                        logger.exception(f"Could not remove {fpath}")
        except Exception:
            logger.exception("Temp file cleanup error")

    def get_nickname(self) -> Optional[str]:
        return self._retry_execute(lambda: self._get_nickname_impl())

    def _get_nickname_impl(self) -> Optional[str]:
        with self._lock:
            cur = self.conn.cursor()
            cur.execute("SELECT value FROM settings WHERE key='nickname'")
            row = cur.fetchone()
            return row[0] if row else None

    def set_nickname(self, nick: str) -> None:
        self._retry_execute(lambda: self._set_nickname_impl(nick))

    def _set_nickname_impl(self, nick: str) -> None:
        with self._lock:
            cur = self.conn.cursor()
            cur.execute("INSERT OR REPLACE INTO settings (key, value) VALUES ('nickname', ?)", (nick,))
            self.conn.commit()

    def add_contact(self, machine_id: str, nickname: str) -> None:
        self._retry_execute(lambda: self._add_contact_impl(machine_id, nickname))

    def _add_contact_impl(self, machine_id: str, nickname: str) -> None:
        with self._lock:
            cur = self.conn.cursor()
            cur.execute(
                "INSERT OR REPLACE INTO contacts (machine_id, nickname, last_seen) VALUES (?, ?, ?)",
                (machine_id, nickname, time.time())
            )
            self.conn.commit()

    def get_all_contacts(self) -> List[Tuple[str, str]]:
        return self._retry_execute(lambda: self._get_all_contacts_impl()) or []

    def _get_all_contacts_impl(self) -> List[Tuple[str, str]]:
        with self._lock:
            cur = self.conn.cursor()
            cur.execute("SELECT machine_id, nickname FROM contacts ORDER BY last_seen DESC")
            return cur.fetchall()

    def save_message(self, sender_id: str, sender_name: str, receiver_id: str,
                     message: str, file_name: str = None, file_path: str = None,
                     is_folder: int = 0, pending: int = 0) -> None:
        self._retry_execute(lambda: self._save_message_impl(
            sender_id, sender_name, receiver_id, message, file_name, file_path, is_folder, pending))

    def _save_message_impl(self, sender_id: str, sender_name: str, receiver_id: str,
                           message: str, file_name: str, file_path: str,
                           is_folder: int, pending: int) -> None:
        with self._lock:
            cur = self.conn.cursor()
            cur.execute(
                "INSERT INTO messages (sender_id, sender_name, receiver_id, message, file_name, file_path, is_folder, timestamp, pending) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
                (sender_id, sender_name, receiver_id, message, file_name, file_path, is_folder, time.time(), pending)
            )
            self.conn.commit()

    def get_chat_history(self, partner_id: str, limit: int = 50, before_id: int = None) -> List[Tuple]:
        return self._retry_execute(lambda: self._get_chat_history_impl(partner_id, limit, before_id)) or []

    def _get_chat_history_impl(self, partner_id: str, limit: int, before_id: int) -> List[Tuple]:
        with self._lock:
            cur = self.conn.cursor()
            if before_id:
                cur.execute(
                    "SELECT id, sender_id, sender_name, message, file_name, file_path, is_folder, timestamp FROM messages WHERE ((sender_id=? AND receiver_id=?) OR (sender_id=? AND receiver_id=?)) AND id < ? ORDER BY timestamp DESC LIMIT ?",
                    (MY_MACHINE_ID, partner_id, partner_id, MY_MACHINE_ID, before_id, limit)
                )
            else:
                cur.execute(
                    "SELECT id, sender_id, sender_name, message, file_name, file_path, is_folder, timestamp FROM messages WHERE (sender_id=? AND receiver_id=?) OR (sender_id=? AND receiver_id=?) ORDER BY timestamp DESC LIMIT ?",
                    (MY_MACHINE_ID, partner_id, partner_id, MY_MACHINE_ID, limit)
                )
            rows = cur.fetchall()
            rows.reverse()
            return rows

    def search_messages(self, query: str) -> List[Tuple[str, str, float]]:
        return self._retry_execute(lambda: self._search_messages_impl(query)) or []

    def _search_messages_impl(self, query: str) -> List[Tuple[str, str, float]]:
        with self._lock:
            cur = self.conn.cursor()
            cur.execute(
                "SELECT sender_name, message, timestamp FROM messages WHERE message LIKE ? ORDER BY timestamp DESC LIMIT 50",
                (f"%{query}%",)
            )
            return cur.fetchall()

    def increment_unread(self, machine_id: str) -> None:
        self._retry_execute(lambda: self._increment_unread_impl(machine_id))

    def _increment_unread_impl(self, machine_id: str) -> None:
        with self._lock:
            cur = self.conn.cursor()
            cur.execute(
                "INSERT INTO unread (machine_id, count) VALUES (?, 1) ON CONFLICT(machine_id) DO UPDATE SET count = count + 1",
                (machine_id,)
            )
            self.conn.commit()

    def clear_unread(self, machine_id: str) -> None:
        self._retry_execute(lambda: self._clear_unread_impl(machine_id))

    def _clear_unread_impl(self, machine_id: str) -> None:
        with self._lock:
            cur = self.conn.cursor()
            cur.execute("DELETE FROM unread WHERE machine_id=?", (machine_id,))
            self.conn.commit()

    def get_all_unread(self) -> Dict[str, int]:
        return self._retry_execute(lambda: self._get_all_unread_impl()) or {}

    def _get_all_unread_impl(self) -> Dict[str, int]:
        with self._lock:
            cur = self.conn.cursor()
            cur.execute("SELECT machine_id, count FROM unread")
            return dict(cur.fetchall())

    def get_pending_messages(self, receiver_id: str) -> List[Tuple[int, str, str, str, int]]:
        return self._retry_execute(lambda: self._get_pending_messages_impl(receiver_id)) or []

    def _get_pending_messages_impl(self, receiver_id: str) -> List[Tuple[int, str, str, str, int]]:
        with self._lock:
            cur = self.conn.cursor()
            cur.execute(
                "SELECT id, message, file_name, file_path, is_folder FROM messages WHERE sender_id=? AND receiver_id=? AND pending=1 ORDER BY timestamp",
                (MY_MACHINE_ID, receiver_id)
            )
            return cur.fetchall()

    def mark_sent(self, msg_id: int) -> None:
        self._retry_execute(lambda: self._mark_sent_impl(msg_id))

    def _mark_sent_impl(self, msg_id: int) -> None:
        with self._lock:
            cur = self.conn.cursor()
            cur.execute("UPDATE messages SET pending=0 WHERE id=?", (msg_id,))
            self.conn.commit()

# ====================== СЕТЕВОЙ ДВИЖОК ======================
executor = ThreadPoolExecutor(max_workers=20, thread_name_prefix="Mesto")
MAX_CONNECTIONS = 20

REQUIRED_KEYS = {
    'HELLO': ['machine_id', 'nickname', 'chat_port', 'file_port', 'ips', 'room_hash'],
    'PING': ['machine_id'],
    'PONG': ['machine_id'],
    'text': ['message'],
    'file_request': ['request_id', 'file_name', 'file_size'],
    'file_accept': ['request_id'],
    'file_reject': ['request_id'],
    'nickname_change': ['new_nick'],
}

class NetworkCore(QObject):
    contact_update = pyqtSignal(dict)
    message_received = pyqtSignal(str, str, str, str, str, bool)
    file_request_received = pyqtSignal(str, str, str, int, str, bool)
    network_error = pyqtSignal(str)
    file_transfer_failed = pyqtSignal(str, str)
    file_transfer_succeeded = pyqtSignal(str, str)
    file_progress = pyqtSignal(str, int, int)
    connection_state_changed = pyqtSignal(str, bool)
    reconnect_requested = pyqtSignal(str)

    def __init__(self, db: ChatDatabase, nickname: str,
                 broadcast_port: int, chat_port: int, file_port: int,
                 room_hash: str = '', auto_reconnect: bool = True, discovery_on: bool = True) -> None:
        super().__init__()
        self.db = db
        self.nickname = nickname
        self.broadcast_port = broadcast_port
        self.chat_port = chat_port
        self.file_port = file_port
        self.running = True
        self.auto_reconnect = auto_reconnect
        self.discovery_on = discovery_on
        self.local_ips = get_all_local_ips()
        self.state_lock = threading.RLock()
        self.room_hash = room_hash
        self.peers: Dict[str, Tuple[List[str], str, float, int, int]] = {}
        self.connections: Dict[str, socket.socket] = {}
        self.offered_files: Dict[str, Tuple[str, str, bool]] = {}
        self.last_pong: Dict[str, float] = {}
        self.reconnect_attempts: Dict[str, int] = defaultdict(int)
        self.reconnecting: Dict[str, bool] = defaultdict(lambda: False)
        self.connection_states: Dict[str, str] = defaultdict(lambda: ConnectionState.NEW)
        self.threads: List[threading.Thread] = []

        try:
            self._init_sockets()
            if self.discovery_on:
                self._send_hello()
            self._start_threads()
            self._merge_contacts()
        except Exception:
            self.network_error.emit("Не удалось запустить сетевые службы")
            raise

    def _init_sockets(self) -> None:
        try:
            self.udp_sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            self.udp_sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            self.udp_sock.bind(('', self.broadcast_port))
            self.udp_sock.settimeout(1.0)

            self.chat_server_sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self.chat_server_sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            self.chat_server_sock.bind(('0.0.0.0', self.chat_port))
            self.chat_server_sock.listen(5)
            self.chat_server_sock.settimeout(1.0)

            self.file_server_sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self.file_server_sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            self.file_server_sock.bind(('0.0.0.0', self.file_port))
            self.file_server_sock.listen(5)
            self.file_server_sock.settimeout(1.0)
        except Exception:
            logger.exception("Failed to initialize sockets")
            raise

    def _start_threads(self) -> None:
        t_udp = threading.Thread(target=self._udp_listener, name="UDPListener")
        t_chat = threading.Thread(target=self._chat_server_loop, name="ChatServer")
        t_file = threading.Thread(target=self._file_server_loop, name="FileServer")
        t_heart = threading.Thread(target=self._heartbeat_loop, name="Heartbeat")
        for t in (t_udp, t_chat, t_file, t_heart):
            t.daemon = False
            t.start()
            self.threads.append(t)

    def shutdown(self) -> None:
        logger.info("Shutting down network core")
        self.running = False

        safe_close_socket(self.udp_sock)
        safe_close_socket(self.chat_server_sock)
        safe_close_socket(self.file_server_sock)

        with self.state_lock:
            conns = list(self.connections.values())
            self.connections.clear()
        for sock in conns:
            safe_close_socket(sock)

        for t in self.threads:
            if t.is_alive():
                t.join(timeout=2)
            if t.is_alive():
                logger.warning(f"Thread {t.name} did not terminate")

        self._cleanup_inactive_peers()
        logger.info("Shutdown complete")

    def _cleanup_inactive_peers(self) -> None:
        now = time.time()
        with self.state_lock:
            inactive = [pid for pid, (_, _, last, _, _) in self.peers.items()
                        if now - last > INACTIVE_PEER_CLEANUP_SECONDS]
            for pid in inactive:
                del self.peers[pid]
                self.last_pong.pop(pid, None)
                self.connection_states.pop(pid, None)

    # ----- UDP DISCOVERY -----
    def _send_hello(self) -> None:
        try:
            sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            sock.setsockopt(socket.SOL_SOCKET, socket.SO_BROADCAST, 1)
            msg = json.dumps({
                'type': 'HELLO',
                'machine_id': MY_MACHINE_ID,
                'nickname': self.nickname,
                'chat_port': self.chat_port,
                'file_port': self.file_port,
                'ips': self.local_ips,
                'room_hash': self.room_hash
            })
            sock.sendto(msg.encode(), ('255.255.255.255', self.broadcast_port))
            sock.close()
        except Exception:
            logger.exception("send_hello failed")

    def _udp_listener(self) -> None:
        while self.running:
            try:
                data, addr = self.udp_sock.recvfrom(UDP_BUFFER_SIZE)
                self._process_udp_packet(data, addr)
            except socket.timeout:
                continue
            except OSError:
                break
            except Exception:
                logger.exception("UDP listener error")
                break

    def _process_udp_packet(self, data: bytes, addr: Tuple[str, int]) -> None:
        try:
            msg = json.loads(data.decode())
        except json.JSONDecodeError:
            logger.warning("Invalid UDP JSON")
            return
        except Exception:
            logger.exception("UDP parsing error")
            return
        if not self._validate_message(msg):
            return
        msg_type = msg.get('type')
        if msg_type == 'HELLO':
            self._handle_hello_packet(msg, addr)
        elif msg_type == 'PING':
            self._handle_ping_packet(addr)
        elif msg_type == 'PONG':
            self._handle_pong_packet(msg)

    def _handle_hello_packet(self, msg: dict, addr: Tuple[str, int]) -> None:
        if not self._validate_hello(msg):
            return
        peer_id = msg['machine_id']
        if peer_id == MY_MACHINE_ID:
            return
        peer_nick = msg['nickname']
        peer_chat_port = msg.get('chat_port', self.chat_port)
        peer_file_port = msg.get('file_port', self.file_port)
        peer_ips = msg.get('ips', [addr[0]])
        with self.state_lock:
            if peer_id in self.peers:
                old_ips = set(self.peers[peer_id][0])
                new_ips = set(peer_ips)
                if old_ips and old_ips != new_ips:
                    logger.warning(f"IP change for {peer_id} ({peer_nick}): {old_ips} -> {new_ips}")
            self.peers[peer_id] = (peer_ips, peer_nick, time.time(), peer_chat_port, peer_file_port)
            self.last_pong[peer_id] = time.time()
            if self.connection_states[peer_id] == ConnectionState.DEAD:
                self.connection_states[peer_id] = ConnectionState.NEW
        self.db.add_contact(peer_id, peer_nick)
        self._merge_contacts()
        if peer_id not in self.connections and self.connection_states[peer_id] != ConnectionState.CONNECTING:
            self._try_connect_to_peer(peer_id, peer_ips, peer_chat_port)

    def _handle_ping_packet(self, addr: Tuple[str, int]) -> None:
        pong = json.dumps({'type': 'PONG', 'machine_id': MY_MACHINE_ID})
        try:
            self.udp_sock.sendto(pong.encode(), addr)
        except Exception:
            logger.exception("PONG send failed")

    def _handle_pong_packet(self, msg: dict) -> None:
        peer_id = msg['machine_id']
        if peer_id != MY_MACHINE_ID:
            with self.state_lock:
                self.last_pong[peer_id] = time.time()

    # ----- HEARTBEAT -----
    def _heartbeat_loop(self) -> None:
        while self.running:
            time.sleep(config.get('heartbeat_interval', HEARTBEAT_INTERVAL))
            now = time.time()
            sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            sock.setsockopt(socket.SOL_SOCKET, socket.SO_BROADCAST, 1)
            ping_msg = json.dumps({'type': 'PING', 'machine_id': MY_MACHINE_ID})
            try:
                sock.sendto(ping_msg.encode(), ('255.255.255.255', self.broadcast_port))
            except Exception:
                logger.exception("PING broadcast failed")
            finally:
                sock.close()
            timeout = config.get('heartbeat_timeout', HEARTBEAT_TIMEOUT)
            with self.state_lock:
                timed_out = []
                for pid, last in self.last_pong.items():
                    if pid in self.connections and now - last > timeout:
                        timed_out.append(pid)
                for pid in timed_out:
                    logger.info(f"Heartbeat timeout for {pid}, closing")
                    safe_close_socket(self.connections[pid])
                    del self.connections[pid]
                    self.connection_states[pid] = ConnectionState.DEAD
                    self.connection_state_changed.emit(pid, False)
                    self.reconnect_requested.emit(pid)
            self._merge_contacts()

    # ----- CONNECTION MANAGEMENT -----
    def _merge_contacts(self) -> None:
        db_contacts = {mid: nick for mid, nick in self.db.get_all_contacts() if mid != MY_MACHINE_ID}
        combined = {}
        with self.state_lock:
            peers_snapshot = dict(self.peers)
        for mid, nick in db_contacts.items():
            if mid in peers_snapshot:
                combined[mid] = peers_snapshot[mid]
            else:
                combined[mid] = ([], nick, 0, 0, 0)
        for mid, data in peers_snapshot.items():
            if mid not in combined:
                combined[mid] = data
        self.contact_update.emit(combined)

    def _try_connect_to_peer(self, peer_id: str, ips: List[str], chat_port: int) -> None:
        with self.state_lock:
            if self.connection_states[peer_id] in (ConnectionState.CONNECTING, ConnectionState.ACTIVE):
                return
            self.connection_states[peer_id] = ConnectionState.CONNECTING
        for ip in ips:
            sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            sock.settimeout(2.0)
            try:
                sock.connect((ip, chat_port))
            except Exception:
                logger.warning(f"Connect to {ip}:{chat_port} failed")
                safe_close_socket(sock)
                continue
            with self.state_lock:
                if peer_id in self.connections:
                    safe_close_socket(sock)
                    self.connection_states[peer_id] = ConnectionState.CONNECTED
                    return
                self.connections[peer_id] = sock
                self.last_pong[peer_id] = time.time()
                self.connection_states[peer_id] = ConnectionState.CONNECTED
            sock.settimeout(30)
            executor.submit(self._chat_receiver, sock, peer_id)
            self._send_identity(sock)
            self._send_pending_messages(peer_id)
            return
        with self.state_lock:
            self.connection_states[peer_id] = ConnectionState.NEW

    def _send_identity(self, sock: socket.socket) -> None:
        identity = json.dumps({
            'type': 'identity',
            'machine_id': MY_MACHINE_ID,
            'nickname': self.nickname,
            'room_hash': self.room_hash
        })
        self._send_frame(sock, identity)

    def _try_reconnect(self, peer_id: str) -> None:
        if not self.auto_reconnect:
            return
        with self.state_lock:
            if self.reconnecting.get(peer_id, False):
                return
            if peer_id in self.connections or not self.running:
                return
            if self.connection_states[peer_id] == ConnectionState.DEAD:
                return
            self.reconnecting[peer_id] = True
            if peer_id not in self.peers:
                return
            ips, _, _, chat_port, _ = self.peers[peer_id]
        logger.info(f"Reconnecting to {peer_id}")
        self._try_connect_to_peer(peer_id, ips, chat_port)
        with self.state_lock:
            if peer_id in self.connections:
                self.reconnect_attempts[peer_id] = 0
                self.connection_states[peer_id] = ConnectionState.CONNECTED
            else:
                self.reconnect_attempts[peer_id] += 1
                if self.reconnect_attempts[peer_id] < MAX_RECONNECT_ATTEMPTS:
                    self.reconnect_requested.emit(peer_id)
                else:
                    self.connection_states[peer_id] = ConnectionState.DEAD
            self.reconnecting[peer_id] = False

    # ----- CHAT SERVER -----
    def _chat_server_loop(self) -> None:
        while self.running:
            try:
                client_sock, addr = self.chat_server_sock.accept()
                with self.state_lock:
                    if len(self.connections) >= MAX_CONNECTIONS:
                        safe_close_socket(client_sock)
                        continue
                client_sock.settimeout(30)
                self._handle_incoming_connection(client_sock, addr)
            except socket.timeout:
                continue
            except OSError:
                break
            except Exception:
                logger.exception("Chat server error")
                break

    def _handle_incoming_connection(self, client_sock: socket.socket, addr: Tuple[str, int]) -> None:
        identity = self._recv_frame(client_sock)
        if not identity:
            safe_close_socket(client_sock)
            return
        try:
            data = json.loads(identity)
        except json.JSONDecodeError:
            logger.warning("Invalid identity JSON")
            safe_close_socket(client_sock)
            return
        except Exception:
            logger.exception("Identity parsing error")
            safe_close_socket(client_sock)
            return
        if data.get('type') == 'identity':
            if self.room_hash and data.get('room_hash') != self.room_hash:
                logger.warning("Room hash mismatch")
                safe_close_socket(client_sock)
                return
            peer_id = data['machine_id']
            peer_nick = data['nickname']
        else:
            if not self._validate_message(data):
                safe_close_socket(client_sock)
                return
            peer_id = data['machine_id']
            peer_nick = data.get('nickname', 'Unknown')
        with self.state_lock:
            if peer_id in self.connections:
                safe_close_socket(client_sock)
                return
            self.connections[peer_id] = client_sock
            if peer_id not in self.peers:
                self.peers[peer_id] = ([addr[0]], peer_nick, time.time(), self.chat_port, self.file_port)
            else:
                ips, _, _, _, _ = self.peers[peer_id]
                self.peers[peer_id] = (ips, peer_nick, time.time(), self.chat_port, self.file_port)
            self.last_pong[peer_id] = time.time()
            self.connection_states[peer_id] = ConnectionState.ACTIVE
        self._merge_contacts()
        executor.submit(self._chat_receiver, client_sock, peer_id)
        self._send_pending_messages(peer_id)

    def _chat_receiver(self, sock: socket.socket, peer_id: str) -> None:
        while self.running:
            try:
                data_str = self._recv_frame(sock)
                if not data_str:
                    break
                try:
                    data = json.loads(data_str)
                except json.JSONDecodeError:
                    logger.warning("Invalid chat JSON")
                    continue
                except Exception:
                    logger.exception("Chat receiver parsing error")
                    continue
                if not self._validate_message(data):
                    continue
                self._process_message(peer_id, data)
            except socket.timeout:
                continue
            except OSError:
                break
            except Exception:
                logger.exception(f"Chat receiver error for {peer_id}")
                break
        with self.state_lock:
            if peer_id in self.connections and self.connections[peer_id] == sock:
                del self.connections[peer_id]
                self.connection_states[peer_id] = ConnectionState.DEAD
        safe_close_socket(sock)
        self._merge_contacts()
        if self.running:
            self.reconnect_requested.emit(peer_id)

    def _process_message(self, peer_id: str, data: dict) -> None:
        msg_type = data.get('type')
        if msg_type == 'text':
            self._handle_text_message(peer_id, data)
        elif msg_type == 'file_request':
            self._handle_file_request_message(peer_id, data)
        elif msg_type == 'file_accept':
            self._send_file_to(peer_id, data['request_id'])
        elif msg_type == 'file_reject':
            with self.state_lock:
                self.offered_files.pop(data['request_id'], None)
        elif msg_type == 'nickname_change':
            self._handle_nickname_change(peer_id, data)

    def _handle_text_message(self, peer_id: str, data: dict) -> None:
        sender_nick = self.peers.get(peer_id, ('', 'Unknown'))[1]
        message = data['message']
        self.db.save_message(peer_id, sender_nick, MY_MACHINE_ID, message)
        self.db.increment_unread(peer_id)
        self.message_received.emit(peer_id, sender_nick, message, '', '', False)

    def _handle_file_request_message(self, peer_id: str, data: dict) -> None:
        sender_nick = self.peers.get(peer_id, ('', 'Unknown'))[1]
        self.file_request_received.emit(peer_id, sender_nick, data['file_name'], data['file_size'], data['request_id'], data.get('is_folder', False))

    def _handle_nickname_change(self, peer_id: str, data: dict) -> None:
        new_nick = data['new_nick']
        with self.state_lock:
            if peer_id in self.peers:
                ips, _, last, cp, fp = self.peers[peer_id]
                self.peers[peer_id] = (ips, new_nick, last, cp, fp)
        self.db.add_contact(peer_id, new_nick)
        self._merge_contacts()

    # ----- MESSAGING -----
    def send_message(self, peer_id: str, text: str) -> bool:
        with self.state_lock:
            sock = self.connections.get(peer_id)
        if not sock:
            self.db.save_message(MY_MACHINE_ID, self.nickname, peer_id, text, pending=1)
            return True
        try:
            self._send_frame(sock, json.dumps({'type': 'text', 'message': text}))
            self.db.save_message(MY_MACHINE_ID, self.nickname, peer_id, text)
            return True
        except Exception:
            logger.exception(f"Send message to {peer_id} failed")
            with self.state_lock:
                self.connections.pop(peer_id, None)
            self.db.save_message(MY_MACHINE_ID, self.nickname, peer_id, text, pending=1)
            return True

    def _send_message_raw(self, peer_id: str, text: str) -> bool:
        with self.state_lock:
            sock = self.connections.get(peer_id)
        if not sock:
            return False
        try:
            self._send_frame(sock, json.dumps({'type': 'text', 'message': text}))
            return True
        except Exception:
            logger.exception(f"Raw send to {peer_id} failed")
            with self.state_lock:
                self.connections.pop(peer_id, None)
            return False

    def send_file_request(self, peer_id: str, file_path: str, is_folder: bool = False) -> bool:
        with self.state_lock:
            sock = self.connections.get(peer_id)
        if not sock:
            return False
        request_id = str(uuid.uuid4())
        file_name = os.path.basename(file_path)
        file_size = os.path.getsize(file_path)
        with self.state_lock:
            self.offered_files[request_id] = (file_path, MY_MACHINE_ID, is_folder)
        msg = json.dumps({
            'type': 'file_request',
            'request_id': request_id,
            'file_name': file_name,
            'file_size': file_size,
            'is_folder': is_folder
        })
        try:
            self._send_frame(sock, msg)
            threading.Timer(60.0, lambda rid=request_id: self._cleanup_offer(rid)).start()
            return True
        except Exception:
            logger.exception(f"Send file request to {peer_id} failed")
            with self.state_lock:
                self.offered_files.pop(request_id, None)
            return False

    def _cleanup_offer(self, request_id: str) -> None:
        with self.state_lock:
            self.offered_files.pop(request_id, None)

    # ----- FILE TRANSFER -----
    def _send_file_to(self, receiver_id: str, request_id: str) -> None:
        with self.state_lock:
            info = self.offered_files.pop(request_id, None)
        if not info:
            return
        file_path, sender_id, is_folder = info
        with self.state_lock:
            if receiver_id not in self.peers:
                return
            peer_ips, _, _, _, file_port = self.peers[receiver_id]
        if not peer_ips or file_port == 0:
            self.file_transfer_failed.emit(receiver_id, "Неизвестный IP или порт получателя")
            return

        file_sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        file_sock.settimeout(TRANSFER_TIMEOUT)
        connected = False
        for ip in peer_ips:
            try:
                file_sock.connect((ip, file_port))
                connected = True
                break
            except Exception:
                continue
        if not connected:
            self.file_transfer_failed.emit(receiver_id, "Не удалось подключиться для передачи файла")
            safe_close_socket(file_sock)
            return

        try:
            preamble = json.dumps({'request_id': request_id, 'sender_id': sender_id, 'is_folder': is_folder})
            self._send_exact(file_sock, preamble.encode().ljust(MAX_PREAMBLE_SIZE))
            header = json.dumps({'file_name': os.path.basename(file_path), 'file_size': os.path.getsize(file_path)})
            self._send_exact(file_sock, header.encode().ljust(MAX_HEADER_SIZE))
            with open(file_path, 'rb') as f:
                while chunk := f.read(BUFFER_SIZE):
                    file_sock.sendall(chunk)
            self.file_transfer_succeeded.emit(receiver_id, os.path.basename(file_path))
        except Exception:
            logger.exception(f"File send error to {receiver_id}")
            self.file_transfer_failed.emit(receiver_id, "Ошибка при отправке файла")
        finally:
            safe_close_socket(file_sock)
            if is_folder and file_path.startswith(tempfile.gettempdir()):
                try:
                    os.remove(file_path)
                except Exception:
                    logger.exception("Failed to remove temp archive")

    def _file_server_loop(self) -> None:
        while self.running:
            try:
                client_sock, addr = self.file_server_sock.accept()
                executor.submit(self._handle_incoming_file, client_sock)
            except socket.timeout:
                continue
            except OSError:
                break
            except Exception:
                logger.exception("File server error")
                break

    def _safe_extract_zip(self, zip_path: str, extract_dir: str) -> None:
        with zipfile.ZipFile(zip_path, 'r') as zf:
            for member in zf.infolist():
                member_path = os.path.abspath(os.path.join(extract_dir, member.filename))
                if not member_path.startswith(os.path.abspath(extract_dir)):
                    raise Exception(f"Zip traversal attempt: {member.filename}")
            zf.extractall(extract_dir)

    def _handle_incoming_file(self, sock: socket.socket) -> None:
        sock.settimeout(TRANSFER_TIMEOUT)
        temp_path = None
        final_path = None
        try:
            preamble_data = self._recv_exact(sock, MAX_PREAMBLE_SIZE)
            try:
                preamble = json.loads(preamble_data.decode().strip())
            except json.JSONDecodeError:
                logger.warning("Invalid file preamble JSON")
                return
            except Exception:
                logger.exception("Error parsing file preamble")
                return
            if not all(k in preamble for k in ('request_id', 'sender_id')):
                logger.warning("Missing fields in preamble")
                return
            request_id = preamble['request_id']
            sender_id = preamble['sender_id']
            is_folder = preamble.get('is_folder', False)

            header_data = self._recv_exact(sock, MAX_HEADER_SIZE)
            try:
                header = json.loads(header_data.decode().strip())
            except json.JSONDecodeError:
                logger.warning("Invalid file header JSON")
                return
            except Exception:
                logger.exception("Error parsing file header")
                return
            if not all(k in header for k in ('file_name', 'file_size')):
                return
            file_name = header['file_name']
            file_size = header['file_size']

            file_name = os.path.basename(file_name)
            safe_name = "".join(c for c in file_name if c.isalnum() or c in "._- ")
            if not safe_name:
                safe_name = "unnamed"
            if file_size > config['max_file_mb'] * 1024 * 1024:
                return

            download_dir = config['download_path']
            os.makedirs(download_dir, exist_ok=True)
            temp_path = os.path.join(download_dir, f"{safe_name}.tmp")
            final_path = os.path.join(download_dir, safe_name)
            received = 0
            last_progress = time.time()
            with open(temp_path, 'wb') as f:
                while received < file_size:
                    chunk = sock.recv(min(BUFFER_SIZE, file_size - received))
                    if not chunk:
                        break
                    f.write(chunk)
                    received += len(chunk)
                    self.file_progress.emit(file_name, received, file_size)
                    if time.time() - last_progress > TRANSFER_PROGRESS_TIMEOUT:
                        raise socket.timeout("Transfer stalled")
                    last_progress = time.time()

            if is_folder and safe_name.lower().endswith('.zip'):
                folder_name = safe_name[:-4]
                extract_dir = os.path.join(download_dir, folder_name)
                os.makedirs(extract_dir, exist_ok=True)
                try:
                    self._safe_extract_zip(temp_path, extract_dir)
                    os.remove(temp_path)
                    final_path = extract_dir
                    final_name = folder_name
                    is_folder_flag = True
                except Exception:
                    logger.exception(f"Zip extract error for {temp_path}")
                    os.rename(temp_path, final_path)
                    final_name = safe_name
                    is_folder_flag = False
            else:
                os.rename(temp_path, final_path)
                final_name = safe_name
                is_folder_flag = False

            with self.state_lock:
                nick = self.peers.get(sender_id, ('', 'Unknown'))[1]
            self.db.save_message(sender_id, nick, MY_MACHINE_ID,
                                 f"Получен файл: {final_name}", final_name, final_path,
                                 is_folder=1 if is_folder_flag else 0)
            self.db.increment_unread(sender_id)
            self.message_received.emit(sender_id, nick, '', final_name, final_path, is_folder_flag)
        except socket.timeout:
            logger.warning("File transfer timed out")
        except Exception:
            logger.exception("File receive error")
        finally:
            safe_close_socket(sock)
            if temp_path and os.path.exists(temp_path):
                try:
                    os.remove(temp_path)
                except Exception:
                    logger.exception("Failed to remove temp file")

    # ----- PROTOCOL HELPERS -----
    def _send_frame(self, sock: socket.socket, plain: str) -> None:
        data = plain.encode()
        length = len(data)
        sock.sendall(struct.pack('!I', length))
        sock.sendall(data)

    def _recv_frame(self, sock: socket.socket) -> Optional[str]:
        raw = sock.recv(4)
        if len(raw) < 4:
            return None
        length = struct.unpack('!I', raw)[0]
        if length > MAX_MESSAGE_SIZE:
            raise ValueError("Сообщение слишком большое")
        data = bytearray()
        while len(data) < length:
            packet = sock.recv(length - len(data))
            if not packet:
                raise ConnectionError("Соединение разорвано")
            data.extend(packet)
        return data.decode()

    def _send_exact(self, sock: socket.socket, data: bytes) -> None:
        sock.sendall(data)

    def _recv_exact(self, sock: socket.socket, n: int) -> bytes:
        data = bytearray()
        while len(data) < n:
            packet = sock.recv(n - len(data))
            if not packet:
                raise ConnectionError("Соединение закрыто при чтении точного количества байт")
            data.extend(packet)
        return bytes(data)

    def _validate_message(self, data: dict, required_type: str = None) -> bool:
        if 'type' not in data:
            return False
        msg_type = data['type']
        if required_type and msg_type != required_type:
            return False
        needed = REQUIRED_KEYS.get(msg_type, [])
        for key in needed:
            if key not in data:
                logger.warning(f"Missing key '{key}' in message type {msg_type}")
                return False
        return True

    def _validate_hello(self, msg: dict) -> bool:
        if not self.room_hash:
            return True
        return msg.get('room_hash') == self.room_hash

    def update_nickname(self, new_nick: str) -> None:
        self.nickname = new_nick
        self.db.set_nickname(new_nick)
        msg = json.dumps({'type': 'nickname_change', 'new_nick': new_nick})
        with self.state_lock:
            conns = list(self.connections.items())
        for pid, sock in conns:
            try:
                self._send_frame(sock, msg)
            except Exception:
                logger.exception(f"Nickname update failed for {pid}")
                with self.state_lock:
                    self.connections.pop(pid, None)
        with self.state_lock:
            if MY_MACHINE_ID in self.peers:
                ips, _, last, cp, fp = self.peers[MY_MACHINE_ID]
                self.peers[MY_MACHINE_ID] = (ips, new_nick, last, cp, fp)
        self._merge_contacts()

    def _send_pending_messages(self, peer_id: str) -> None:
        pending = self.db.get_pending_messages(peer_id)
        for msg_id, text, file_name, file_path, is_folder in pending:
            if file_name:
                self.db.mark_sent(msg_id)
            else:
                if self._send_message_raw(peer_id, text):
                    self.db.mark_sent(msg_id)

# ====================== GUI ======================
class ChatDisplay(QTextEdit):
    file_dropped = pyqtSignal(str, bool)
    history_scroll = pyqtSignal()

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setAcceptDrops(True)
        self.setReadOnly(True)
        self.setFont(QFont("Segoe UI", 10))
        self.verticalScrollBar().valueChanged.connect(self._on_scroll)

    def _on_scroll(self, value: int) -> None:
        if value <= self.verticalScrollBar().minimum() + 10:
            self.history_scroll.emit()

    def dragEnterEvent(self, event: QDragEnterEvent) -> None:
        if event.mimeData().hasUrls():
            event.acceptProposedAction()

    def dragMoveEvent(self, event: QDragMoveEvent) -> None:
        if event.mimeData().hasUrls():
            event.acceptProposedAction()

    def dropEvent(self, event: QDropEvent) -> None:
        if event.mimeData().hasUrls():
            for url in event.mimeData().urls():
                path = url.toLocalFile()
                if os.path.isdir(path):
                    base = os.path.join(tempfile.gettempdir(), f"folder_{uuid.uuid4()}")
                    archive_path = shutil.make_archive(base, 'zip', path)
                    self.file_dropped.emit(archive_path, True)
                    event.acceptProposedAction()
                    return
                elif os.path.isfile(path):
                    self.file_dropped.emit(path, False)
                    event.acceptProposedAction()
                    return
        event.ignore()

class NicknameDialog(QDialog):
    def __init__(self, current_nick=''):
        super().__init__()
        self.setWindowTitle("Вход в MestoChat")
        self.setMinimumWidth(300)
        layout = QFormLayout()
        self.nick_edit = QLineEdit(current_nick)
        self.nick_edit.setPlaceholderText("Введите ваш ник...")
        layout.addRow("Никнейм:", self.nick_edit)
        buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)
        layout.addRow(buttons)
        self.setLayout(layout)

    def get_nickname(self) -> str:
        return self.nick_edit.text().strip()

class SettingsDialog(QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Настройки MestoChat")
        self.setMinimumWidth(350)
        layout = QFormLayout()

        self.nickname_edit = QLineEdit()
        layout.addRow("Имя:", self.nickname_edit)

        self.auto_reconnect_check = QCheckBox("Автоматическое переподключение")
        self.auto_reconnect_check.setChecked(config.get('auto_reconnect', True))
        layout.addRow(self.auto_reconnect_check)

        self.theme_combo = QComboBox()
        self.theme_combo.addItems(["Тёмная", "Светлая"])
        current_theme = config.get('theme', 'dark')
        self.theme_combo.setCurrentIndex(0 if current_theme == 'dark' else 1)
        layout.addRow("Тема:", self.theme_combo)

        self.font_size_combo = QComboBox()
        self.font_size_combo.addItems(["Маленький", "Средний", "Большой"])
        current_font = config.get('font_size', 'medium')
        idx = 1 if current_font == 'medium' else (2 if current_font == 'large' else 0)
        self.font_size_combo.setCurrentIndex(idx)
        layout.addRow("Размер шрифта:", self.font_size_combo)

        buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        buttons.accepted.connect(self.save_and_accept)
        buttons.rejected.connect(self.reject)
        layout.addRow(buttons)
        self.setLayout(layout)

    def save_and_accept(self) -> None:
        config['auto_reconnect'] = self.auto_reconnect_check.isChecked()
        config['theme'] = 'dark' if self.theme_combo.currentIndex() == 0 else 'light'
        idx = self.font_size_combo.currentIndex()
        config['font_size'] = 'small' if idx == 0 else ('large' if idx == 2 else 'medium')
        save_config(config)
        self.accept()

class MainWindow(QMainWindow):
    def __init__(self, db: ChatDatabase, nickname: str, broad_port: int, chat_port: int, file_port: int):
        super().__init__()
        self.db = db
        self.nickname = nickname
        self.setWindowTitle(f"MestoChat — {html.escape(nickname)}")
        self.setMinimumSize(800, 500)
        self.current_peer: Optional[str] = None
        self.unread_counts: Dict[str, int] = defaultdict(int)
        self.history_offset: Dict[str, Optional[int]] = {}

        auto_reconnect = config.get('auto_reconnect', True)
        discovery_on = config.get('discovery_on', True)

        stored_hash = config.get('shared_secret_hash', '')
        room_hash = ''
        if stored_hash:
            password, ok = QInputDialog.getText(self, "Пароль комнаты", "Введите секретный ключ:", QLineEdit.Password)
            if not ok or not password:
                QMessageBox.critical(self, "Ошибка", "Для входа в комнату требуется пароль.")
                sys.exit(1)
            if hashlib.sha256(password.encode()).hexdigest() != stored_hash:
                QMessageBox.critical(self, "Ошибка", "Неверный пароль комнаты.")
                sys.exit(1)
            room_hash = stored_hash

        try:
            self.net = NetworkCore(db, nickname, broad_port, chat_port, file_port, room_hash,
                                   auto_reconnect, discovery_on)
        except Exception as e:
            QMessageBox.critical(self, "Критическая ошибка", f"Не удалось запустить сеть:\n{e}")
            sys.exit(1)

        self.net.contact_update.connect(self.update_contacts)
        self.net.message_received.connect(self.display_message)
        self.net.file_request_received.connect(self.handle_incoming_file)
        self.net.network_error.connect(self.show_error)
        self.net.file_transfer_failed.connect(self.on_file_transfer_failed)
        self.net.file_transfer_succeeded.connect(self.on_file_transfer_succeeded)
        self.net.file_progress.connect(self.on_file_progress)
        self.net.reconnect_requested.connect(self.schedule_reconnect)

        self._apply_theme()
        self._setup_ui()
        self._load_contacts()

        self.hello_timer = QTimer()
        self.hello_timer.timeout.connect(self.net._send_hello)
        self.hello_timer.start(5000)

        self.tray_icon = QSystemTrayIcon(self)
        self.tray_icon.setIcon(self.style().standardIcon(QStyle.SP_ComputerIcon))
        self.tray_icon.setToolTip("MestoChat")
        tray_menu = QMenu()
        show_action = QAction("Открыть", self)
        show_action.triggered.connect(self.show)
        tray_menu.addAction(show_action)
        settings_action = QAction("Настройки", self)
        settings_action.triggered.connect(self.open_settings)
        tray_menu.addAction(settings_action)
        tray_menu.addSeparator()
        quit_action = QAction("Выйти", self)
        quit_action.triggered.connect(self.full_quit)
        tray_menu.addAction(quit_action)
        self.tray_icon.setContextMenu(tray_menu)
        self.tray_icon.activated.connect(self.on_tray_activated)
        self.tray_icon.show()

    def _apply_theme(self) -> None:
        theme = config.get('theme', 'dark')
        if theme == 'dark':
            style = """
                QMainWindow { background-color: #1e1e1e; color: #d4d4d4; }
                QWidget { background-color: #1e1e1e; color: #d4d4d4; }
                QListWidget { background-color: #252526; color: #cccccc; }
                QTextEdit { background-color: #1e1e1e; color: #d4d4d4; }
                QLineEdit { background-color: #3c3c3c; color: white; }
            """
        else:
            style = """
                QMainWindow { background-color: #ffffff; color: #000000; }
                QWidget { background-color: #f0f0f0; color: #000000; }
                QListWidget { background-color: #ffffff; color: #000000; }
                QTextEdit { background-color: #ffffff; color: #000000; }
                QLineEdit { background-color: #ffffff; color: #000000; }
            """
        self.setStyleSheet(style)

    def schedule_reconnect(self, peer_id: str) -> None:
        if not config.get('auto_reconnect', True):
            return
        attempts = self.net.reconnect_attempts.get(peer_id, 0)
        if attempts >= MAX_RECONNECT_ATTEMPTS:
            return
        delay = min(2 ** attempts + random.uniform(0, 1), RECONNECT_BACKOFF_MAX)
        QTimer.singleShot(int(delay * 1000), lambda pid=peer_id: self.net._try_reconnect(pid))

    def _setup_ui(self) -> None:
        central = QWidget()
        self.setCentralWidget(central)
        main_layout = QVBoxLayout(central)
        main_layout.setContentsMargins(0, 0, 0, 0)

        self.net_status_label = QLabel("LAN Chat — 0 online 🟢 stable")
        self.net_status_label.setAlignment(Qt.AlignCenter)
        self.net_status_label.setStyleSheet("background-color: #1e1e1e; color: #aaa; padding: 2px; font-size: 9pt;")
        main_layout.addWidget(self.net_status_label)

        splitter = QSplitter(Qt.Horizontal)
        main_layout.addWidget(splitter)

        left_panel = QWidget()
        left_layout = QVBoxLayout(left_panel)
        left_layout.setContentsMargins(0, 0, 0, 0)
        self.contact_list = QListWidget()
        self.contact_list.setFont(QFont("Segoe UI", 10))
        self.contact_list.itemClicked.connect(self.on_contact_clicked)
        left_layout.addWidget(self.contact_list)
        splitter.addWidget(left_panel)

        right_panel = QWidget()
        right_layout = QVBoxLayout(right_panel)
        right_layout.setContentsMargins(0, 0, 0, 0)

        self.chat_display = ChatDisplay()
        self.chat_display.file_dropped.connect(self.on_file_dropped)
        self.chat_display.history_scroll.connect(self.load_more_history)
        self.chat_display.anchorClicked.connect(self._on_anchor_clicked)
        right_layout.addWidget(self.chat_display)

        input_layout = QHBoxLayout()
        self.message_input = QLineEdit()
        self.message_input.setPlaceholderText("Введите сообщение...")
        self.message_input.returnPressed.connect(self.send_message)
        input_layout.addWidget(self.message_input)

        send_btn = QPushButton("⬆")
        send_btn.setFixedWidth(40)
        send_btn.clicked.connect(self.send_message)
        input_layout.addWidget(send_btn)

        right_layout.addLayout(input_layout)
        splitter.addWidget(right_panel)
        splitter.setSizes([200, 600])

        font_size = config.get('font_size', 'medium')
        sizes = {'small': 8, 'medium': 10, 'large': 12}
        size = sizes.get(font_size, 10)
        font = QFont("Segoe UI", size)
        self.contact_list.setFont(font)
        self.chat_display.setFont(font)
        self.message_input.setFont(font)

    def _load_contacts(self) -> None:
        contacts = self.db.get_all_contacts()
        for machine_id, nickname in contacts:
            if machine_id != MY_MACHINE_ID:
                self._add_contact_entry(machine_id, nickname)
        unread = self.db.get_all_unread()
        for mid, count in unread.items():
            self.unread_counts[mid] = count

    def _add_contact_entry(self, machine_id: str, nickname: str) -> None:
        item = QListWidgetItem()
        item.setData(Qt.UserRole, machine_id)
        self.contact_list.addItem(item)

    def update_contacts(self, peers: dict) -> None:
        current = self.contact_list.currentItem()
        current_id = current.data(Qt.UserRole) if current else None
        self.contact_list.clear()
        online = []
        reconnecting = []
        offline = []
        now = time.time()
        for mid, (ips, nick, last_hello, _, _) in peers.items():
            status = 'online' if (now - last_hello < PEER_TIMEOUT) else 'offline'
            if self.net.reconnect_attempts.get(mid, 0) > 0:
                status = 'reconnecting'
            entry = (mid, nick, status)
            if status == 'online':
                online.append(entry)
            elif status == 'reconnecting':
                reconnecting.append(entry)
            else:
                offline.append(entry)

        online.sort(key=lambda x: x[1].lower())
        reconnecting.sort(key=lambda x: x[1].lower())
        offline.sort(key=lambda x: x[1].lower())

        for mid, nick, status in online + reconnecting + offline:
            icon = '🟢' if status == 'online' else ('🟡' if status == 'reconnecting' else '⚫')
            text = f"{icon} {html.escape(nick)}"
            unread = self.unread_counts.get(mid, 0)
            if unread > 0:
                text += f"  ({unread})"
            item = QListWidgetItem(text)
            item.setData(Qt.UserRole, mid)
            self.contact_list.addItem(item)

        if current_id:
            for i in range(self.contact_list.count()):
                if self.contact_list.item(i).data(Qt.UserRole) == current_id:
                    self.contact_list.setCurrentRow(i)
                    break

        online_count = len(online)
        total = len(peers)
        if total == 0:
            status_text = "LAN Chat — waiting for peers..."
            status_color = "#aaa"
        elif online_count == total:
            status_text = f"LAN Chat — {online_count} online 🟢 stable"
            status_color = "#4caf50"
        elif reconnecting:
            status_text = f"LAN Chat — {online_count}/{total} online 🟡 unstable"
            status_color = "#ff9800"
        else:
            status_text = f"LAN Chat — {online_count}/{total} online 🔴 degraded"
            status_color = "#f44336"
        self.net_status_label.setText(status_text)
        self.net_status_label.setStyleSheet(f"background-color: #1e1e1e; color: {status_color}; padding: 2px; font-size: 9pt;")

    def on_contact_clicked(self, item: QListWidgetItem) -> None:
        self.current_peer = item.data(Qt.UserRole)
        self.history_offset[self.current_peer] = None
        self.load_chat_history(self.current_peer)
        self.db.clear_unread(self.current_peer)
        self.unread_counts[self.current_peer] = 0
        self.message_input.setFocus()

    def load_chat_history(self, peer_id: str) -> None:
        self.chat_display.clear()
        messages = self.db.get_chat_history(peer_id, limit=50)
        for row in messages:
            self._append_message(row)
        if messages:
            self.history_offset[peer_id] = messages[0][0]
        self.chat_display.moveCursor(QTextCursor.End)

    def _append_message(self, row: tuple) -> None:
        msg_id, sender_id, sender_name, message, file_name, file_path, is_folder, timestamp = row
        time_str = datetime.fromtimestamp(timestamp).strftime("%H:%M")
        safe_sender = html.escape(sender_name)
        if file_name:
            safe_file = html.escape(file_name)
            link = f"mestochat://open_file?path={quote(file_path)}"
            icon = "📁" if is_folder else "📄"
            self.chat_display.append(
                f"<b>[{time_str}] {safe_sender}:</b> "
                f"<a href='{html.escape(link)}'>{icon} {safe_file}</a>"
            )
        else:
            safe_msg = html.escape(message)
            self.chat_display.append(f"<b>[{time_str}] {safe_sender}:</b> {safe_msg}")

    def load_more_history(self) -> None:
        if not self.current_peer:
            return
        oldest = self.history_offset.get(self.current_peer)
        if oldest is None:
            return
        older = self.db.get_chat_history(self.current_peer, limit=50, before_id=oldest)
        if not older:
            return
        scrollbar = self.chat_display.verticalScrollBar()
        old_value = scrollbar.value()
        old_max = scrollbar.maximum()
        cursor = self.chat_display.textCursor()
        cursor.movePosition(QTextCursor.Start)
        self.chat_display.setTextCursor(cursor)
        for row in older:
            self._append_message(row)
            cursor.movePosition(QTextCursor.Start)
            self.chat_display.setTextCursor(cursor)
        new_max = scrollbar.maximum()
        delta = new_max - old_max
        scrollbar.setValue(old_value + delta)
        self.history_offset[self.current_peer] = older[0][0]

    def display_message(self, sender_id: str, nick: str, text: str, file_name: str, local_path: str, is_folder: bool) -> None:
        safe_nick = html.escape(nick)
        if self.current_peer != sender_id or not self.isActiveWindow():
            self.unread_counts[sender_id] = self.unread_counts.get(sender_id, 0) + 1
            self._update_contact_display()
            if not self.isActiveWindow():
                self.tray_icon.showMessage(
                    f"Новое сообщение от {safe_nick}",
                    html.escape(text) if text else f"Файл: {html.escape(file_name)}",
                    QSystemTrayIcon.Information,
                    3000
                )
        if self.current_peer == sender_id:
            time_str = datetime.now().strftime("%H:%M")
            if file_name:
                link = f"mestochat://open_file?path={quote(local_path)}"
                icon = "📁" if is_folder else "📄"
                self.chat_display.append(
                    f"<b>[{time_str}] {safe_nick}:</b> "
                    f"<a href='{html.escape(link)}'>{icon} {html.escape(file_name)}</a>"
                )
            else:
                self.chat_display.append(f"<b>[{time_str}] {safe_nick}:</b> {html.escape(text)}")
            self.chat_display.moveCursor(QTextCursor.End)

    def _on_anchor_clicked(self, url: QUrl) -> None:
        if url.scheme() == "mestochat" and url.host() == "open_file":
            from PyQt5.QtCore import QUrlQuery
            query = QUrlQuery(url)
            path = query.queryItemValue("path")
            if path and os.path.exists(path):
                ext = os.path.splitext(path)[1].lower()
                if ext in ('.png', '.jpg', '.jpeg', '.gif', '.bmp'):
                    pix = QPixmap(path)
                    if not pix.isNull():
                        dlg = QDialog(self)
                        dlg.setWindowTitle("Просмотр изображения")
                        layout = QVBoxLayout()
                        label = QLabel()
                        label.setPixmap(pix.scaled(800, 600, Qt.KeepAspectRatio, Qt.SmoothTransformation))
                        layout.addWidget(label)
                        dlg.setLayout(layout)
                        dlg.exec_()
                        return
                QDesktopServices.openUrl(QUrl.fromLocalFile(path))

    def send_message(self) -> None:
        if not self.current_peer:
            return
        text = self.message_input.text().strip()
        if not text:
            return
        if self.net.send_message(self.current_peer, text):
            time_str = datetime.now().strftime("%H:%M")
            self.chat_display.append(f"<b>[{time_str}] Вы:</b> {html.escape(text)}")
            self.message_input.clear()
        else:
            self.chat_display.append("<i style='color:red'>⚠ Не доставлено (сохранено для отправки)</i>")

    def on_file_dropped(self, file_path: str, is_folder: bool) -> None:
        if not self.current_peer:
            QMessageBox.warning(self, "Ошибка", "Сначала выберите контакт в списке.")
            return
        if self.net.send_file_request(self.current_peer, file_path, is_folder=is_folder):
            file_name = os.path.basename(file_path)
            self.chat_display.append(f"<b>Вы:</b> <i>{html.escape(file_name)} → отправка 0%</i>")
        else:
            self.chat_display.append("<i style='color:red'>⚠ Не удалось отправить файл</i>")

    def handle_incoming_file(self, sender_id: str, nick: str, file_name: str, file_size: int, request_id: str, is_folder: bool) -> None:
        accept_msg = json.dumps({'type': 'file_accept', 'request_id': request_id})
        with self.net.state_lock:
            sock = self.net.connections.get(sender_id)
        if sock:
            try:
                self.net._send_frame(sock, accept_msg)
            except Exception:
                logger.exception("Error sending file accept")
        if self.current_peer == sender_id:
            self.chat_display.append(f"<i style='color:gray'>{html.escape(nick)}: получение {html.escape(file_name)} 0%</i>")

    def on_file_progress(self, file_name: str, received: int, total: int) -> None:
        percent = int(received / total * 100) if total else 0
        cursor = self.chat_display.textCursor()
        cursor.movePosition(QTextCursor.End)
        cursor.movePosition(QTextCursor.StartOfLine, QTextCursor.KeepAnchor)
        last_line = cursor.selectedText()
        if 'отправка' in last_line or 'получение' in last_line:
            cursor.removeSelectedText()
            new_text = last_line.split('%')[0].rsplit(' ', 1)[0] + f" {percent}%</i>"
            self.chat_display.append(new_text)
        else:
            self.chat_display.append(f"<i style='color:gray'>Прогресс: {html.escape(file_name)} {percent}%</i>")

    def on_file_transfer_failed(self, peer_id: str, error_msg: str) -> None:
        if self.current_peer == peer_id:
            self.chat_display.append(f"<i style='color:red'>❌ Передача не удалась: {html.escape(error_msg)}</i>")
        else:
            QMessageBox.warning(self, "Ошибка передачи файла", html.escape(error_msg))

    def on_file_transfer_succeeded(self, peer_id: str, file_name: str) -> None:
        if self.current_peer == peer_id:
            self.chat_display.append(f"<i style='color:green'>✔ {html.escape(file_name)} отправлен</i>")

    def open_settings(self) -> None:
        dlg = SettingsDialog(self)
        if dlg.exec_() == QDialog.Accepted:
            self._apply_theme()
            font_size = config.get('font_size', 'medium')
            sizes = {'small': 8, 'medium': 10, 'large': 12}
            size = sizes.get(font_size, 10)
            font = QFont("Segoe UI", size)
            self.contact_list.setFont(font)
            self.chat_display.setFont(font)
            self.message_input.setFont(font)

    def show_error(self, msg: str) -> None:
        QMessageBox.critical(self, "Ошибка", msg)

    def on_tray_activated(self, reason: int) -> None:
        if reason == QSystemTrayIcon.Trigger:
            self.show()

    def closeEvent(self, event) -> None:
        if self.tray_icon.isVisible():
            self.hide()
            self.tray_icon.showMessage("MestoChat", "Программа свернута в трей.", QSystemTrayIcon.Information, 2000)
            event.ignore()
        else:
            self.full_quit()

    def full_quit(self) -> None:
        self.net.shutdown()
        self.tray_icon.hide()
        QApplication.quit()

    def _update_contact_display(self) -> None:
        for i in range(self.contact_list.count()):
            item = self.contact_list.item(i)
            mid = item.data(Qt.UserRole)
            if mid in self.unread_counts and self.unread_counts[mid] > 0:
                base = item.text().split("  (")[0] if "  (" in item.text() else item.text()
                if "🟢" in base or "🟡" in base or "⚫" in base:
                    item.setText(f"{base}  ({self.unread_counts[mid]})")

if __name__ == "__main__":
    app = QApplication(sys.argv)
    app.setQuitOnLastWindowClosed(False)

    db = ChatDatabase()
    nickname = db.get_nickname()
    if not nickname:
        dialog = NicknameDialog()
        if dialog.exec_() == QDialog.Accepted:
            nickname = dialog.get_nickname()
            if nickname:
                db.set_nickname(nickname)
            else:
                sys.exit(0)
        else:
            sys.exit(0)

    used_ports = set()
    def get_unique_port():
        while True:
            port = get_free_port()
            if port not in used_ports:
                used_ports.add(port)
                return port

    broad = config['broadcast_port'] or get_unique_port()
    chat = config['chat_port'] or get_unique_port()
    file = config['file_port'] or get_unique_port()

    try:
        window = MainWindow(db, nickname, broad, chat, file)
        window.show()
        sys.exit(app.exec_())
    except Exception as e:
        QMessageBox.critical(None, "Ошибка запуска", str(e))
