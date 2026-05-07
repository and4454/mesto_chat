import sys, os, socket, threading, json, time, struct, uuid, random, logging, zipfile, tempfile, shutil, sqlite3, hashlib, html
from datetime import datetime
from collections import defaultdict
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
from urllib.parse import quote

from PyQt5.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
    QListWidget, QListWidgetItem, QTextEdit, QLineEdit, QPushButton,
    QLabel, QMessageBox, QFileDialog, QSplitter, QSystemTrayIcon, QMenu, QAction,
    QDialog, QFormLayout, QDialogButtonBox, QStyle, QStackedWidget, QInputDialog,
    QTabWidget, QSpinBox
)
from PyQt5.QtCore import Qt, pyqtSignal, QObject, QTimer, QUrl
from PyQt5.QtGui import QDragEnterEvent, QDropEvent, QTextCursor, QDesktopServices, QPixmap, QDragMoveEvent

# ----------------------------------------------------------------------
# Конфигурация
# ----------------------------------------------------------------------
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
    "heartbeat_interval": 3,
    "heartbeat_timeout": 9,
    "download_path": DEFAULT_DOWNLOADS_DIR,
    "shared_secret_hash": ""
}

def load_config():
    if os.path.exists(CONFIG_PATH):
        with open(CONFIG_PATH, 'r') as f:
            cfg = json.load(f)
            for k, v in DEFAULT_CONFIG.items():
                cfg.setdefault(k, v)
            return cfg
    else:
        save_config(DEFAULT_CONFIG)
        return DEFAULT_CONFIG.copy()

def save_config(cfg):
    with open(CONFIG_PATH, 'w') as f:
        json.dump(cfg, f, indent=4)

config = load_config()
os.makedirs(config['download_path'], exist_ok=True)

logging.basicConfig(
    filename=LOG_PATH,
    level=logging.INFO,
    format='%(asctime)s [%(levelname)s] %(message)s'
)
logger = logging.getLogger('MestoChat')

if not os.path.exists(MACHINE_ID_PATH):
    machine_id = str(uuid.uuid4())
    with open(MACHINE_ID_PATH, 'w') as f:
        f.write(machine_id)
else:
    with open(MACHINE_ID_PATH, 'r') as f:
        machine_id = f.read().strip()
MY_MACHINE_ID = machine_id

# ----------------------------------------------------------------------
# Сетевые утилиты
# ----------------------------------------------------------------------
def get_free_port(start=50000, end=50100):
    for port in range(start, end):
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
            try:
                s.bind(('', port))
                return port
            except:
                continue
    return random.randint(49152, 65535)

def get_all_local_ips():
    ips = set()
    hostname = socket.gethostname()
    try:
        for info in socket.getaddrinfo(hostname, None, socket.AF_INET, socket.SOCK_DGRAM):
            ip = info[4][0]
            if not ip.startswith('127.'):
                ips.add(ip)
    except:
        pass
    if not ips:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        try:
            s.connect(('10.254.254.254', 1))
            ips.add(s.getsockname()[0])
        except:
            pass
        finally:
            s.close()
    return list(ips)

def safe_close(sock):
    if sock:
        try:
            sock.shutdown(socket.SHUT_RDWR)
        except:
            pass
        try:
            sock.close()
        except:
            pass

# ----------------------------------------------------------------------
# База данных
# ----------------------------------------------------------------------
class ChatDatabase:
    def __init__(self, db_path=DB_PATH):
        self.lock = threading.RLock()
        self.conn = sqlite3.connect(db_path, check_same_thread=False)
        self.conn.execute("PRAGMA journal_mode=WAL")
        self.conn.execute("PRAGMA busy_timeout=5000")
        self._create_tables()
        self._cleanup_old_messages()

    def _retry_execute(self, func, max_retries=5):
        for i in range(max_retries):
            try:
                return func()
            except sqlite3.OperationalError as e:
                if "locked" in str(e) and i < max_retries - 1:
                    time.sleep(0.1)
                else:
                    raise
            except Exception as e:
                logger.error(f"DB error: {e}")
                raise
        return None

    def _create_tables(self):
        def _do():
            with self.lock:
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

    def _cleanup_old_messages(self):
        days = config.get('history_days', 90)
        if days <= 0:
            return
        cutoff = time.time() - days * 86400
        def _do():
            with self.lock:
                cur = self.conn.cursor()
                cur.execute("DELETE FROM messages WHERE timestamp < ?", (cutoff,))
                self.conn.commit()
        self._retry_execute(_do)

    def get_nickname(self):
        return self._retry_execute(lambda: self._get_nickname_impl())

    def _get_nickname_impl(self):
        with self.lock:
            cur = self.conn.cursor()
            cur.execute("SELECT value FROM settings WHERE key='nickname'")
            row = cur.fetchone()
            return row[0] if row else None

    def set_nickname(self, nick):
        self._retry_execute(lambda: self._set_nickname_impl(nick))

    def _set_nickname_impl(self, nick):
        with self.lock:
            cur = self.conn.cursor()
            cur.execute("INSERT OR REPLACE INTO settings (key, value) VALUES ('nickname', ?)", (nick,))
            self.conn.commit()

    def add_contact(self, machine_id, nickname):
        self._retry_execute(lambda: self._add_contact_impl(machine_id, nickname))

    def _add_contact_impl(self, machine_id, nickname):
        with self.lock:
            cur = self.conn.cursor()
            cur.execute(
                "INSERT OR REPLACE INTO contacts (machine_id, nickname, last_seen) VALUES (?, ?, ?)",
                (machine_id, nickname, time.time())
            )
            self.conn.commit()

    def get_all_contacts(self):
        return self._retry_execute(lambda: self._get_all_contacts_impl()) or []

    def _get_all_contacts_impl(self):
        with self.lock:
            cur = self.conn.cursor()
            cur.execute("SELECT machine_id, nickname FROM contacts ORDER BY last_seen DESC")
            return cur.fetchall()

    def save_message(self, sender_id, sender_name, receiver_id, message, file_name=None, file_path=None, is_folder=0, pending=0):
        self._retry_execute(lambda: self._save_message_impl(sender_id, sender_name, receiver_id, message, file_name, file_path, is_folder, pending))

    def _save_message_impl(self, sender_id, sender_name, receiver_id, message, file_name, file_path, is_folder, pending):
        with self.lock:
            cur = self.conn.cursor()
            cur.execute(
                "INSERT INTO messages (sender_id, sender_name, receiver_id, message, file_name, file_path, is_folder, timestamp, pending) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
                (sender_id, sender_name, receiver_id, message, file_name, file_path, is_folder, time.time(), pending)
            )
            self.conn.commit()

    def get_chat_history(self, partner_id, limit=50, before_id=None):
        return self._retry_execute(lambda: self._get_chat_history_impl(partner_id, limit, before_id)) or []

    def _get_chat_history_impl(self, partner_id, limit, before_id):
        with self.lock:
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

    def search_messages(self, query):
        return self._retry_execute(lambda: self._search_messages_impl(query)) or []

    def _search_messages_impl(self, query):
        with self.lock:
            cur = self.conn.cursor()
            cur.execute(
                "SELECT sender_name, message, timestamp FROM messages WHERE message LIKE ? ORDER BY timestamp DESC LIMIT 50",
                (f"%{query}%",)
            )
            return cur.fetchall()

    def increment_unread(self, machine_id):
        self._retry_execute(lambda: self._increment_unread_impl(machine_id))

    def _increment_unread_impl(self, machine_id):
        with self.lock:
            cur = self.conn.cursor()
            cur.execute(
                "INSERT INTO unread (machine_id, count) VALUES (?, 1) ON CONFLICT(machine_id) DO UPDATE SET count = count + 1",
                (machine_id,)
            )
            self.conn.commit()

    def clear_unread(self, machine_id):
        self._retry_execute(lambda: self._clear_unread_impl(machine_id))

    def _clear_unread_impl(self, machine_id):
        with self.lock:
            cur = self.conn.cursor()
            cur.execute("DELETE FROM unread WHERE machine_id=?", (machine_id,))
            self.conn.commit()

    def get_all_unread(self):
        return self._retry_execute(lambda: self._get_all_unread_impl()) or {}

    def _get_all_unread_impl(self):
        with self.lock:
            cur = self.conn.cursor()
            cur.execute("SELECT machine_id, count FROM unread")
            return dict(cur.fetchall())

    def get_pending_messages(self, receiver_id):
        return self._retry_execute(lambda: self._get_pending_messages_impl(receiver_id)) or []

    def _get_pending_messages_impl(self, receiver_id):
        with self.lock:
            cur = self.conn.cursor()
            cur.execute(
                "SELECT id, message, file_name, file_path, is_folder FROM messages WHERE sender_id=? AND receiver_id=? AND pending=1 ORDER BY timestamp",
                (MY_MACHINE_ID, receiver_id)
            )
            return cur.fetchall()

    def mark_sent(self, msg_id):
        self._retry_execute(lambda: self._mark_sent_impl(msg_id))

    def _mark_sent_impl(self, msg_id):
        with self.lock:
            cur = self.conn.cursor()
            cur.execute("UPDATE messages SET pending=0 WHERE id=?", (msg_id,))
            self.conn.commit()

# ----------------------------------------------------------------------
# Сетевой движок
# ----------------------------------------------------------------------
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
    file_progress = pyqtSignal(str, int, int)
    connection_state_changed = pyqtSignal(str, bool)
    reconnect_requested = pyqtSignal(str)

    def __init__(self, db, nickname, broadcast_port, chat_port, file_port, room_hash=''):
        super().__init__()
        self.db = db
        self.nickname = nickname
        self.broadcast_port = broadcast_port
        self.chat_port = chat_port
        self.file_port = file_port
        self.running = True
        self.local_ips = get_all_local_ips()
        self.lock = threading.RLock()
        self.room_hash = room_hash
        self.peer_ips_history = defaultdict(set)
        self.peers = {}            # machine_id: (ips, nickname, last_hello, chat_port, file_port)
        self.connections = {}
        self.offered_files = {}    # request_id: (file_path, sender_id, is_folder)
        self.last_pong = {}
        self.reconnect_attempts = defaultdict(int)

        self.udp_sock = None
        self.chat_server_sock = None
        self.file_server_sock = None

        try:
            self._start_udp_listener()
            self._start_chat_server()
            self._start_file_server()
        except Exception as e:
            logger.error(f"Failed to start network services: {e}")
            self.network_error.emit(f"Не удалось запустить сетевые службы: {e}")

        self._send_hello()
        executor.submit(self._heartbeat_loop)
        self._merge_contacts()

    def _merge_contacts(self):
        db_contacts = {mid: nick for mid, nick in self.db.get_all_contacts() if mid != MY_MACHINE_ID}
        combined = {}
        now = time.time()
        for mid, nick in db_contacts.items():
            if mid in self.peers:
                ips, nick_net, last_hello, cp, fp = self.peers[mid]
                combined[mid] = (ips, nick_net, last_hello, cp, fp)
            else:
                combined[mid] = ([], nick, 0, 0, 0)
        for mid, (ips, nick_net, last_hello, cp, fp) in self.peers.items():
            if mid not in combined:
                combined[mid] = (ips, nick_net, last_hello, cp, fp)
        self.contact_update.emit(combined)

    def _start_udp_listener(self):
        self.udp_sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.udp_sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.udp_sock.bind(('', self.broadcast_port))
        self.udp_sock.settimeout(1.0)
        executor.submit(self._udp_listener)

    def _start_chat_server(self):
        self.chat_server_sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.chat_server_sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.chat_server_sock.bind(('0.0.0.0', self.chat_port))
        self.chat_server_sock.listen(5)
        self.chat_server_sock.settimeout(1.0)
        executor.submit(self._chat_server_loop)

    def _start_file_server(self):
        self.file_server_sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.file_server_sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.file_server_sock.bind(('0.0.0.0', self.file_port))
        self.file_server_sock.listen(5)
        self.file_server_sock.settimeout(1.0)
        executor.submit(self._file_server_loop)

    def stop(self):
        self.running = False
        safe_close(self.udp_sock)
        safe_close(self.chat_server_sock)
        safe_close(self.file_server_sock)
        with self.lock:
            for sock in self.connections.values():
                safe_close(sock)
            self.connections.clear()

    def _send_hello(self):
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
        except Exception as e:
            logger.error(f"send_hello error: {e}")

    def _validate_message(self, data, required_type=None):
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

    def _validate_hello(self, msg):
        if not self.room_hash:
            return True
        return msg.get('room_hash') == self.room_hash

    def _udp_listener(self):
        while self.running:
            try:
                data, addr = self.udp_sock.recvfrom(4096)
                try:
                    msg = json.loads(data.decode())
                except:
                    continue
                if not self._validate_message(msg):
                    continue
                msg_type = msg.get('type')
                if msg_type == 'HELLO':
                    if not self._validate_hello(msg):
                        continue
                    peer_id = msg['machine_id']
                    if peer_id == MY_MACHINE_ID:
                        continue
                    peer_nick = msg['nickname']
                    peer_chat_port = msg.get('chat_port', self.chat_port)
                    peer_file_port = msg.get('file_port', self.file_port)
                    peer_ips = msg.get('ips', [addr[0]])
                    with self.lock:
                        if peer_id in self.peers:
                            old_ips = set(self.peers[peer_id][0])
                            new_ips = set(peer_ips)
                            if old_ips and old_ips != new_ips:
                                logger.warning(f"Machine {peer_id} ({peer_nick}) changed IP from {old_ips} to {new_ips}")
                        self.peers[peer_id] = (peer_ips, peer_nick, time.time(), peer_chat_port, peer_file_port)
                        self.last_pong[peer_id] = time.time()
                    self.db.add_contact(peer_id, peer_nick)
                    self._merge_contacts()
                    if peer_id not in self.connections:
                        self._try_connect_to_peer(peer_id, peer_ips, peer_chat_port)
                elif msg_type == 'PING':
                    pong = json.dumps({'type': 'PONG', 'machine_id': MY_MACHINE_ID})
                    self.udp_sock.sendto(pong.encode(), addr)
                elif msg_type == 'PONG':
                    peer_id = msg['machine_id']
                    if peer_id != MY_MACHINE_ID:
                        self.last_pong[peer_id] = time.time()
            except socket.timeout:
                continue
            except Exception as e:
                if self.running:
                    logger.error(f"UDP error: {e}")

    def _heartbeat_loop(self):
        while self.running:
            time.sleep(config.get('heartbeat_interval', 3))
            now = time.time()
            sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            sock.setsockopt(socket.SOL_SOCKET, socket.SO_BROADCAST, 1)
            ping_msg = json.dumps({'type': 'PING', 'machine_id': MY_MACHINE_ID})
            sock.sendto(ping_msg.encode(), ('255.255.255.255', self.broadcast_port))
            sock.close()
            timeout = config.get('heartbeat_timeout', 9)
            with self.lock:
                for peer_id in list(self.connections.keys()):
                    last = self.last_pong.get(peer_id, 0)
                    if now - last > timeout:
                        logger.info(f"Heartbeat timeout for {peer_id}, closing")
                        safe_close(self.connections[peer_id])
                        del self.connections[peer_id]
                        self.connection_state_changed.emit(peer_id, False)
                        self.reconnect_requested.emit(peer_id)
            self._merge_contacts()

    def _try_reconnect(self, peer_id):
        if peer_id in self.connections or not self.running:
            return
        with self.lock:
            if peer_id not in self.peers:
                return
            ips, _, _, chat_port, _ = self.peers[peer_id]
        logger.info(f"Reconnecting to {peer_id} ({ips}:{chat_port})")
        self._try_connect_to_peer(peer_id, ips, chat_port)
        if peer_id in self.connections:
            self.reconnect_attempts[peer_id] = 0
        else:
            self.reconnect_attempts[peer_id] += 1
            if self.reconnect_attempts[peer_id] < 5:
                self.reconnect_requested.emit(peer_id)

    def _try_connect_to_peer(self, peer_id, ips, chat_port):
        for ip in ips:
            sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            sock.settimeout(2.0)
            try:
                sock.connect((ip, chat_port))
            except Exception as e:
                logger.warning(f"Connect to {ip}:{chat_port} failed: {e}")
                safe_close(sock)
                continue
            with self.lock:
                if peer_id in self.connections:
                    safe_close(sock)
                    return
                self.connections[peer_id] = sock
            sock.settimeout(30)
            executor.submit(self._chat_receiver, sock, peer_id)
            self._send_identity(sock)
            self._send_pending_messages(peer_id)
            return

    def _send_identity(self, sock):
        identity = json.dumps({
            'type': 'identity',
            'machine_id': MY_MACHINE_ID,
            'nickname': self.nickname,
            'room_hash': self.room_hash
        })
        self._send_frame(sock, identity)

    def _chat_server_loop(self):
        while self.running:
            try:
                client_sock, addr = self.chat_server_sock.accept()
                with self.lock:
                    if len(self.connections) >= MAX_CONNECTIONS:
                        safe_close(client_sock)
                        continue
                client_sock.settimeout(30)
                identity = self._recv_frame(client_sock)
                if not identity:
                    safe_close(client_sock)
                    continue
                try:
                    data = json.loads(identity)
                except:
                    safe_close(client_sock)
                    continue
                if data.get('type') == 'identity':
                    if self.room_hash and data.get('room_hash') != self.room_hash:
                        logger.warning("Connection rejected: room_hash mismatch")
                        safe_close(client_sock)
                        continue
                    peer_id = data['machine_id']
                    peer_nick = data['nickname']
                else:
                    if not self._validate_message(data):
                        safe_close(client_sock)
                        continue
                    peer_id = data['machine_id']
                    peer_nick = data.get('nickname', 'Unknown')
                with self.lock:
                    if peer_id in self.connections:
                        safe_close(client_sock)
                        continue
                    self.connections[peer_id] = client_sock
                    if peer_id not in self.peers:
                        self.peers[peer_id] = ([addr[0]], peer_nick, time.time(), self.chat_port, self.file_port)
                    else:
                        ips, _, _, _, _ = self.peers[peer_id]
                        self.peers[peer_id] = (ips, peer_nick, time.time(), self.chat_port, self.file_port)
                    self.last_pong[peer_id] = time.time()
                self._merge_contacts()
                executor.submit(self._chat_receiver, client_sock, peer_id)
                self._send_pending_messages(peer_id)
            except socket.timeout:
                continue
            except Exception as e:
                if self.running:
                    logger.error(f"Chat server error: {e}")

    def _chat_receiver(self, sock, peer_id):
        while self.running:
            try:
                data_str = self._recv_frame(sock)
                if not data_str:
                    break
                try:
                    data = json.loads(data_str)
                except:
                    continue
                if not self._validate_message(data):
                    continue
                self._process_message(peer_id, data)
            except socket.timeout:
                continue
            except Exception as e:
                logger.warning(f"Chat receiver error for {peer_id}: {e}")
                break
        with self.lock:
            if peer_id in self.connections and self.connections[peer_id] == sock:
                del self.connections[peer_id]
        safe_close(sock)
        self._merge_contacts()
        if self.running:
            self.reconnect_requested.emit(peer_id)

    def _process_message(self, peer_id, data):
        msg_type = data.get('type')
        if msg_type == 'text':
            sender_nick = self.peers.get(peer_id, ('', 'Unknown'))[1]
            message = data['message']
            self.db.save_message(peer_id, sender_nick, MY_MACHINE_ID, message)
            self.db.increment_unread(peer_id)
            self.message_received.emit(peer_id, sender_nick, message, '', '', False)
        elif msg_type == 'file_request':
            file_name = data['file_name']
            file_size = data['file_size']
            request_id = data['request_id']
            is_folder = data.get('is_folder', False)
            sender_nick = self.peers.get(peer_id, ('', 'Unknown'))[1]
            self.file_request_received.emit(peer_id, sender_nick, file_name, file_size, request_id, is_folder)
        elif msg_type == 'file_accept':
            request_id = data['request_id']
            self._send_file_to(peer_id, request_id)
        elif msg_type == 'file_reject':
            request_id = data['request_id']
            with self.lock:
                self.offered_files.pop(request_id, None)
        elif msg_type == 'nickname_change':
            new_nick = data['new_nick']
            with self.lock:
                if peer_id in self.peers:
                    ips, _, last, cp, fp = self.peers[peer_id]
                    self.peers[peer_id] = (ips, new_nick, last, cp, fp)
            self.db.add_contact(peer_id, new_nick)
            self._merge_contacts()

    def send_message(self, peer_id, text):
        with self.lock:
            sock = self.connections.get(peer_id)
            if not sock:
                self.db.save_message(MY_MACHINE_ID, self.nickname, peer_id, text, pending=1)
                return True
            try:
                self._send_frame(sock, json.dumps({'type': 'text', 'message': text}))
                self.db.save_message(MY_MACHINE_ID, self.nickname, peer_id, text)
                return True
            except:
                self.connections.pop(peer_id, None)
                self.db.save_message(MY_MACHINE_ID, self.nickname, peer_id, text, pending=1)
                return True

    def _send_message_raw(self, peer_id, text):
        with self.lock:
            sock = self.connections.get(peer_id)
            if not sock:
                return False
            try:
                self._send_frame(sock, json.dumps({'type': 'text', 'message': text}))
                return True
            except:
                self.connections.pop(peer_id, None)
                return False

    def send_file_request(self, peer_id, file_path, is_folder=False):
        with self.lock:
            sock = self.connections.get(peer_id)
        if not sock:
            return False
        request_id = str(uuid.uuid4())
        file_name = os.path.basename(file_path)
        file_size = os.path.getsize(file_path)
        with self.lock:
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
        except:
            with self.lock:
                self.offered_files.pop(request_id, None)
            return False

    def _cleanup_offer(self, request_id):
        with self.lock:
            self.offered_files.pop(request_id, None)

    def _send_file_to(self, receiver_id, request_id):
        with self.lock:
            info = self.offered_files.pop(request_id, None)
        if not info:
            return
        file_path, sender_id, is_folder = info
        with self.lock:
            if receiver_id not in self.peers:
                return
            peer_ips, _, _, _, file_port = self.peers[receiver_id]
        if not peer_ips or file_port == 0:
            self.file_transfer_failed.emit(receiver_id, "Неизвестный IP или порт получателя")
            return
        file_sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        file_sock.settimeout(10)
        connected = False
        for ip in peer_ips:
            try:
                file_sock.connect((ip, file_port))
                connected = True
                break
            except:
                continue
        if not connected:
            self.file_transfer_failed.emit(receiver_id, "Не удалось подключиться для передачи файла")
            return
        try:
            preamble = json.dumps({'request_id': request_id, 'sender_id': sender_id, 'is_folder': is_folder})
            self._send_exact(file_sock, preamble.encode().ljust(128))
            header = json.dumps({'file_name': os.path.basename(file_path), 'file_size': os.path.getsize(file_path)})
            self._send_exact(file_sock, header.encode().ljust(512))
            with open(file_path, 'rb') as f:
                while chunk := f.read(8192):
                    file_sock.sendall(chunk)
        except Exception as e:
            logger.error(f"File send error: {e}")
            self.file_transfer_failed.emit(receiver_id, f"Ошибка при отправке файла: {e}")
        finally:
            safe_close(file_sock)
            if is_folder and file_path.startswith(tempfile.gettempdir()):
                try:
                    os.remove(file_path)
                except:
                    pass

    def _file_server_loop(self):
        while self.running:
            try:
                client_sock, addr = self.file_server_sock.accept()
                executor.submit(self._handle_incoming_file, client_sock)
            except socket.timeout:
                continue
            except Exception as e:
                if self.running:
                    logger.error(f"File server error: {e}")

    def _safe_extract_zip(self, zip_path, extract_dir):
        with zipfile.ZipFile(zip_path, 'r') as zf:
            for member in zf.infolist():
                member_path = os.path.abspath(os.path.join(extract_dir, member.filename))
                if not member_path.startswith(os.path.abspath(extract_dir)):
                    raise Exception(f"Zip traversal attempt: {member.filename}")
            zf.extractall(extract_dir)

    def _handle_incoming_file(self, sock):
        sock.settimeout(30)
        try:
            preamble_data = self._recv_exact(sock, 128)
            try:
                preamble = json.loads(preamble_data.decode().strip())
            except:
                return
            if not all(k in preamble for k in ('request_id', 'sender_id')):
                logger.warning("Invalid preamble")
                return
            request_id = preamble['request_id']
            sender_id = preamble['sender_id']
            is_folder = preamble.get('is_folder', False)

            header_data = self._recv_exact(sock, 512)
            try:
                header = json.loads(header_data.decode().strip())
            except:
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
            save_path = os.path.join(download_dir, safe_name)
            received = 0
            with open(save_path, 'wb') as f:
                while received < file_size:
                    chunk = sock.recv(min(8192, file_size - received))
                    if not chunk:
                        break
                    f.write(chunk)
                    received += len(chunk)
                    self.file_progress.emit(file_name, received, file_size)

            if is_folder and safe_name.lower().endswith('.zip'):
                folder_name = safe_name[:-4]
                extract_dir = os.path.join(download_dir, folder_name)
                os.makedirs(extract_dir, exist_ok=True)
                try:
                    self._safe_extract_zip(save_path, extract_dir)
                    os.remove(save_path)
                    final_path = extract_dir
                    final_name = folder_name
                    is_folder_flag = True
                except Exception as e:
                    logger.error(f"Zip extract error: {e}")
                    final_path = save_path
                    final_name = safe_name
                    is_folder_flag = False
            else:
                final_path = save_path
                final_name = safe_name
                is_folder_flag = False

            with self.lock:
                nick = self.peers.get(sender_id, ('', 'Unknown'))[1]
            self.db.save_message(sender_id, nick, MY_MACHINE_ID,
                                 f"Получен файл: {final_name}", final_name, final_path,
                                 is_folder=1 if is_folder_flag else 0)
            self.db.increment_unread(sender_id)
            self.message_received.emit(sender_id, nick, '', final_name, final_path, is_folder_flag)
        except Exception as e:
            logger.error(f"File receive error: {e}")
        finally:
            safe_close(sock)

    def _send_frame(self, sock, plain: str):
        data = plain.encode()
        length = len(data)
        sock.sendall(struct.pack('!I', length))
        sock.sendall(data)

    def _recv_frame(self, sock):
        raw = sock.recv(4)
        if len(raw) < 4:
            return None
        length = struct.unpack('!I', raw)[0]
        if length > 10 * 1024 * 1024:
            raise ValueError("Сообщение слишком большое")
        data = bytearray()
        while len(data) < length:
            packet = sock.recv(length - len(data))
            if not packet:
                raise ConnectionError("Соединение разорвано")
            data.extend(packet)
        return data.decode()

    def _send_exact(self, sock, data: bytes):
        sock.sendall(data)

    def _recv_exact(self, sock, n: int) -> bytes:
        data = bytearray()
        while len(data) < n:
            packet = sock.recv(n - len(data))
            if not packet:
                raise ConnectionError("Соединение закрыто при чтении точного количества байт")
            data.extend(packet)
        return bytes(data)

    def update_nickname(self, new_nick):
        self.nickname = new_nick
        self.db.set_nickname(new_nick)
        msg = json.dumps({'type': 'nickname_change', 'new_nick': new_nick})
        with self.lock:
            for pid, sock in list(self.connections.items()):
                try:
                    self._send_frame(sock, msg)
                except:
                    self.connections.pop(pid, None)
        if MY_MACHINE_ID in self.peers:
            ips, _, last, cp, fp = self.peers[MY_MACHINE_ID]
            self.peers[MY_MACHINE_ID] = (ips, new_nick, last, cp, fp)
        self._merge_contacts()

    def _send_pending_messages(self, peer_id):
        pending = self.db.get_pending_messages(peer_id)
        for msg_id, text, file_name, file_path, is_folder in pending:
            if file_name:
                self.db.mark_sent(msg_id)
            else:
                if self._send_message_raw(peer_id, text):
                    self.db.mark_sent(msg_id)

# ----------------------------------------------------------------------
# GUI
# ----------------------------------------------------------------------
class ChatDisplay(QTextEdit):
    file_dropped = pyqtSignal(str, bool)  # file_path, is_folder
    history_scroll = pyqtSignal()

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setAcceptDrops(True)
        self.setReadOnly(True)
        self.verticalScrollBar().valueChanged.connect(self._on_scroll)

    def _on_scroll(self, value):
        if value <= self.verticalScrollBar().minimum() + 10:
            self.history_scroll.emit()

    def dragEnterEvent(self, event: QDragEnterEvent):
        if event.mimeData().hasUrls():
            event.acceptProposedAction()

    def dragMoveEvent(self, event: QDragMoveEvent):
        if event.mimeData().hasUrls():
            event.acceptProposedAction()

    def dropEvent(self, event: QDropEvent):
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

    def get_nickname(self):
        return self.nick_edit.text().strip()

class SettingsDialog(QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Настройки MestoChat")
        self.setMinimumWidth(400)
        layout = QFormLayout()
        self.bport = QSpinBox(); self.bport.setRange(0,65535)
        self.cport = QSpinBox(); self.cport.setRange(0,65535)
        self.fport = QSpinBox(); self.fport.setRange(0,65535)
        self.max_mb = QSpinBox(); self.max_mb.setRange(10,2000)
        self.history_days = QSpinBox(); self.history_days.setRange(0,3650)
        self.key_path = QLineEdit()
        self.heartbeat_int = QSpinBox(); self.heartbeat_int.setRange(1,30)
        self.heartbeat_timeout = QSpinBox(); self.heartbeat_timeout.setRange(3,60)
        self.download_path = QLineEdit()
        self.download_path.setReadOnly(True)
        browse_btn = QPushButton("Обзор...")
        browse_btn.clicked.connect(self.browse_download_path)
        self.shared_secret = QLineEdit()
        self.shared_secret.setEchoMode(QLineEdit.Password)

        self.load_config()
        layout.addRow("Broadcast порт (0-авто):", self.bport)
        layout.addRow("Чат порт (0-авто):", self.cport)
        layout.addRow("Файловый порт (0-авто):", self.fport)
        layout.addRow("Макс. размер файла (МБ):", self.max_mb)
        layout.addRow("Хранить историю (дней):", self.history_days)
        layout.addRow("Путь к ключу шифрования:", self.key_path)
        layout.addRow("Heartbeat интервал (сек):", self.heartbeat_int)
        layout.addRow("Heartbeat таймаут (сек):", self.heartbeat_timeout)
        layout.addRow("Папка загрузок:", self.download_path)
        layout.addRow("", browse_btn)
        layout.addRow("Секретный ключ (общий):", self.shared_secret)
        buttons = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        buttons.accepted.connect(self.save_and_accept)
        buttons.rejected.connect(self.reject)
        layout.addRow(buttons)
        self.setLayout(layout)

    def load_config(self):
        self.bport.setValue(config.get('broadcast_port',0))
        self.cport.setValue(config.get('chat_port',0))
        self.fport.setValue(config.get('file_port',0))
        self.max_mb.setValue(config.get('max_file_mb',500))
        self.history_days.setValue(config.get('history_days',90))
        self.key_path.setText(config.get('encryption_key_path',''))
        self.heartbeat_int.setValue(config.get('heartbeat_interval',3))
        self.heartbeat_timeout.setValue(config.get('heartbeat_timeout',9))
        self.download_path.setText(config.get('download_path', DEFAULT_DOWNLOADS_DIR))
        self.shared_secret.setText('')

    def browse_download_path(self):
        folder = QFileDialog.getExistingDirectory(self, "Выберите папку для загрузок", self.download_path.text())
        if folder:
            self.download_path.setText(folder)

    def save_and_accept(self):
        config['broadcast_port'] = self.bport.value()
        config['chat_port'] = self.cport.value()
        config['file_port'] = self.fport.value()
        config['max_file_mb'] = self.max_mb.value()
        config['history_days'] = self.history_days.value()
        config['encryption_key_path'] = self.key_path.text()
        config['heartbeat_interval'] = self.heartbeat_int.value()
        config['heartbeat_timeout'] = self.heartbeat_timeout.value()
        config['download_path'] = self.download_path.text()
        pwd = self.shared_secret.text()
        if pwd:
            config['shared_secret_hash'] = hashlib.sha256(pwd.encode()).hexdigest()
        else:
            config['shared_secret_hash'] = ''
        save_config(config)
        if not os.path.exists(config['download_path']):
            os.makedirs(config['download_path'], exist_ok=True)
        self.accept()

class DiagnosticsWidget(QWidget):
    def __init__(self, net, parent=None):
        super().__init__(parent)
        self.net = net
        layout = QVBoxLayout()
        self.info_label = QLabel()
        layout.addWidget(self.info_label)
        layout.addWidget(QLabel("Последние записи лога:"))
        self.log_text = QTextEdit()
        self.log_text.setReadOnly(True)
        layout.addWidget(self.log_text)
        self.refresh_btn = QPushButton("Обновить")
        self.refresh_btn.clicked.connect(self.refresh)
        layout.addWidget(self.refresh_btn)
        self.setLayout(layout)
        self.refresh()

    def refresh(self):
        info = (
            f"Мой IP: {self.net.local_ips}\n"
            f"Broadcast порт: {self.net.broadcast_port}\n"
            f"Чат порт: {self.net.chat_port}\n"
            f"Файловый порт: {self.net.file_port}\n"
            f"Пиров онлайн: {sum(1 for p in self.net.peers.values() if time.time()-p[2]<20)}\n"
            f"Всего пиров: {len(self.net.peers)}\n"
            f"Активных TCP-соединений: {len(self.net.connections)}\n"
            f"Попыток переподключения: {len(self.net.reconnect_attempts)}"
        )
        self.info_label.setText(info)
        try:
            with open(LOG_PATH, 'r') as f:
                lines = f.readlines()[-30:]
                self.log_text.setPlainText(''.join(lines))
        except:
            pass

class MainWindow(QMainWindow):
    def __init__(self, db, nickname, broad_port, chat_port, file_port):
        super().__init__()
        self.db = db
        self.nickname = nickname
        self.setWindowTitle(f"MestoChat — {html.escape(nickname)}")
        self.setMinimumSize(900, 600)
        self.current_peer = None
        self.unread_counts = defaultdict(int)
        self.history_offset = {}

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
            self.net = NetworkCore(db, nickname, broad_port, chat_port, file_port, room_hash)
        except Exception as e:
            QMessageBox.critical(self, "Критическая ошибка", f"Не удалось запустить сеть:\n{e}")
            sys.exit(1)

        self.net.contact_update.connect(self.update_contacts)
        self.net.message_received.connect(self.display_message)
        self.net.file_request_received.connect(self.handle_incoming_file)
        self.net.network_error.connect(self.show_error)
        self.net.file_transfer_failed.connect(self.on_file_transfer_failed)
        self.net.reconnect_requested.connect(self.schedule_reconnect)

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
        quit_action = QAction("Выйти", self)
        quit_action.triggered.connect(self.full_quit)
        tray_menu.addAction(quit_action)
        self.tray_icon.setContextMenu(tray_menu)
        self.tray_icon.activated.connect(self.on_tray_activated)
        self.tray_icon.show()

    def schedule_reconnect(self, peer_id):
        attempts = self.net.reconnect_attempts.get(peer_id, 0)
        if attempts >= 5:
            return
        delay = min(2 ** attempts + random.uniform(0, 1), 30)
        QTimer.singleShot(int(delay * 1000), lambda pid=peer_id: self.net._try_reconnect(pid))

    def _setup_ui(self):
        central = QWidget()
        self.setCentralWidget(central)
        main_layout = QVBoxLayout(central)

        self.tabs = QTabWidget()
        main_layout.addWidget(self.tabs)

        chat_tab = QWidget()
        chat_layout = QHBoxLayout(chat_tab)

        splitter = QSplitter(Qt.Horizontal)
        chat_layout.addWidget(splitter)

        contact_panel = QWidget()
        contact_layout = QVBoxLayout(contact_panel)
        self.contact_filter = QLineEdit()
        self.contact_filter.setPlaceholderText("Поиск контакта...")
        self.contact_filter.textChanged.connect(self.filter_contacts)
        contact_layout.addWidget(self.contact_filter)
        self.contact_list = QListWidget()
        self.contact_list.itemClicked.connect(self.on_contact_clicked)
        contact_layout.addWidget(self.contact_list)
        self.search_input = QLineEdit()
        self.search_input.setPlaceholderText("Поиск сообщений...")
        self.search_input.returnPressed.connect(self.search_messages)
        contact_layout.addWidget(self.search_input)
        self.back_btn = QPushButton("← Назад к чату")
        self.back_btn.clicked.connect(self.return_to_chat)
        self.back_btn.hide()
        contact_layout.addWidget(self.back_btn)
        splitter.addWidget(contact_panel)

        self.stack = QStackedWidget()
        chat_page = QWidget()
        chat_page_layout = QVBoxLayout(chat_page)
        self.chat_display = ChatDisplay()
        self.chat_display.file_dropped.connect(self.on_file_dropped)
        self.chat_display.history_scroll.connect(self.load_more_history)
        self.chat_display.anchorClicked.connect(self._on_anchor_clicked)
        chat_page_layout.addWidget(self.chat_display)

        input_layout = QHBoxLayout()
        self.message_input = QLineEdit()
        self.message_input.setPlaceholderText("Сообщение...")
        self.message_input.returnPressed.connect(self.send_message)
        input_layout.addWidget(self.message_input)

        send_btn = QPushButton("Отправить")
        send_btn.clicked.connect(self.send_message)
        input_layout.addWidget(send_btn)

        file_btn = QPushButton("📎 Файлы")
        file_btn.clicked.connect(self.select_and_send_files)
        input_layout.addWidget(file_btn)

        export_btn = QPushButton("💾 Сохранить чат")
        export_btn.clicked.connect(self.export_chat)
        input_layout.addWidget(export_btn)

        open_folder_btn = QPushButton("📂 Файлы")
        open_folder_btn.clicked.connect(self.open_downloads_folder)
        input_layout.addWidget(open_folder_btn)

        nick_btn = QPushButton("✏️ Ник")
        nick_btn.clicked.connect(self.change_nickname)
        input_layout.addWidget(nick_btn)

        settings_btn = QPushButton("⚙️ Настройки")
        settings_btn.clicked.connect(self.open_settings)
        input_layout.addWidget(settings_btn)

        chat_page_layout.addLayout(input_layout)
        self.stack.addWidget(chat_page)

        search_page = QWidget()
        search_layout = QVBoxLayout(search_page)
        self.search_display = QTextEdit()
        self.search_display.setReadOnly(True)
        search_layout.addWidget(self.search_display)
        self.stack.addWidget(search_page)

        splitter.addWidget(self.stack)
        splitter.setSizes([220, 680])

        self.tabs.addTab(chat_tab, "Чаты")
        self.diag_widget = DiagnosticsWidget(self.net)
        self.tabs.addTab(self.diag_widget, "🩺 Диагностика")

    def _load_contacts(self):
        contacts = self.db.get_all_contacts()
        for machine_id, nickname in contacts:
            if machine_id != MY_MACHINE_ID:
                item = QListWidgetItem(f"🖥 {html.escape(nickname)}")
                item.setData(Qt.UserRole, machine_id)
                self.contact_list.addItem(item)
        unread = self.db.get_all_unread()
        for mid, count in unread.items():
            self.unread_counts[mid] = count
        self._update_contact_display()

    def update_contacts(self, peers):
        current = self.contact_list.currentItem()
        current_id = current.data(Qt.UserRole) if current else None
        self.contact_list.clear()
        online = []
        offline = []
        now = time.time()
        for mid, (ips, nick, last_hello, _) in peers.items():
            safe_nick = html.escape(nick)
            unread = self.unread_counts.get(mid, 0)
            display = f"🖥 {safe_nick}"
            if unread > 0:
                display += f"  ({unread})"
            if last_hello > 0 and now - last_hello < 20:
                online.append((mid, display))
            else:
                offline.append((mid, display))
        online.sort(key=lambda x: x[1].lower())
        offline.sort(key=lambda x: x[1].lower())
        for mid, display in online:
            item = QListWidgetItem(f"🟢 {display}")
            item.setData(Qt.UserRole, mid)
            self.contact_list.addItem(item)
        for mid, display in offline:
            item = QListWidgetItem(f"⚫ {display}")
            item.setData(Qt.UserRole, mid)
            self.contact_list.addItem(item)
        if current_id:
            for i in range(self.contact_list.count()):
                if self.contact_list.item(i).data(Qt.UserRole) == current_id:
                    self.contact_list.setCurrentRow(i)
                    break
        self.filter_contacts(self.contact_filter.text())

    def filter_contacts(self, text):
        for i in range(self.contact_list.count()):
            item = self.contact_list.item(i)
            if text.lower() in item.text().lower():
                item.setHidden(False)
            else:
                item.setHidden(True)

    def on_contact_clicked(self, item):
        self.current_peer = item.data(Qt.UserRole)
        self.history_offset[self.current_peer] = None
        self.load_chat_history(self.current_peer)
        self.stack.setCurrentIndex(0)
        self.back_btn.hide()
        self.db.clear_unread(self.current_peer)
        self.unread_counts[self.current_peer] = 0
        self._update_contact_display()

    def load_chat_history(self, peer_id):
        self.chat_display.clear()
        messages = self.db.get_chat_history(peer_id, limit=50)
        for row in messages:
            self._append_message(row)
        if messages:
            self.history_offset[peer_id] = messages[0][0]

    def _append_message(self, row):
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

    def load_more_history(self):
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

    def display_message(self, sender_id, nick, text, file_name, local_path, is_folder):
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
        if self.current_peer == sender_id and self.stack.currentIndex() == 0:
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

    def _on_anchor_clicked(self, url):
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

    def send_message(self):
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

    def select_and_send_files(self):
        if not self.current_peer:
            QMessageBox.warning(self, "Ошибка", "Выберите контакт.")
            return
        files, _ = QFileDialog.getOpenFileNames(self, "Выберите файлы", "", "Все файлы (*.*)")
        for f in files:
            self.offer_file(f, is_folder=False)

    def on_file_dropped(self, file_path, is_folder):
        if not self.current_peer:
            QMessageBox.warning(self, "Ошибка", "Сначала выберите контакт в списке.")
            return
        if self.net.send_file_request(self.current_peer, file_path, is_folder=is_folder):
            self.chat_display.append(f"<b>Вы:</b> <i>Предложен файл: {html.escape(os.path.basename(file_path))}</i>")
        else:
            self.chat_display.append("<i style='color:red'>⚠ Не удалось предложить файл (контакт офлайн?)</i>")

    def offer_file(self, file_path, is_folder=False):
        if self.net.send_file_request(self.current_peer, file_path, is_folder=is_folder):
            self.chat_display.append(f"<b>Вы:</b> <i>Предложен файл: {html.escape(os.path.basename(file_path))}</i>")
        else:
            self.chat_display.append("<i style='color:red'>⚠ Не удалось предложить файл (контакт офлайн?)</i>")

    def handle_incoming_file(self, sender_id, nick, file_name, file_size, request_id, is_folder):
        item_type = "папку" if is_folder else "файл"
        reply = QMessageBox.question(
            self,
            "Входящий файл",
            f"{html.escape(nick)} хочет передать {item_type}:\n{html.escape(file_name)} ({file_size} байт)\n\nПринять?",
            QMessageBox.Yes | QMessageBox.No
        )
        if reply == QMessageBox.Yes:
            accept_msg = json.dumps({'type': 'file_accept', 'request_id': request_id})
            with self.net.lock:
                sock = self.net.connections.get(sender_id)
            if sock:
                try:
                    self.net._send_frame(sock, accept_msg)
                except:
                    pass
        else:
            reject_msg = json.dumps({'type': 'file_reject', 'request_id': request_id})
            with self.net.lock:
                sock = self.net.connections.get(sender_id)
            if sock:
                try:
                    self.net._send_frame(sock, reject_msg)
                except:
                    pass

    def on_file_transfer_failed(self, peer_id, error_msg):
        if self.current_peer == peer_id and self.stack.currentIndex() == 0:
            self.chat_display.append(f"<i style='color:red'>⚠ {html.escape(error_msg)}</i>")
        else:
            QMessageBox.warning(self, "Ошибка передачи файла", html.escape(error_msg))

    def search_messages(self):
        query = self.search_input.text().strip()
        if query:
            results = self.db.search_messages(query)
            self.search_display.clear()
            self.search_display.append(f"Результаты поиска: {html.escape(query)}")
            for sender_name, message, timestamp in results:
                time_str = datetime.fromtimestamp(timestamp).strftime("%H:%M")
                self.search_display.append(f"<b>[{time_str}] {html.escape(sender_name)}:</b> {html.escape(message)}")
            self.stack.setCurrentIndex(1)
            self.back_btn.show()

    def return_to_chat(self):
        self.stack.setCurrentIndex(0)
        self.back_btn.hide()
        if self.current_peer:
            self.load_chat_history(self.current_peer)

    def export_chat(self):
        if not self.current_peer:
            return
        path, _ = QFileDialog.getSaveFileName(self, "Экспорт чата", f"chat_{self.current_peer}.txt", "Текстовые файлы (*.txt)")
        if path:
            with open(path, 'w', encoding='utf-8') as f:
                f.write(self.chat_display.toPlainText())
            QMessageBox.information(self, "Готово", f"Чат сохранён в {path}")

    def open_downloads_folder(self):
        folder = config.get('download_path', DEFAULT_DOWNLOADS_DIR)
        QDesktopServices.openUrl(QUrl.fromLocalFile(folder))

    def change_nickname(self):
        new_nick, ok = QInputDialog.getText(self, "Сменить ник", "Новый никнейм:", text=self.nickname)
        if ok and new_nick.strip():
            new_nick = new_nick.strip()
            if new_nick != self.nickname:
                self.nickname = new_nick
                self.setWindowTitle(f"MestoChat — {html.escape(new_nick)}")
                self.net.update_nickname(new_nick)

    def open_settings(self):
        dlg = SettingsDialog(self)
        if dlg.exec_() == QDialog.Accepted:
            QMessageBox.information(self, "Настройки", "Изменения вступят в силу после перезапуска программы.")

    def show_error(self, msg):
        QMessageBox.critical(self, "Ошибка", msg)

    def on_tray_activated(self, reason):
        if reason == QSystemTrayIcon.Trigger:
            self.show()

    def closeEvent(self, event):
        if self.tray_icon.isVisible():
            self.hide()
            self.tray_icon.showMessage("MestoChat", "Программа свернута в трей.", QSystemTrayIcon.Information, 2000)
            event.ignore()
        else:
            self.full_quit()

    def full_quit(self):
        self.net.stop()
        self.tray_icon.hide()
        executor.shutdown(wait=False)
        QApplication.quit()

    def _update_contact_display(self):
        for i in range(self.contact_list.count()):
            item = self.contact_list.item(i)
            mid = item.data(Qt.UserRole)
            if mid in self.unread_counts and self.unread_counts[mid] > 0:
                base = item.text().split("  (")[0] if "  (" in item.text() else item.text()
                if "🟢" in base or "⚫" in base:
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
