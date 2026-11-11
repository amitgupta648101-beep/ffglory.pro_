# -*- coding: utf-8 -*-
# ═══════════════════════════════════════════════════════════════════
#  NG RAXX — Squad Bot v6.1
#  4-4 AUTO SQUADS + BG MATCH + CHASE + GUILD(PROTO) + CREATE
#  NO EXTERNAL HTTP GUILD API — fully proto-based clan info/join
# ═══════════════════════════════════════════════════════════════════
import sys, asyncio, httpx, random, json, socket, struct, time, os, uuid
import itertools, secrets, traceback, base64, re, hmac, hashlib, string, ssl
from datetime import datetime
from typing import Dict, List, Optional, Tuple, Any

if sys.platform == "win32":
    try:
        if hasattr(sys.stdout, 'reconfigure'):
            sys.stdout.reconfigure(encoding='utf-8', errors='replace')
            sys.stderr.reconfigure(encoding='utf-8', errors='replace')
    except Exception: pass

from google_play_scraper import app as play_scraper
from Crypto.Cipher import AES
from Crypto.Util.Padding import pad
from protobuf_decoder.protobuf_decoder import Parser
from message_ids import MESSAGE_ID_TO_NAME

import aiohttp
import aiohttp.web

try:
    import NgRaxxFF_pb2
except ImportError:
    NgRaxxFF_pb2 = None

try:
    import NgRaxx_pb2
except ImportError:
    NgRaxx_pb2 = None

try:
    import reqClan_pb2
    _CLAN_PB_AVAILABLE = True
except Exception:
    _CLAN_PB_AVAILABLE = False

try:
    import infoClan_pb2
    _GUILD_INFO_PB_AVAILABLE = True
except Exception:
    _GUILD_INFO_PB_AVAILABLE = False

try:
    import CguFF_pb2
    _START_MATCH_PROTO = CguFF_pb2
except ImportError:
    _START_MATCH_PROTO = NgRaxxFF_pb2 or NgRaxx_pb2

from dashboard_server import start_web_dashboard

# ═══════════════════════════ CONFIG ═══════════════════════════
WEB_HOST = "0.0.0.0"
WEB_PORT = int(os.environ.get("PORT", 20343))
ACCOUNTS_FILE = "accounts.json"
TOKEN_CACHE_FILE = "token_cache.json"
DEVICES_FILE = "devices.json"
TOKEN_CACHE_TTL = 4500

CLAN_ID_DEFAULT = "3105331459"
GUILD_INFO_SHOW_ON_JOIN = True
GUILD_INFO_SHOW_ON_BOOT = True
ENABLE_GUILD_PROTO = True

BOT_NAME_PREFIX = "RAXX_"
BOT_NAME_SUFFIX_LEN = 7

START_MATCH_INTERVAL    = 4.0
NEW_MATCH_DELAY         = 6.0
MAX_MATCH_DURATION      = 3000
MATCH_IDLE_TIMEOUT      = 150.0
HANDSHAKE_TIMEOUT       = 45.0
EXP_REFRESH_INTERVAL    = 30.0
EXP_REFRESH_AFTER_MATCH_DELAY = 9.0
MAX_CONSECUTIVE_PARSE_FAILURES = 5
NON_MATCH_RECONNECT_DELAY      = 1.0
SESSION_RETRY_DELAY            = 5.0

BR_MODE_ID             = 1
BR_MAP_ID              = 1

ANTI_AFK_MIN_INTERVAL  = 1.8
ANTI_AFK_MAX_INTERVAL  = 3.5

MATCH_SEARCH_TIMEOUT   = 90.0
MATCH_WATCHDOG_CHECK   = 30.0
REGION_ROTATION_LIST   = ["IND", "ID", "SG", "TH", "MY", "VN", "PH"]
REGION_ROTATE_EVERY_N  = 2
MAX_SEARCH_ATTEMPTS    = 25

SAFE_PLAY_MODE        = True
BYPASS_TIMING_JITTER  = True
BYPASS_PACKET_JITTER  = True
BYPASS_HELLO_DELAY    = True
BYPASS_KA_JITTER      = True

ENABLE_SPEED_MOVEMENT       = True
MOVEMENT_PATTERN            = "circle"      # circle | random
MOVEMENT_TICK_MS            = 240
MOVEMENT_RADIUS             = 180
MOVEMENT_UPDATE_SPEED_EVERY = 4.0
MOVEMENT_SPEED_MIN          = 1.0
MOVEMENT_SPEED_MAX          = 1.4
MOVEMENT_STATE_IDLE_CHANCE   = 0.10
MOVEMENT_STATE_WALK_CHANCE   = 0.28
MOVEMENT_STATE_RUN_CHANCE    = 0.32
MOVEMENT_STATE_SPRINT_CHANCE = 0.10
MOVEMENT_STATE_JUMP_CHANCE   = 0.08
MOVEMENT_STATE_CROUCH_CHANCE = 0.06
MOVEMENT_STATE_PRONE_CHANCE  = 0.06

ENABLE_HTTP_PING = True
PING_INTERVAL    = 20.0
PING_TIMEOUT     = 8.0
PING_URL         = "https://loginbp.ppmainecoonghj.com/Ping"
PING_REAL_IP     = "103.109.214.211"

FALLBACK_UID = ""
FALLBACK_PASSWORD = ""

# ─── SQUAD GROUPING ───
TEAM_MODE               = True
TEAM_SIZE               = 4
TEAM_PEER_WAIT_TIMEOUT  = 25.0
TEAM_CREATE_WAIT        = 4.0
TEAM_INVITE_CYCLE_WAIT  = 4.0
TEAM_INVITE_MAX_TIME    = 120.0
TEAM_HEARTBEAT_INTERVAL = 3.0
TEAM_IDLE_ITERS_TEAM    = 1800
TEAM_MEMBER_START_DELAY = 20.0
TEAM_FINAL_WAIT         = 8.0
TEAM_READY_DELAY        = 5.0
_accept_friend_request  = True
DEBUG_TEAM_PACKETS      = False

# ─── BACKGROUND MATCH RESTART ───
MAX_BG_MATCHES   = 3
BG_RESTART_DELAY = 2.0
BG_CAP_WAIT_MAX  = 15.0

REGION_LANG = {"ME": "ar", "IND": "hi", "ID": "id", "VN": "vi", "TH": "th",
               "BD": "bn", "PK": "ur", "TW": "zh", "RU": "ru", "SAC": "es",
               "BR": "pt", "NA": "pt", "SG": "pt", "US": "pt"}

FORCED_CLIENT_VERSION = "2.133.13"

# ═══════════════════════════ BOT STATE ═══════════════════════════
class BotState:
    def __init__(self):
        self.accounts: Dict[str, dict] = {}
        self.account_credentials: Dict[str, dict] = {}
        self.account_workers: Dict[str, asyncio.Task] = {}
        self.auth_to_game_id: Dict[str, str] = {}
        self.game_to_auth_id: Dict[str, str] = {}
        self.paused: set = set()
        self.writers: Dict[str, list] = {}
        self.logs: List[dict] = []
        self.total_matches = 0
        self.matches_started = 0
        self.total_exp_gained = 0
        self.create_progress: List[str] = []
        self.creating = False
        self.start_time = time.time()
        self.refresh_callbacks = {}
        self.guild_cache: Dict[str, dict] = {}

    def log(self, msg, level="info"):
        try:
            t = datetime.now().strftime("%H:%M:%S")
            self.logs.append({"t": time.time(), "time": t, "message": str(msg), "level": level})
            if len(self.logs) > 500: self.logs = self.logs[-500:]
        except Exception: pass

    def register_account(self, uid, nickname, region="IND", level=1, exp=0, likes=0,
                         token=None, auth_uid=None):
        uid = str(uid)
        existing = self.accounts.get(uid, {})
        self.accounts[uid] = {
            "uid": uid, "nickname": nickname, "region": region,
            "level": level, "exp": exp, "likes": likes,
            "token": token, "auth_uid": auth_uid,
            "status": "ONLINE", "current_exp": exp,
            "initial_exp": existing.get("initial_exp", exp),
            "gained_exp": existing.get("gained_exp", 0),
            "matches": existing.get("matches", 0), "active_matches": 0,
            "uptime_seconds": existing.get("uptime_seconds", 0),
            "last_match_time": existing.get("last_match_time", "Running..."),
            "is_paused": False,
        }

    def update_status(self, uid, status, matches=0):
        uid = str(uid)
        if uid in self.accounts:
            self.accounts[uid]["status"] = status
            self.accounts[uid]["active_matches"] = matches
            self.accounts[uid]["is_paused"] = (status == "PAUSED")

    def update_exp(self, uid, exp, level=None):
        uid = str(uid)
        if uid in self.accounts:
            a = self.accounts[uid]
            old = a.get("current_exp", 0)
            if exp > old:
                a["gained_exp"] = a.get("gained_exp", 0) + (exp - old)
                self.total_exp_gained += (exp - old)
            a["current_exp"] = exp
            a["exp"] = exp
            if level: a["level"] = level

    def increment_match(self, uid):
        self.total_matches += 1
        uid = str(uid)
        if uid in self.accounts:
            self.accounts[uid]["matches"] = self.accounts[uid].get("matches", 0) + 1
            self.accounts[uid]["last_match_time"] = datetime.now().strftime("%H:%M:%S")

    def increment_match_started(self): self.matches_started += 1

    def register_writer(self, uid, w): self.writers.setdefault(str(uid), []).append(w)

    def unregister_writer(self, uid, w):
        try: self.writers.get(str(uid), []).remove(w)
        except Exception: pass

    def close_writers_for_account(self, uid):
        for w in list(self.writers.get(str(uid), [])):
            try: w.close()
            except Exception: pass
        self.writers[str(uid)] = []

    def is_paused(self, uid): return str(uid) in self.paused

    def toggle_pause(self, uid, state):
        uid = str(uid)
        if state:
            self.paused.add(uid)
            if uid in self.accounts:
                self.accounts[uid]["is_paused"] = True
                self.accounts[uid]["status"] = "PAUSED"
        else:
            self.paused.discard(uid)
            if uid in self.accounts:
                self.accounts[uid]["is_paused"] = False
                if self.accounts[uid].get("status") == "PAUSED":
                    self.accounts[uid]["status"] = "ONLINE"

bot_state = BotState()
_ACTIVE_GROUPS: Dict[int, Any] = {}

# ═══════════════════════════ LOG ═══════════════════════════
class Colors:
    GREEN='\033[92m'; FAIL='\033[91m'; WARNING='\033[93m'
    CYAN='\033[96m'; MAGENTA='\033[95m'; WHITE='\033[97m'; ENDC='\033[0m'

def print_colored(t, c=Colors.WHITE):
    try: print(f"{c}{t}{Colors.ENDC}", flush=True)
    except Exception: pass

def print_success(t):
    print_colored(f"[+] {t}", Colors.GREEN)
    try: bot_state.log(t, "success")
    except Exception: pass

def print_error(t):
    print_colored(f"[-] {t}", Colors.FAIL)
    try: bot_state.log(t, "error")
    except Exception: pass

def print_warning(t):
    print_colored(f"[!] {t}", Colors.WARNING)
    try: bot_state.log(t, "warning")
    except Exception: pass

def print_info(t):
    print_colored(f"[i] {t}", Colors.CYAN)
    try: bot_state.log(t, "info")
    except Exception: pass

def banner_team_code(team_code, uid=""):
    if not team_code: return
    box_w = 50
    line = "═" * box_w
    print_colored(f"╔{line}╗", Colors.GREEN)
    title = f"  🎯 TEAM CODE: {team_code}  "
    pad_n = max(0, (box_w - len(title)) // 2)
    print_colored(f"║{' ' * pad_n}{title}{' ' * (box_w - pad_n - len(title))}║", Colors.GREEN)
    if uid:
        s = f"  Leader: {uid}"
        print_colored(f"║{s:<{box_w}}║", Colors.CYAN)
    print_colored(f"╚{line}╝", Colors.GREEN)
    try: bot_state.log(f"TEAM CODE: {team_code}", "success")
    except Exception: pass

def extract_team_code_from_bytes(buf: bytes) -> Optional[str]:
    if not buf or len(buf) < 5: return None
    m = re.search(rb'\x5a[\x06\x07\x08]([0-9]{6,8})', buf)
    if m:
        c = m.group(1).decode('ascii', 'ignore')
        if c.isdigit() and 6 <= len(c) <= 8: return c
    m2 = re.search(rb'(?:[\x30-\x39]{7})', buf)
    if m2:
        c = m2.group(0).decode('ascii', 'ignore')
        if c.isdigit() and len(c) == 7: return c
    try:
        idx = 0
        while idx < len(buf) - 4:
            if buf[idx] == 0x52:
                length = buf[idx + 1]
                if 6 <= length <= 8 and idx + 2 + length <= len(buf):
                    c = buf[idx + 2:idx + 2 + length].decode('ascii', 'ignore')
                    if c.isdigit() and 6 <= len(c) <= 8: return c
            idx += 1
    except Exception: pass
    return None

def get_proto_field(d, key, default=None):
    if not d or not isinstance(d, dict): return default
    if key in d:
        v = d[key].get('data'); return v if v is not None else default
    if str(key) in d:
        v = d[str(key)].get('data'); return v if v is not None else default
    return default

# ═══════════════════════════ ANTI-BAN ═══════════════════════════
def bypass_jitter(base, spread=0.35):
    if not (SAFE_PLAY_MODE and BYPASS_TIMING_JITTER): return base
    return max(0.05, base + random.uniform(-spread, spread))

def bypass_packet_jitter(base, spread_ratio=0.35):
    if not (SAFE_PLAY_MODE and BYPASS_PACKET_JITTER): return base
    return max(0.1, base + random.uniform(-base * spread_ratio, base * spread_ratio))

def bypass_hello_delay():
    if not (SAFE_PLAY_MODE and BYPASS_HELLO_DELAY): return 0.0
    return random.uniform(0.05, 0.45)

def bypass_ka_jitter(base=5.0):
    if not (SAFE_PLAY_MODE and BYPASS_KA_JITTER): return base
    return max(3.0, base + random.uniform(-0.8, 1.2))

def bypass_human_reconnect_delay(attempt):
    if not (SAFE_PLAY_MODE and BYPASS_TIMING_JITTER): return min(attempt * 0.5, 2.0)
    return max(0.05, min(attempt * 0.5, 2.0) + random.uniform(-0.4, 0.7))

# ═══════════════════════════ BOT NAME ═══════════════════════════
def generate_bot_name() -> str:
    al = string.ascii_uppercase + string.ascii_lowercase + string.digits
    return BOT_NAME_PREFIX + ''.join(random.choices(al, k=BOT_NAME_SUFFIX_LEN))

# ═══════════════════════════ DEVICE ═══════════════════════════
def get_device_for_account(account_identifier):
    devices = {}
    if os.path.exists(DEVICES_FILE):
        try:
            with open(DEVICES_FILE, "r", encoding="utf-8") as f:
                devices = json.load(f)
        except Exception: pass
    key = str(account_identifier)
    if key in devices: return devices[key]
    dev_list = [
        ("Samsung", "SM-G998B", "Adreno (TM) 660", "Android OS 12 / API-31"),
        ("Xiaomi", "2201122G", "Adreno (TM) 730", "Android OS 13 / API-33"),
        ("Realme", "RMX3700", "Mali-G710", "Android OS 14 / API-34"),
        ("OnePlus", "CPH2451", "Adreno (TM) 740", "Android OS 13 / API-33"),
        ("OPPO", "CPH2611", "Adreno (TM) 720", "Android OS 14 / API-34"),
    ]
    brand, model, gpu, os_ver = random.choice(dev_list)
    dev = {
        "unique_device_id": f"Google|{uuid.uuid4()}",
        "brand": brand, "model": model, "gpu_renderer": gpu, "system_software": os_ver,
        "screen_width": random.choice([1080, 1440, 720]),
        "screen_height": random.choice([2400, 3200, 1600]),
        "screen_dpi": str(random.randint(300, 420)),
        "memory": random.randint(2800, 6500),
        "processor_details": f"ARM64 FP ASIMD AES | {random.randint(2200, 3200)} | {random.randint(6, 12)}",
        "client_ip": f"{random.randint(103, 223)}.{random.randint(10, 250)}.{random.randint(10, 250)}.{random.randint(10, 250)}",
    }
    devices[key] = dev
    try:
        with open(DEVICES_FILE, "w", encoding="utf-8") as f:
            json.dump(devices, f, indent=2)
    except Exception: pass
    return dev

# ═══════════════════════════ DNS / SOCKETS ═══════════════════════════
_DNS_CACHE: Dict[str, Tuple[str, float]] = {}
_DNS_CACHE_TTL = 300.0

async def resolve_host_cloudflare(hostname):
    if not hostname: return hostname
    parts = hostname.split('.')
    if len(parts) == 4 and all(p.isdigit() for p in parts): return hostname
    now = time.time()
    if hostname in _DNS_CACHE:
        ip, exp = _DNS_CACHE[hostname]
        if now < exp: return ip
    try:
        loop = asyncio.get_running_loop()
        info = await loop.getaddrinfo(hostname, None, family=socket.AF_INET)
        if info:
            ip = info[0][4][0]
            _DNS_CACHE[hostname] = (ip, now + _DNS_CACHE_TTL)
            return ip
    except Exception: pass
    return hostname

def optimize_tcp_socket(sock):
    try:
        sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_KEEPALIVE, 1)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 131072)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_SNDBUF, 131072)
    except Exception: pass

def optimize_udp_socket(sock):
    try:
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 131072)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_SNDBUF, 131072)
    except Exception: pass

async def safe_close_writer(writer):
    if not writer: return
    try:
        if not writer.is_closing(): writer.close()
        await asyncio.wait_for(writer.wait_closed(), timeout=1.5)
    except Exception: pass

# ═══════════════════════════ HTTP CLIENTS / KEYS ═══════════════════════════
client = httpx.AsyncClient(verify=False, timeout=10.0,
    limits=httpx.Limits(max_connections=300, max_keepalive_connections=150))
_LOGIN_SEMAPHORE = asyncio.Semaphore(4)

headers = {
    'User-Agent': 'UnityPlayer/2018.4.12f1 (UnityWebRequest/1.0, libcurl/8.5.0-DEV)',
    'Connection': 'Keep-Alive', 'Accept-Encoding': 'gzip',
    'Content-Type': 'application/x-www-form-urlencoded',
    'X-Unity-Version': '2018.4.12f1', 'X-GA-SV': '1789535859',
    'X-GA': 'v1 1', 'ReleaseVersion': 'OB55'
}

AES_KEY = b'Yg&tc%DEuh6%Zc^8'
AES_IV  = b'6oyZDr22E3ychjM%'

HEX_KEY = "2ee44819e9b4598845141067b281621874d0d5d7af9d8f7e00c1e54715b7d1e3"
API_KEY = HEX_KEY.encode()

KEYSTREAM = bytes([0x30,0x30,0x30,0x32,0x30,0x31,0x37,0x30,0x30,0x30,0x30,0x30,0x32,
                   0x30,0x31,0x37,0x30,0x30,0x30,0x30,0x30,0x32,0x30,0x31,0x37,0x30,
                   0x30,0x30,0x30,0x30,0x32,0x30])

GGRE_RAW = bytes.fromhex(
    "47475245010101006d020000b260ee08e1f86b4c57f9c70f86bba26ed5d1436bcf52e142db3249d905eded757764991ca31a8373cdd26eab91b80f3f1f6f262f4f10b895d7b6937ddba30a27197453890e9da49373f736c679b8254e2f8e1623e91084a5fdd5374fe478ff99e010834553fddeb0bec4018d142e49df9bb236675b67e852f92a43586f7a7d4d0d7a197a1d4da32714dab4d069ad53214e2c33b3877420a12459738c4c619cbd815fa878bbd104776bb3e1ac7818d5397b04a666ac57f682763ff2df31bc2f846ddc7904f3dce1bda0c4b01f9698e9166f98c84f92640abe3f6317834a42e5c12573b46842c1a6ea8fe6ca9c006dca48a2087e1f983dfb5692771e4a0b15b337ad669b1d08b40862b176bace5331b49a767375b1a8469012aa70a67b55fe71b72478201d0b3ac7269c064c960361e92ee7ba8a42cc6b582bf9b965fb388fa9172ad44c4b073ac23c02080a6bcd106b691ffdf4c7cf71e42f2063fcf196e9bddc5e85be1fe5048eb1b31b460efbb46d76195eef9904c4cba326f2e17ff51fec17dd965aa06dadd4ab07d6966e4a7c38e8afd66dfde56c872bb87516a8f7313c797e4d80e5ad4a5f7afad95c1e0449254adae052e71a3fb98399f93ab30848e0d23252dd45e6fd41bc5fa7303dfb846a8fd713a0032a0b0ae96dfba1bbe41d20abd8099e2cb7fccc329d25bd153029139ef05d090a5093ea557693c0a8d491395b8a23ca844b3887dd5dfc29ac06f4b9be87883a793211b973465e2644c4f5de02b8ab01571401203fc2740423826858cc6da0194c195d27aac4ec4b9d23d506c1501d06440aca3fc180926d75d4a004d3dff21eb4ea1e8c86e6c9627248eff953e1d192d5c8efc006a7e512388ef2ebdb72ee3ad42d719f28e8f994e12ebf4c79f2ffe3abd7408ccd2236a7b89b2606247a732c10c4"
)

CRC7_TABLE = bytes([
    0,9,18,27,36,45,54,63,72,65,90,83,108,101,126,119,25,16,11,2,61,52,47,38,
    81,88,67,74,117,124,103,110,50,59,32,41,22,31,4,13,122,115,104,97,94,87,76,69,
    43,34,57,48,15,6,29,20,99,106,113,120,71,78,85,92,100,109,118,127,64,73,82,91,
    44,37,62,55,8,1,26,19,125,116,111,102,89,80,75,66,53,60,39,46,17,24,3,10,
    86,95,68,77,114,123,96,105,30,23,12,5,58,51,40,33,79,70,93,84,107,98,121,112,
    7,14,21,28,35,42,49,56,65,72,83,90,101,108,119,126,9,0,27,18,45,36,63,54,
    88,81,74,67,124,117,110,103,16,25,2,11,52,61,38,47,115,122,97,104,87,94,69,76,
    59,50,41,32,31,22,13,4,106,99,120,113,78,71,92,85,34,43,48,57,6,15,20,29,
    37,44,55,62,1,8,19,26,109,100,127,118,73,64,91,82,60,53,46,39,24,17,10,3,
    116,125,102,111,80,89,66,75,23,30,5,12,51,58,33,40,95,86,77,68,123,114,105,96,
    14,7,28,21,42,35,56,49,70,79,84,93,98,107,112,121,
])
_DELTA = 0x9E3779B9
_ROUNDS = 16
_FIELD_SIZES = {0:1, 1:2, 2:2, 3:1, 4:2}
_FIELD_NAMES = {0:"sendOption", 1:"cmd", 2:"orderId", 3:"flags", 4:"length"}

# ═══════════════════════════ MATCH COUNTER ═══════════════════════════
_match_counters: Dict[str, int] = {}
_match_counter_lock = asyncio.Lock()

async def _inc_match(uid):
    async with _match_counter_lock:
        _match_counters[uid] = _match_counters.get(uid, 0) + 1
        return _match_counters[uid]

async def _dec_match(uid):
    async with _match_counter_lock:
        if uid in _match_counters and _match_counters[uid] > 0:
            _match_counters[uid] -= 1
        return _match_counters.get(uid, 0)

async def _get_match_count(uid):
    async with _match_counter_lock:
        return _match_counters.get(uid, 0)

# ═══════════════════════════ SQUAD GROUP ═══════════════════════════
class TeamGroup:
    def __init__(self, gid: int, size: int = TEAM_SIZE):
        self.gid = gid
        self.size = max(1, min(int(size), TEAM_SIZE))
        self.peers: Dict[str, Any] = {}
        self.leader_uid: Optional[str] = None
        self.team_code: Optional[str] = None
        self.pk_code: Optional[str] = None
        self.members: set = set()
        self.members_lock = asyncio.Lock()
        self.lock = asyncio.Lock()
        self.active = {"flag": True}

    def tag(self) -> str:
        return f"G{self.gid}"

async def team_member_join(grp: TeamGroup, uid):
    uid = str(uid)
    async with grp.members_lock:
        before = len(grp.members)
        grp.members.add(uid)
        after = len(grp.members)
    if after != before:
        print_success(f"[TEAM-{grp.tag()}] 👥 In team ({after}/{grp.size}) | joined: {uid}")
    return after

async def team_member_leave(grp: TeamGroup, uid):
    async with grp.members_lock:
        grp.members.discard(str(uid))

async def team_member_count(grp: TeamGroup):
    async with grp.members_lock:
        return len(grp.members)

async def team_member_reset(grp: TeamGroup, keep_leader=True):
    async with grp.members_lock:
        grp.members.clear()
        if keep_leader and grp.leader_uid:
            grp.members.add(grp.leader_uid)

# ═══════════════════════════ TOKEN CACHE ═══════════════════════════
_token_cache_memo = {}
_token_cache_memo_time = 0.0
_TOKEN_CACHE_MEMO_TTL = 5.0

def _json_serializer(obj):
    if isinstance(obj, (bytes, bytearray)): return {"__bytes_hex__": bytes(obj).hex()}
    raise TypeError(f"not serializable: {type(obj)}")

def _json_deserializer(obj):
    if isinstance(obj, dict):
        if "__bytes_hex__" in obj and len(obj) == 1:
            try: return bytes.fromhex(obj["__bytes_hex__"])
            except Exception: return b""
        return {k: _json_deserializer(v) for k, v in obj.items()}
    if isinstance(obj, list): return [_json_deserializer(x) for x in obj]
    return obj

def _load_token_cache():
    global _token_cache_memo, _token_cache_memo_time
    now = time.time()
    if _token_cache_memo and (now - _token_cache_memo_time) < _TOKEN_CACHE_MEMO_TTL:
        return _token_cache_memo
    if not os.path.exists(TOKEN_CACHE_FILE): return {}
    try:
        with open(TOKEN_CACHE_FILE, "r", encoding="utf-8") as f:
            content = f.read().strip()
        if not content: return {}
        data = json.loads(content)
        if not isinstance(data, dict): raise ValueError("root must be dict")
        parsed = _json_deserializer(data)
        _token_cache_memo = parsed; _token_cache_memo_time = now
        return parsed
    except Exception as e:
        print_error(f"Token cache corrupt -> delete: {e}")
        try: os.remove(TOKEN_CACHE_FILE)
        except Exception: pass
        return {}

def _save_token_cache(cache):
    global _token_cache_memo, _token_cache_memo_time
    try:
        tmp = TOKEN_CACHE_FILE + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(cache, f, indent=2, default=_json_serializer)
        os.replace(tmp, TOKEN_CACHE_FILE)
        _token_cache_memo = cache; _token_cache_memo_time = time.time()
    except Exception as e: print_error(f"Cache save: {e}")

def cache_get(uid):
    cache = _load_token_cache()
    e = cache.get(str(uid))
    if not e: return None
    if time.time() - e.get("cached_at", 0) > TOKEN_CACHE_TTL:
        cache_invalidate(uid); return None
    if str(e.get("account_id", "")).isdigit(): e["account_id"] = int(e["account_id"])
    if not isinstance(e.get("login_payload_data"), (bytes, bytearray)):
        cache_invalidate(uid); return None
    return e

def cache_set(uid, data):
    cache = _load_token_cache()
    e = dict(data); e["cached_at"] = time.time()
    cache[str(uid)] = e; _save_token_cache(cache)

def cache_invalidate(uid):
    cache = _load_token_cache()
    if str(uid) in cache:
        del cache[str(uid)]; _save_token_cache(cache)

def _update_cache_profile(data, level, exp):
    try:
        keys = []
        if data.get('auth_uid'): keys.append(str(data['auth_uid']))
        if data.get('auth_token'): keys.append(f"tok_{data['auth_token'][:20]}")
        if not keys: return
        cache = _load_token_cache(); ch = False
        for k in keys:
            if k in cache and isinstance(cache[k], dict):
                cache[k]['level'] = level; cache[k]['exp'] = exp; ch = True
        if ch: _save_token_cache(cache)
    except Exception: pass

# ═══════════════════════════ CRYPTO / PROTOBUF ═══════════════════════════
async def aes_encrypt(payload, key, iv):
    return AES.new(key, AES.MODE_CBC, iv).encrypt(pad(payload, AES.block_size))

async def get_playstore_version():
    try:
        loop = asyncio.get_event_loop()
        res = await loop.run_in_executor(
            None, lambda: play_scraper('com.dts.freefireth', lang='hi', country='id'))
        return res.get("version")
    except Exception:
        return "1.134.14"

def get_app_version():
    try: return play_scraper('com.dts.freefireth').get('version')
    except Exception: return "1.134.14"

async def version_config(region="IND"):
    app_version = await get_playstore_version()
    lang = REGION_LANG.get(str(region).upper(), "en")
    url = ("https://version.ggwhitehawk.com/live/ver.php"
           f"?version={app_version}&lang={lang}&device=android&channel=android"
           f"&appstore=googleplay&region={str(region).upper()}"
           "&whitelist_version=1.3.0&whitelist_sp_version=1.0.0")
    try:
        r = await client.get(url); r.raise_for_status()
        j = r.json()
        su = j.get("server_url"); lr = j.get("latest_release_version")
        if not su: return None
        gops = [u.strip() for u in j.get("gop_url", "").split(";") if u.strip()]
        gop_1 = gops[0] if gops else "https://ffmconnect.ppmainecoonghj.com"
        remote = FORCED_CLIENT_VERSION or j.get("remote_version") or app_version
        return lr, remote, su, gop_1, app_version
    except Exception: return None

async def get_access_token(uid, password):
    url = "https://100067.connect.garena.com/oauth/guest/token/grant"
    hdrs = {
        "Host": "100067.connect.garena.com",
        "User-Agent": "Dalvik/2.1.0 (Linux; U; Android 12; SM-G998B)",
        "Content-Type": "application/x-www-form-urlencoded",
        "Accept-Encoding": "gzip, deflate, br", "Connection": "close"
    }
    data = {
        "uid": uid, "password": password, "response_type": "token", "client_type": "2",
        "client_secret": HEX_KEY, "client_id": "100067"
    }
    for attempt in range(5):
        try:
            r = await client.post(url, headers=hdrs, data=data)
            if r.status_code == 200:
                d = r.json()
                oid = d.get("open_id"); at = d.get("access_token"); pf = d.get("platform", 4)
                if oid and at: return oid, at, pf
            if r.status_code == 429: await asyncio.sleep(1); continue
        except Exception: pass
        await asyncio.sleep(0.5)
    return None

def generate_signature(payload_str):
    return hmac.new(API_KEY, payload_str.encode(), hashlib.sha256).hexdigest()

async def register_account(password, gop_url, app_version):
    await asyncio.sleep(3.0)
    connector = aiohttp.TCPConnector(resolver=aiohttp.ThreadedResolver())
    rp = {"app_id": 100067, "client_type": 2, "password": password, "source": 2}
    payload = json.dumps(rp, separators=(',', ':'))
    sig = generate_signature(payload)
    hdrs = {
        "User-Agent": f"GarenaMSDK/4.0.44(SM-E135F ;Android 14;en;GB;app {app_version} 2019118525;)",
        "Authorization": f"Signature {sig}",
        "Accept": "application/json",
        "Content-Type": "application/json; charset=utf-8",
    }
    try:
        async with aiohttp.ClientSession(connector=connector) as s:
            async with s.post(f"{gop_url}/api/v2/oauth/guest:register", headers=hdrs,
                              data=payload, timeout=aiohttp.ClientTimeout(total=15)) as resp:
                data = json.loads(await resp.text())
                if data.get("code") == 0: return data["data"]["uid"]
    except Exception: pass
    return None

async def grant_token(uid, password, gop_url, app_version, max_attempts=5):
    gp = {
        "client_id": 100067, "client_secret": HEX_KEY, "client_type": 2,
        "device_id": f"02-{uuid.uuid4()}", "password": password,
        "response_type": "token", "uid": int(uid),
    }
    payload = json.dumps(gp, separators=(',', ':'))
    sig = generate_signature(payload)
    hdrs = {
        "User-Agent": f"GarenaMSDK/4.0.44(SM-E135F ;Android 14;en;GB;app {app_version} 2019118525;)",
        "Authorization": f"Signature {sig}",
        "Accept": "application/json",
        "Content-Type": "application/json; charset=utf-8",
    }
    urls = [f"{gop_url}/api/v2/oauth/guest/token:grant",
            f"{gop_url}/api/v2/oauth/guest:token:grant"]
    connector = aiohttp.TCPConnector(resolver=aiohttp.ThreadedResolver())
    last_reason = "unknown"
    for attempt in range(max_attempts):
        for url in urls:
            try:
                async with aiohttp.ClientSession(connector=connector) as s:
                    async with s.post(url, headers=hdrs, data=payload,
                                      timeout=aiohttp.ClientTimeout(total=15)) as resp:
                        text = await resp.text()
                        if resp.status != 200:
                            last_reason = f"HTTP {resp.status}: {text[:100]}"; continue
                        try: data = json.loads(text)
                        except Exception:
                            last_reason = f"non-JSON: {text[:100]}"; continue
                        if data.get("code") == 0 and data.get("data"): return data["data"]
                        last_reason = f"code={data.get('code')} msg={data.get('message') or '?'}"
            except Exception as e:
                last_reason = f"{type(e).__name__}: {e}"
        if attempt < max_attempts - 1:
            await asyncio.sleep(2.0 + attempt * 1.5)
    print_error(f"[GRANT] failed for UID {uid} | last={last_reason}")
    return None

async def parse_results(parsed):
    out = {}
    for r in parsed:
        fd = {"wire_type": r.wire_type}
        if r.wire_type in ("varint", "string", "bytes"): fd["data"] = r.data
        elif r.wire_type == "length_delimited":
            fd["data"] = await parse_results(r.data.results)
        out[r.field] = fd
    return out

async def decode_protobuf(data):
    parsed = Parser().parse(data)
    return json.dumps(await parse_results(parsed))

def decode_varint(data, offset):
    result = 0; shift = 0
    while offset < len(data):
        byte = data[offset]
        result |= (byte & 0x7F) << shift
        offset += 1
        if not (byte & 0x80): return result, offset
        shift += 7
    return None, offset

def decode_zigzag(n: int) -> int:
    return (n >> 1) ^ (-(n & 1))

def decode_protobuf_2(data):
    result = {}; offset = 0; dl = len(data)
    while offset < dl:
        header, offset = decode_varint(data, offset)
        if header is None: break
        fn = header >> 3; wt = header & 0x7
        if wt == 0:
            v, offset = decode_varint(data, offset)
            if v is not None: result[fn] = v
        elif wt == 2:
            length, offset = decode_varint(data, offset)
            if length is None: break
            value = data[offset:offset+length]; offset += length
            try:
                s = value.decode('utf-8')
                result[fn] = s if s else value.hex()
            except UnicodeDecodeError:
                nested = decode_protobuf_2(value)
                result[fn] = nested if nested else value.hex()
        elif wt == 1: offset += 8
        elif wt == 3: offset += 4
        else: break
    return result

def extract_raw_fields(data: bytes) -> dict:
    result = {}; offset = 0; dl = len(data)
    while offset < dl:
        header, offset = decode_varint(data, offset)
        if header is None: break
        fn = header >> 3; wt = header & 0x7
        if wt == 0:
            v, offset = decode_varint(data, offset)
            if v is not None: result[fn] = v
        elif wt == 2:
            length, offset = decode_varint(data, offset)
            if length is None: break
            if offset + length > dl: break
            result[fn] = bytes(data[offset:offset+length]); offset += length
        elif wt == 1: offset += 8
        elif wt == 3: offset += 4
        else: break
    return result

def _parse_results_sync(results):
    out = {}
    for r in results:
        fd = {"wire_type": r.wire_type}
        if r.wire_type == "varint": fd["data"] = r.data
        elif r.wire_type in ("string", "bytes"): fd["data"] = r.data
        elif r.wire_type == "length_delimited":
            if hasattr(r.data, "results"): fd["data"] = _parse_results_sync(r.data.results)
            elif isinstance(r.data, list): fd["data"] = _parse_results_sync(r.data)
            else: fd["data"] = str(r.data)
        out[str(r.field)] = fd
    return out

def decode_protobuf_dict(data: bytes) -> dict:
    try: return _parse_results_sync(Parser().parse(data))
    except Exception: return {}

async def decode_protobuf_async(data):
    try: return json.dumps(_parse_results_sync(Parser().parse(data)))
    except Exception: return "{}"

def _decode_proto_manual(data):
    result = {}; offset = 0; dl = len(data)
    while offset < dl:
        header = 0; shift = 0
        while offset < dl:
            b = data[offset]; offset += 1
            header |= (b & 0x7F) << shift
            if not (b & 0x80): break
            shift += 7
            if shift > 28: break
        if header == 0: break
        fn = header >> 3; wt = header & 0x7
        if fn == 0: break
        if wt == 0:
            v = 0; shift = 0
            while offset < dl:
                b = data[offset]; offset += 1
                v |= (b & 0x7F) << shift
                if not (b & 0x80): break
                shift += 7
                if shift > 63: break
            result[fn] = v
        elif wt == 2:
            length = 0; shift = 0
            while offset < dl:
                b = data[offset]; offset += 1
                length |= (b & 0x7F) << shift
                if not (b & 0x80): break
                shift += 7
                if shift > 28: break
            if length > dl - offset: break
            value = data[offset:offset+length]; offset += length
            try:
                s = value.decode('utf-8')
                if s and all(31 < ord(c) < 127 or ord(c) in (9, 10, 13) for c in s):
                    result[fn] = s
                else:
                    nested = _decode_proto_manual(value)
                    result[fn] = nested if nested else value.hex()
            except UnicodeDecodeError:
                nested = _decode_proto_manual(value)
                result[fn] = nested if nested else value.hex()
        elif wt == 5: offset += 4
        elif wt == 1: offset += 8
        else: break
    return result

def _wrap_manual(inner):
    try:
        alt = _decode_proto_manual(inner)
        if alt and len(alt) > 0:
            return {str(k): {"data": v} for k, v in alt.items()}
    except Exception: pass
    return None

def encode_varint(n):
    out = bytearray()
    if n < 0: n &= 0xFFFFFFFFFFFFFFFF
    while True:
        b = n & 0x7F; n >>= 7
        if n: b |= 0x80
        out.append(b)
        if not n: break
    return bytes(out)

def _pb_varint(fn, val): return encode_varint((fn << 3) | 0) + encode_varint(val)
def _pb_length(fn, val):
    enc = val.encode('utf-8') if isinstance(val, str) else val
    return encode_varint((fn << 3) | 2) + encode_varint(len(enc)) + enc

def create_proto(fields):
    packet = bytearray()
    for field, value in fields.items():
        if isinstance(field, str): field = int(field)
        if isinstance(value, dict):
            packet.extend(_pb_length(field, bytes(create_proto(value))))
        elif isinstance(value, list):
            for item in value:
                if isinstance(item, dict): packet.extend(_pb_length(field, bytes(create_proto(item))))
                elif isinstance(item, str): packet.extend(_pb_length(field, item))
                elif isinstance(item, (bytes, bytearray)): packet.extend(_pb_length(field, bytes(item)))
                elif isinstance(item, bool): packet.extend(_pb_varint(field, 1 if item else 0))
                elif isinstance(item, int): packet.extend(_pb_varint(field, item))
        elif isinstance(value, bool): packet.extend(_pb_varint(field, 1 if value else 0))
        elif isinstance(value, int): packet.extend(_pb_varint(field, value))
        elif isinstance(value, str): packet.extend(_pb_length(field, value))
        elif isinstance(value, (bytes, bytearray)): packet.extend(_pb_length(field, bytes(value)))
    return bytes(packet)

def _encode_proto_std(fields):
    out = b""
    for f in sorted(fields.keys()):
        v = fields[f]
        if isinstance(v, bool): out += encode_varint((f << 3) | 0) + encode_varint(int(v))
        elif isinstance(v, int): out += encode_varint((f << 3) | 0) + encode_varint(v)
        elif isinstance(v, (str, bytes)):
            if isinstance(v, str): v = v.encode()
            out += encode_varint((f << 3) | 2) + encode_varint(len(v)) + v
    return out

def encrypt_api(plain_hex):
    return AES.new(AES_KEY, AES.MODE_CBC, AES_IV).encrypt(
        pad(bytes.fromhex(plain_hex), AES.block_size)).hex()

def encrypt_aes(hex_data: str) -> str:
    return encrypt_api(hex_data)

def create_packet(Pk, N, K, V):
    if isinstance(K, str): K = bytes.fromhex(K) if len(K) == 32 else K.encode()
    if isinstance(V, str): V = bytes.fromhex(V) if len(V) == 32 else V.encode()
    PkEnc = AES.new(K, AES.MODE_CBC, V).encrypt(pad(bytes.fromhex(Pk), 16)).hex()
    L = len(PkEnc) // 2
    hexlen = hex(L)[2:]
    if len(hexlen) % 2 != 0: hexlen = '0' + hexlen
    pad_len = 12 - len(N) - len(hexlen)
    if pad_len < 0: pad_len = 0
    return bytes.fromhex(N + ('0' * pad_len) + hexlen + PkEnc)

# ═══════════ SQUAD PACKETS ═══════════
def create_team(key, iv, game_version="1.132.13"):
    fields = {
        1: 1, 2: {2: bytes.fromhex("01"), 3: 1, 4: 3, 5: "en",
            8: {1: "IDC3", 2: 123, 3: "IND"}, 9: 1,
            10: bytes.fromhex("01090a0b1219202729"), 11: 2, 13: 1,
            14: {1: "08FBA33B4BABE2790205390333330000009700050092005F72697EB2134DCBB2467625142201040e38e848dc0e748c3f6aa04d81000000ff1113090dcacfa16d",
                 2: 478, 3: "7e585d55", 4: "y[Z]", 6: 12, 7: "15686677735a7506101c",
                 8: str(game_version), 9: 3, 10: 1, 11: "03626253513637754174"},
            19: 329, 21: bytes.fromhex("374f521955"), 24: {1: 21},
            27: "a_6534489873065906362"}}
    return create_packet(create_proto(fields).hex(), "0515", key, iv)

def team_fresh(account_id, key, iv):
    return create_packet(create_proto({1: 72, 2: {1: int(account_id)}}).hex(), "0515", key, iv)

def invite_player_in_team(target_uid, key, iv, region="IND"):
    return create_packet(create_proto({1: 2, 2: {1: int(target_uid), 2: region, 4: 1}}).hex(),
                         "0515", key, iv)

def accept_team_invite(target_uid, group_id, key, iv):
    fields = {1: 4, 2: {1: int(target_uid), 3: int(target_uid),
        4: bytes.fromhex("0107090a0b120f19202729"), 8: 1,
        9: {1: "08FBA33B0522052002041B0222220007000C00010004000547E265AE1080779546762514110104076fa2e8770e748c3f6a68ed75000000ff08080500cacfa16d",
            2: 235, 3: {14: 80, 11: 86}, 4: "{Y\\R", 6: 13, 7: {2: 4},
            8: "1.132.13", 9: 2, 10: 1, 11: "0362625351"},
        10: str(group_id),
        11: {"1": "IDC3", "2": 107, "3": "IND"}, 13: "en", 16: "374f5219",
        20: {1: 21}, 23: "a_6534489873065906362",
        24: "https://dl-sg-production.freefiremobile.com/",
        27: {1: 2, 2: 4}}}
    return create_packet(create_proto(fields).hex(), "0515", key, iv)

def start_match_team(account_id, key, iv, region="IND"):
    fields = {1: 9, 2: {1: int(account_id), 7: {1: "IDC3", 2: 410, 3: region}}}
    return create_packet(create_proto(fields).hex(), "0515", key, iv)

def ready_for_game(uid, key, iv):
    return create_packet(create_proto({1: 15, 2: {1: uid, 2: 1}}).hex(), "0519", key, iv)

# ═══════════════════════════ NEW START MATCH ═══════════════════════════
def _b64url(data: bytes) -> str:
    return base64.urlsafe_b64encode(data).rstrip(b"=").decode()

def build_match_prepare_payload(uid: int, name: str, account_id: int,
                                region: str = "IND", map_id: int = 41000) -> dict:
    return {
        1: int(uid), 2: str(name), 3: 2, 4: 102000007, 5: 50,
        6: bytes.fromhex("c0b5ce64c091e66080c38566c09ae06180a897638096a361"),
        10: int(account_id), 11: 45, 13: 49, 14: 1000,
        15: bytes.fromhex("c205b622ba10da16"),
        16: region, 17: region, 18: 1, 22: 301, 24: 1, 25: 1, 28: 1,
        29: 1001000100, 33: 49, 40: 1, 46: "", 50: "", 53: "",
        55: 3800, 56: 2, 62: 3800, 63: 2, 66: 2, 69: "", 89: 1, 94: 96,
        107: 1, 110: "", 111: "", 123: 301, 124: "", 126: "",
        131: 3, 132: 4, 133: 16000,
        141: {1: "no_prefer", 2: "no_prefer", 3: "no_prefer", 4: "no_prefer",
              5: "no_prefer", 6: "no_feeling", 11: "no_prefer", 12: "no_prefer",
              13: "no_prefer", 14: "no_prefer", 16: 2, 17: 1,
              18: [{1: 1}, {1: 2}]},
        149: "\x00", 157: 1, 169: int(map_id), 170: 2, 175: 3, 176: 2,
        179: int(time.time()), 190: "", 193: {1: int(uid)}, 208: f"a_{uid}",
        216: {1: 1, 2: [{2: 706}, {1: 1, 2: 4406}, {1: 2, 2: 2106}, {1: 3, 2: 2906}], 5: 1},
        220: 1, 221: 1, 231: "", 237: "2019118527",
    }

def build_match_prepare_jwt(uid: int, name: str, account_id: int,
                            signature: Optional[str] = None,
                            hmac_key: Optional[bytes] = None,
                            region: str = "IND", map_id: int = 41000) -> str:
    header = b'{"alg":"HS256","typ":"JWT"}'
    payload_bytes = create_proto(build_match_prepare_payload(uid, name, account_id,
                                                            region=region, map_id=map_id))
    signing_input = f"{_b64url(header)}.{_b64url(payload_bytes)}"
    if signature:
        return f"{signing_input}.{signature}"
    if hmac_key:
        sig = hmac.new(hmac_key, signing_input.encode(), hashlib.sha256).digest()
        return f"{signing_input}.{_b64url(sig)}"
    return signing_input + "."

def build_start_match_v2(account_id, uid, name, server_ip_port, udp_key, jwt_token,
                         match_code="04312", region="IND", mode=5, map_id=41000,
                         team_size=4, key=None, iv=None, framed=True) -> bytes:
    fields = {
        1: int(account_id), 2: str(server_ip_port), 3: str(udp_key),
        4: str(jwt_token), 5: int(mode), 6: 1, 7: 1, 8: 1, 13: 1,
        42: str(match_code), 44: 1, 45: int(team_size), 46: int(map_id),
    }
    proto_hex = create_proto(fields).hex()
    if framed and key and iv:
        return create_packet(proto_hex, "0515", key, iv)
    return proto_hex

def build_start_match_hex(*args, **kwargs) -> str:
    kwargs["framed"] = False
    return build_start_match_v2(*args, **kwargs)

# ═══════════════════════════ MAJORREGISTER / LOGIN / GETLOGIN ═══════════════════════════
async def major_register(release_v, access_token, open_id, name, game_version,
                         login_url, lang_code="en"):
    field14 = bytes(ord(c) ^ KEYSTREAM[i % 32] for i, c in enumerate(open_id))
    fields = {1: name, 2: access_token, 3: open_id, 5: 102000007, 6: 4, 7: 1, 13: 1,
              14: field14, 15: lang_code, 16: 2, 20: game_version, 21: 1, 22: GGRE_RAW}
    proto = _encode_proto_std(fields)
    payload = AES.new(AES_KEY, AES.MODE_CBC, AES_IV).encrypt(pad(proto, 16))
    url = f"{login_url.rstrip('/')}/MajorRegister"
    hdrs = {
        "Accept": "*/*", "Authorization": "Bearer ",
        "Content-Type": "application/x-www-form-urlencoded",
        "ReleaseVersion": f"{release_v}",
        "User-Agent": "UnityPlayer/2018.4.12f1 (UnityWebRequest/1.0, libcurl/8.5.0-DEV)",
        "X-GA": "v1 1", "X-GA-SV": str(int(time.time())),
        "X-Unity-Version": "2018.4.12f1",
    }
    try:
        ctx = ssl.create_default_context()
        ctx.check_hostname = False; ctx.verify_mode = ssl.CERT_NONE
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=30)) as s:
            async with s.post(url, headers=hdrs, data=payload, ssl=ctx) as resp:
                content = await resp.read()
                if resp.status != 200 or not content: return None
                for off in [0, 64, 48, 32, 16]:
                    if off >= len(content): continue
                    try:
                        r = decode_protobuf_2(content[off:])
                        if r and 3 in r:
                            return {str(k): {"data": v} for k, v in r.items()}
                    except Exception: pass
                return None
    except Exception: return None

async def get_payload(access_token, open_id, platform, version, lang_code="en"):
    device_id = f"Google|{uuid.uuid4()}"
    major_login = {
        "3": str(datetime.now())[:-7], "4": "free fire", "5": 1,
        "7": "1.134.14",
        "8": "Android OS 14 / API-34 (UP1A.231005.007/E156BXXS6AYD4)",
        "9": "Handheld", "10": "airtel", "11": "CarrierDataNetwork",
        "12": 2340, "13": 1080, "14": "295",
        "15": "ARM64 FP ASIMD AES | 2200 | 8", "16": 5586,
        "17": "Mali-G57 MC2", "18": "OpenGL ES 3.2 v1.r38p1",
        "19": device_id, "20": "27.61.46.111", "21": lang_code,
        "22": f"{open_id}", "23": f"{platform}", "24": "Handheld",
        "25": "samsung SM-A146B", "26": "IND", "29": f"{access_token}",
        "30": 1, "41": "airtel", "42": "4G",
        "57": "7428b253defc164018c604a1ebbfebdf",
        "60": 108009, "61": 3859, "62": 5023, "64": 3987,
        "65": 108009, "66": 3987, "67": 108009,
        "70": 4, "73": 3,
        "74": "/data/app/~~OlJmIW-Yzl-44x2WnJP4Nw==/com.garena.game.ffi-_eDk_pQQMiFk1YUeqwJBvQ==/lib/arm64",
        "76": 3,
        "77": "dd9d4c174e0472d34b7fd34bd5924bc9|/data/app/~~OlJmIW-Yzl-44x2WnJP4Nw==/com.garena.game.ffi-_eDk_pQQMiFk1YUeqwJBvQ==/base.apk",
        "78": 3, "79": 2, "81": "64", "83": "2019121269",
        "85": 3, "86": "OpenGLES2", "87": 8191, "88": int(platform),
        "92": 9570, "93": "android",
        "94": "KqsHT54jON6bxITmlrRyOrXWBqKqZ4BoqPzT/mhtriAfRt2dt7gC8pnAJfj11alcEUA5sD8BshSYQhxXT9RFmU6YzcI1FKK4MwxJcF4+kvelPD1H",
        "95": 111207,
        "96": "{\"cur_rate\":null,\"support_etc2\":false}",
        "97": 1, "99": "4", "100": "4", "102": {},
        "104": 11921, "105": 1,
        "106": "https://dl-tata.freefireind.in/live/ABHotUpdates/|https://core-tata.freefireind.in/live/ABHotUpdates/|dff941d41e6e3a9e76f05ed71fdc8d87",
        "107": "1.6168622e0868ddbd",
    }
    send_getlogin = dict(major_login)
    send_getlogin["90"] = "Coimbatore"
    send_getlogin["91"] = "TN"
    send_getlogin["99"] = "4"
    send_getlogin["103"] = 1
    p1 = create_proto(major_login).hex()
    p2 = create_proto(send_getlogin).hex()
    return bytes.fromhex(encrypt_aes(p1)), bytes.fromhex(encrypt_aes(p2))

async def major_login(payload, login_url, release_version):
    url = f"{login_url.rstrip('/')}/MajorLogin"
    hdrs = {"Accept": "*/*", "Authorization": "Bearer ",
            "Content-Type": "application/x-www-form-urlencoded",
            "ReleaseVersion": f"{release_version}",
            "User-Agent": "UnityPlayer/2018.4.12f1 (UnityWebRequest/1.0, libcurl/8.5.0-DEV)",
            "X-GA": "v1 1", "X-GA-SV": str(int(time.time())),
            "X-Unity-Version": "2018.4.12f1"}
    try:
        ctx = ssl.create_default_context()
        ctx.check_hostname = False; ctx.verify_mode = ssl.CERT_NONE
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=15)) as s:
            async with s.post(url, headers=hdrs, data=payload, ssl=ctx) as resp:
                content = await resp.read()
                if resp.status != 200 or len(content) < 200: return None
                best = None; best_score = -1; best_off = 0
                for off in [64, 0, 48, 32, 80, 16, 128, 8, 96, 60, 56, 40, 24, 20, 12, 4]:
                    if off >= len(content): continue
                    cb = content[off:]; cand = None
                    try: cand = decode_protobuf_dict(cb)
                    except Exception: cand = None
                    if not cand:
                        try:
                            c2 = decode_protobuf_2(cb)
                            if c2: cand = {str(k): {"data": v} for k, v in c2.items()}
                        except Exception: cand = None
                    if not cand: continue
                    keys = set(cand.keys())
                    has_jwt = ("8" in keys) or (8 in keys)
                    has_url = ("10" in keys) or (10 in keys)
                    score = len(cand) + (100 if has_jwt else 0) + (50 if has_url else 0)
                    if score > best_score: best = cand; best_score = score; best_off = off
                    if has_jwt and has_url: break
                if not best or ("8" not in best and 8 not in best): return None
                best["__RAW_HEX__"] = content.hex(); best["__OFFSET__"] = best_off
                return best
    except Exception: return None

async def get_login_data(payload, jwt_token, server_url, release_version):
    url = f"{server_url.rstrip('/')}/GetLoginData"
    hdrs = {"Accept": "*/*", "Authorization": f"Bearer {jwt_token}",
            "Content-Type": "application/x-www-form-urlencoded",
            "ReleaseVersion": f"{release_version}",
            "User-Agent": "UnityPlayer/2018.4.12f1", "X-GA": "v1 1",
            "X-GA-SV": str(int(time.time())), "X-Unity-Version": "2018.4.12f1"}
    try:
        ctx = ssl.create_default_context()
        ctx.check_hostname = False; ctx.verify_mode = ssl.CERT_NONE
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=10)) as s:
            async with s.post(url, headers=hdrs, data=payload, ssl=ctx) as r:
                if r.status != 200: return None
                content = await r.read()
                for off in [0, 64, 48, 32, 80, 16, 128, 8, 96, 112, 144, 160]:
                    if off >= len(content): continue
                    try:
                        c = decode_protobuf_dict(content[off:])
                        if c and (("14" in c and "32" in c) or (14 in c and 32 in c)): return c
                    except Exception: pass
                for off in [0, 64, 48, 32, 80, 16, 128, 8, 96]:
                    if off >= len(content): continue
                    try:
                        c = decode_protobuf_dict(content[off:])
                        if c and len(c) >= 3: return c
                    except Exception: pass
                for off in [0, 64, 48, 32, 80]:
                    if off >= len(content): continue
                    c = decode_protobuf_2(content[off:])
                    if c and len(c) >= 3: return {str(k): {"data": v} for k, v in c.items()}
        return None
    except Exception: return None

async def get_player_personal_show(target_uid, jwt_token, server_url, release_version):
    url = f"{server_url}/GetPlayerPersonalShow"
    payload = bytes.fromhex(encrypt_aes(create_proto({"1": int(target_uid)}).hex()))
    hdrs = {"authorization": f"Bearer {jwt_token}",
            "host": server_url.replace("https://", "").split("/")[0],
            "x-ga": "v1 1", "content-type": "application/x-www-form-urlencoded",
            "releaseversion": f"{release_version}",
            "user-agent": "UnityPlayer/2022.3.47f1", "accept": "*/*",
            "x-unity-version": "2022.3.47f1"}
    try:
        ctx = ssl.create_default_context()
        ctx.check_hostname = False; ctx.verify_mode = ssl.CERT_NONE
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=8)) as s:
            async with s.post(url, headers=hdrs, data=payload, ssl=ctx) as r:
                if r.status != 200: return None
                return decode_protobuf_2(await r.read())
    except Exception: return None

def _extract_key_iv(res_json):
    if "__RAW_HEX__" in res_json and "__OFFSET__" in res_json:
        try:
            raw = bytes.fromhex(res_json["__RAW_HEX__"])
            off = int(res_json["__OFFSET__"])
            rf = extract_raw_fields(raw[off:])
            for kf, vf in [(22, 23), (24, 25), (6, 7)]:
                k = rf.get(kf); v = rf.get(vf)
                if isinstance(k, (bytes, bytearray)) and len(k) == 16 and \
                   isinstance(v, (bytes, bytearray)) and len(v) == 16:
                    return bytes(k), bytes(v)
        except Exception: pass
    found = {}
    for k, v in res_json.items():
        if str(k).startswith("__") or not isinstance(v, dict): continue
        data = v.get("data")
        if data is None: continue
        raw = None
        if isinstance(data, (bytes, bytearray)) and len(data) == 16: raw = bytes(data)
        elif isinstance(data, str) and len(data) == 32:
            try:
                c = bytes.fromhex(data)
                if len(c) == 16: raw = c
            except Exception: pass
        if raw and len(raw) == 16:
            try: found[int(k)] = raw
            except Exception: pass
    if len(found) < 2: return None, None
    for kf, vf in [(22, 23), (24, 25), (6, 7)]:
        if kf in found and vf in found: return found[kf], found[vf]
    sk = sorted(found.keys()); return found[sk[0]], found[sk[1]]

async def send_majorlogin(data, release_version, server_url):
    return await major_login(data, server_url, release_version)

async def send_getlogin(data, base_url, token, release_version):
    return await get_login_data(data, token, base_url, release_version)

# ═══════════════════════════ HTTP PING ═══════════════════════════
async def send_ping(account_id, token, release_version, ping_url=None):
    try:
        try: acc = int(account_id)
        except Exception: acc = 0
        now_ms = int(time.time() * 1000)
        payload = struct.pack("<Q", acc & 0xFFFFFFFFFFFFFFFF) + struct.pack("<Q", now_ms & 0xFFFFFFFFFFFFFFFF)
        req_id = secrets.token_urlsafe(18)[:22]
        hdrs = {
            'accept': '*/*', 'accept-encoding': 'deflate, gzip',
            'authorization': f'Bearer {token}',
            'content-type': 'application/x-www-form-urlencoded',
            'releaseversion': release_version,
            'user-agent': 'UnityPlayer/2018.4.12f1',
            'x-ga': 'v1 1', 'x-ga-sv': str(int(time.time())),
            'x-railway-edge': 'sin1', 'x-railway-request-id': req_id,
            'x-real-ip': PING_REAL_IP, 'x-request-start': str(now_ms),
            'x-unity-version': '2018.4.12f1',
        }
        r = await client.post(str(ping_url or PING_URL), headers=hdrs, content=payload, timeout=PING_TIMEOUT)
        return r.status_code == 200
    except Exception: return False

async def ping_worker(account_id, token, release_version, region="IND", ping_url=None):
    if not ENABLE_HTTP_PING: return
    uid_str = str(account_id); ok_count = 0; fails = 0
    try:
        await asyncio.sleep(5.0 + random.uniform(0, 2.0))
        while True:
            ok = await send_ping(uid_str, token, release_version, ping_url)
            if ok: ok_count += 1; fails = 0
            else: fails += 1
            await asyncio.sleep(max(5.0, PING_INTERVAL + random.uniform(-3.0, 3.0)))
    except asyncio.CancelledError: pass

# ═══════════════════════════ TCP STARTUP ═══════════════════════════
async def build_tcp_startup_packet(account_id, token, server_time, key, iv, region="IND", typ='OnLine'):
    uid_hex = f"{int(account_id):016x}"
    ts_hex = f"{int(server_time):08x}"
    enc = (await aes_encrypt(token.encode(), key, iv)).hex()
    enc_len = f"{len(enc)//2:08x}"
    reg = str(region).upper() if region else "IND"
    if typ == 'OnLine':
        pfx = '7219' if reg == 'BD' else ('7214' if reg == 'IND' else '7215')
        return f"{pfx}{uid_hex}{ts_hex}00000000{enc_len}{enc}"
    pfx = '8119' if reg == 'BD' else ('8114' if reg == 'IND' else '8115')
    return f"{pfx}{uid_hex}{ts_hex}{enc_len}{enc}"

async def send_keep_alive(region="IND"):
    try:
        reg = str(region).upper() if region else "IND"
        return bytes.fromhex("0219" if reg == "BD" else ("0214" if reg == "IND" else "0215"))
    except Exception:
        return bytes.fromhex("0215")

# ═══════════════════════════ MATCH SEARCH PACKETS ═══════════════════════════
BR_HEX = (
    "080112800a0a010110013a110a044944433110aa011a064555524f50453a100a044944433210311a064555524f5045"
    "40014a0801090a0b1219202758016291090a80013038384638324246303241393637363730323031303130303030"
    "30303030303030303030313030303130303135303030323232463937454545304630303030303034363736323531"
    "34303030303030303030303030303030303030303030303030303030303030303030303030306666303030303030"
    "3030636163666131366410241afb02735d5e571400024a775d45414d1a041b1c001f11010449715f4243481a001e"
    "1d071c1703004b1a4066785c524570735c51486775421b5c5a4c07504042685a63610816054e19025e7519600147"
    "7c015165406370195f5547404e4550640103020f1304064863754268676c755f65576e40467e5f0a417a4701026d"
    "675d6e73670b1108495a4c6a0b78470b740065645e525a057258425f584a447d4e6759440c11044e7c596d7f4b62"
    "5f7d04055a47505c4e1d6b5b4107447d7201057d7f0f14084e430457674f7e517d72015172415d027473577c4d61"
    "5f79535256780911030f4d5e027a797f614165067806505d53777750475e75064257076500460817014e741e7e50"
    "78487e7a7c465e7669767153497064605a7376677773550d160148037e18675966787f4c42607a645f577e7b44"
    "1b460776026b18685d0b110205490060020f70676175654674706671797f41067346677c4e06585e780f15074c57"
    "047b40517075415f6364027259674b5b0166407f7340600407770a22047a5d5c52300b3a0a167305067162727516"
    "134208312e3133302e3232480350015ae90403626253513635686e556f4e36416456324b796f566c636f47777648"
    "4f624e56526c4d727073504b4f43654177616848494176795556497273743752737149734a7a786b324752526837"
    "7a2f637664626d504f6a73552f79626d38547a4c69586d2f474351696d494b53486833447955726f39515152756c"
    "34545350626d6d624b7949565937545671577059455372323646572f59624578507338514f706d317372785455736c"
    "30796a434144444d4f34616a654b615753366361496c554b4963797a494e396d52516f715277687939797257476d"
    "337a644345337a6a61436f492f5a585233656f65365a42647a64677654636b6b665733356e4d4c6a6a56507256"
    "4b6433523172756174394e50514150724a5546627859696c4c5a3859707336654d5447666b6649793574666a526c"
    "314d4648706b51774c6373374439656378566c41636f374e664f6d2b30654756466c443474447870677138553359"
    "5973587645384842502f70666c767a737138316a32524f4d7857437556445442492f684735625462773166456e42"
    "49725162762b636144775147696f74554e316d4c4b77734379456f4766706746614251457645672b736a764c4c78"
    "704743334c304a5344532f74526169504354553344374e6249306547516651622f5a466f4c36455630775a324d6f"
    "583932414c572f5049752f56634663584e70596b356f7966326151416a536971486a2f363276354843644f525551"
    "303578754e6171795251625653704654303137655237675255636b4966366c6f447476342b514e4a4670766d7475"
    "7077707774396a5a5974437a4b56743657726d6e36785837706658456251555434684f3758a201050803108703a2"
    "01050804108103a20105080510c001a20105081d10cc01a2010408161078a20105080e10af01a201020815"
)

async def start_game_battle_royale(region, client_version, writer, key, iv):
    packet = bytes.fromhex(BR_HEX)
    if _START_MATCH_PROTO is not None:
        try:
            proto = _START_MATCH_PROTO.StartMatch(); proto.ParseFromString(packet)
            reg = str(region).upper() if region else "IND"
            if hasattr(proto.main, 'region_list') and len(proto.main.region_list) > 0:
                proto.main.region_list[0].region = reg
                if len(proto.main.region_list) > 1:
                    proto.main.region_list[1].region = reg
            if hasattr(proto.main, 'client_version'):
                proto.main.client_version.remote_version = client_version
            packet = proto.SerializeToString()
        except Exception: pass
    enc = (await aes_encrypt(packet, key, iv)).hex()
    plen = len(enc) // 2
    hl = hex(plen)[2:]
    hl = hl if len(hl) > 1 else "0" + hl
    reg = str(region).upper() if region else "IND"
    pfx = "031500" if reg == "ID" else ("031400" if reg == "IND" else "031500")
    final = pfx + "0" * (6 - len(hl)) + hl + enc
    writer.write(bytes.fromhex(final)); await writer.drain()
    print_info(f"[BR] search sent ({plen}B) R={reg}")

# ═══════════════════════════ UDP HELPERS ═══════════════════════════
async def has_ssan_zig(n):
    z = (n << 1) & 0xFFFFFFFFFFFFFFFF
    out = bytearray()
    while z >= 0x80: out.append((z & 0x7F) | 0x80); z >>= 7
    out.append(z); return bytes(out)

async def uleb_encode(n):
    out = bytearray()
    while True:
        b = n & 0x7F; n >>= 7
        if n: b |= 0x80
        out.append(b)
        if not n: break
    return bytes(out)

def uleb_encode_sync(n: int) -> bytes:
    return encode_varint(n)

def zigzag_encode(n: int) -> bytes:
    z = (n << 1) if n >= 0 else ((-n) << 1) - 1
    return uleb_encode_sync(z)

async def tea_enc(v0, v1, k0, k1, k2, k3):
    s = 0
    for _ in range(_ROUNDS):
        s = (s + _DELTA) & 0xFFFFFFFF
        v0 = (v0 + (((((v1<<4)&0xFFFFFFFF)+k0)&0xFFFFFFFF ^ ((v1+s)&0xFFFFFFFF) ^ (((v1>>5)+k1)&0xFFFFFFFF)))) & 0xFFFFFFFF
        v1 = (v1 + (((((v0<<4)&0xFFFFFFFF)+k2)&0xFFFFFFFF ^ ((v0+s)&0xFFFFFFFF) ^ (((v0>>5)+k3)&0xFFFFFFFF)))) & 0xFFFFFFFF
    return v0, v1

async def tea_dec(v0, v1, k0, k1, k2, k3):
    s = (_DELTA * _ROUNDS) & 0xFFFFFFFF
    for _ in range(_ROUNDS):
        v1 = (v1 - (((((v0<<4)&0xFFFFFFFF)+k2)&0xFFFFFFFF ^ ((v0+s)&0xFFFFFFFF) ^ (((v0>>5)+k3)&0xFFFFFFFF)))) & 0xFFFFFFFF
        v0 = (v0 - (((((v1<<4)&0xFFFFFFFF)+k0)&0xFFFFFFFF ^ ((v1+s)&0xFFFFFFFF) ^ (((v1>>5)+k1)&0xFFFFFFFF)))) & 0xFFFFFFFF
        s = (s - _DELTA) & 0xFFFFFFFF
    return v0, v1

async def tea_cbc_encrypt(padded, key_bytes):
    k0,k1,k2,k3 = (struct.unpack_from("<I", key_bytes, o)[0] for o in (0,4,8,12))
    out = bytearray(len(padded)); pc = bytearray(8); pi = bytearray(8)
    for i in range(0, len(padded), 8):
        x = bytearray(8)
        for j in range(8): x[j] = padded[i+j] ^ pc[j]
        e0,e1 = await tea_enc(struct.unpack_from("<I", x, 0)[0],
                              struct.unpack_from("<I", x, 4)[0], k0,k1,k2,k3)
        enc = bytearray(8)
        struct.pack_into("<I", enc, 0, e0); struct.pack_into("<I", enc, 4, e1)
        for j in range(8): out[i+j] = enc[j] ^ pi[j]
        pc[:] = out[i:i+8]; pi[:] = x
    return bytes(out)

async def tea_cbc_decrypt(body, key_bytes):
    k0,k1,k2,k3 = (struct.unpack_from("<I", key_bytes, o)[0] for o in (0,4,8,12))
    out = bytearray(len(body)); pi = bytearray(8); pc = bytearray(8)
    x = bytearray(8); dec = bytearray(8)
    for i in range(0, len(body), 8):
        for j in range(8): x[j] = body[i+j] ^ pi[j]
        d0,d1 = await tea_dec(struct.unpack_from("<I", x, 0)[0],
                              struct.unpack_from("<I", x, 4)[0], k0,k1,k2,k3)
        struct.pack_into("<I", dec, 0, d0); struct.pack_into("<I", dec, 4, d1)
        for j in range(8): out[i+j] = dec[j] ^ pc[j]
        pc[:] = body[i:i+8]; pi[:] = dec
    return bytes(out)

async def build_padded(content):
    pad_len = (8 - (len(content) + 10) % 8) % 8
    return bytes([pad_len, 0, 0]) + b"\x00" * pad_len + content + b"\x00" * 7

async def encode_header(layout, so, cmd, oid, flags, length, k, v80):
    out = bytearray()
    for code in layout:
        val = {0:so, 1:cmd, 2:oid, 3:flags, 4:length}[code]
        if _FIELD_SIZES[code] == 1: out.append((val & 0xFF) ^ k)
        else:
            v = ((val & 0xFFFF) ^ v80) & 0xFFFF
            out.append(v & 0xFF); out.append((v >> 8) & 0xFF)
    return bytes(out)

async def crc7_buff(crc, buf):
    c = crc & 0x7F
    for b in buf: c = CRC7_TABLE[((2*(c & 0xFF)) ^ (b & 0xFF)) & 0xFF] & 0x7F
    return c & 0x7F

async def sv_frame(msg_key, layout, so, cmd, oid, flags, content, key, encrypted=True):
    k = key[0]; v80 = ((k << 8) | k) & 0xFFFF
    body = await tea_cbc_encrypt(await build_padded(content), key) if encrypted else content
    hdr = bytearray([msg_key, 0]) + await encode_header(layout, so, cmd, oid, flags, len(body), k, v80)
    pkt = bytearray(hdr + body)
    pkt[1] = await crc7_buff(0, bytes(pkt[2:])) & 0x7F
    return bytes(pkt)

async def build_packet(msg_key, layout, so, cmd, oid, flags, content, key, encrypted=True):
    k = key[0]; v80 = ((k << 8) | k) & 0xFFFF
    body = await tea_cbc_encrypt(await build_padded(content), key) if encrypted else content
    hdr = bytearray([msg_key, 0])
    for code in layout:
        val = {0:so, 1:cmd, 2:oid, 3:flags, 4:len(body)}[code]
        if _FIELD_SIZES[code] == 1: hdr.append((val & 0xFF) ^ k)
        else:
            v = ((val & 0xFFFF) ^ v80) & 0xFFFF
            hdr.append(v & 0xFF); hdr.append((v >> 8) & 0xFF)
    pkt = bytearray(hdr + body)
    pkt[1] = await crc7_buff(0, bytes(pkt[2:])) & 0x7F
    return bytes(pkt)

async def layouts_from_mask(mask):
    ru = [int(c) for c in str(mask).strip()]
    nr = [c for c in ru if c != 2]
    return ru, nr

async def build_hello_packet(text, key, layout):
    data = text.encode("utf-8")
    if len(data) > 25: raise ValueError("too long")
    content = b"\x10\x00\x00\x00" + data + b"\x00" * (29 - 4 - len(data))
    k = key[0] if key else 10
    v80 = ((k << 8) | k) & 0xFFFF
    layout = [int(c) for c in str(layout).strip()] if isinstance(layout, str) else list(layout)
    padded = await build_padded(content)
    enc_body = await tea_cbc_encrypt(padded, key)
    hdr = await encode_header(layout, 1, 1, 0, 1, len(enc_body), k, v80)
    pkt = bytearray([0x63, 0x00]) + hdr + enc_body
    pkt[1] = await crc7_buff(0, pkt[2:]) & 0x7F
    return bytes(pkt).hex()

async def classify(frame):
    cmd = frame["cmd"]
    name = MESSAGE_ID_TO_NAME.get(cmd, f"UNKNOWN_{cmd}")
    if name == "UDP_HELLO": return "HELLO"
    if name == "UDP_ACK": return "ACK"
    if name == "UDP_PING": return "PING"
    if name == "RUDP_JOIN_MATCH": return "JOIN_MATCH"
    if name.startswith("RUDP_"): return name
    if name.startswith("UDP_"): return name
    return "DATA"

async def reply_for(frame, key, mask, ack_key=0x68, ping_key=0x6D, hello_key=0x5B, ack_style="short"):
    _, nr = await layouts_from_mask(mask)
    typ = await classify(frame)
    if typ == "HELLO":
        if ack_style == "echo":
            content = frame["content"] if frame["content"] else b"\x10\x00\x00\x00"
            return typ, await build_packet(hello_key, nr, 1, 1, None, 1, content, key)
        return typ, await build_packet(ack_key, nr, 0, 2, None, 1, b"\x01\x00", key)
    if typ == "ACK":
        content = frame["content"] if frame["content"] else b"\x01\x00"
        return typ, await build_packet(ack_key, nr, 0, 2, None, 1, content, key)
    if typ == "PING":
        c = frame["content"]
        counter = c[:4] if len(c) >= 4 else c
        return typ, await build_packet(ping_key, nr, 0, 3, None, 0, counter + b"\x00\x00\x00", key, encrypted=False)
    if typ == "JOIN_MATCH":
        return typ, await build_packet(ack_key, nr, 0, 2, None, 1, b"\x02\x00", key)
    return typ, None

async def keepalive_ping(sock, ip, port, key_bytes, mask, stop_event):
    nr = (await layouts_from_mask(mask))[1]
    ping_keys = [0x66, 0x6D, 0x69, 0x6C, 0x6B, 0x6E, 0x6F, 0x70]
    loop = asyncio.get_event_loop(); i = 0
    while not stop_event.is_set():
        pk = ping_keys[i % len(ping_keys)]
        counter = int(time.time() * 1000) & 0xFFFFFFFF
        pkt = await build_packet(pk, nr, 0, 3, None, 0, struct.pack("<I", counter) + b"\x00\x00\x00",
                                 key_bytes, encrypted=False)
        try: await loop.sock_sendto(sock, pkt, (ip, port))
        except Exception: pass
        i += 1
        try: await asyncio.wait_for(stop_event.wait(), timeout=bypass_packet_jitter(3.0, 0.4))
        except asyncio.TimeoutError: pass

async def try_header(buf, layout, k, v80):
    off = 2; out = {}
    for code in layout:
        size = _FIELD_SIZES[code]
        if off + size > len(buf): return None
        out[_FIELD_NAMES[code]] = ((buf[off] ^ k) if size == 1
                                    else ((buf[off] | (buf[off+1] << 8)) ^ v80) & 0xFFFF)
        off += size
    out["headerLen"] = off
    return out

async def oicq_unpad(padded):
    if not padded or len(padded) < 8: return None
    if not all(padded[-1-i] == 0 for i in range(7)): return None
    pad_len = padded[0] & 0x07
    s = 3 + pad_len; e = len(padded) - 7
    return padded[s:e] if s < e else b""

async def decode_packet(packet, key, mask=None):
    data = bytes(packet) if isinstance(packet, bytes) else bytes.fromhex(packet)
    if len(data) < 8: return None
    k = key[0]; v80 = ((k << 8) | k) & 0xFFFF
    crc_ok = (data[1] & 0x7F) == await crc7_buff(0, data[2:])
    candidates = []
    if mask:
        ru, nr = await layouts_from_mask(mask)
        layouts = [("RUDP", ru), ("nonRUDP", nr)]
    else:
        layouts = [("RUDP", list(p)) for p in itertools.permutations([0,1,2,3,4])]
        layouts += [("nonRUDP", list(p)) for p in itertools.permutations([0,1,3,4])]
    for kind, layout in layouts:
        f = await try_header(data, layout, k, v80)
        if not f: continue
        if f["flags"] > 7 or f["sendOption"] > 7: continue
        if f["length"] != len(data) - f["headerLen"]: continue
        body = data[f["headerLen"]:f["headerLen"]+f["length"]]
        content = None
        if f["flags"] & 1:
            if len(body) < 8 or len(body) % 8 != 0: continue
            padded = await tea_cbc_decrypt(body, key)
            content = await oicq_unpad(padded)
            if content is None: continue
        else: content = body
        score = (1 if crc_ok else 0) + (1 if content is not None else 0)
        candidates.append({"kind":kind, "layout":layout, "headerLen":f["headerLen"],
            "msgKey":data[0], "cmd":f["cmd"], "flags":f["flags"],
            "sendOption":f["sendOption"], "orderId":f.get("orderId"),
            "length":f["length"], "content":content, "crcOk":crc_ok,
            "score":score, "total":len(data)})
    if not candidates: return None
    candidates.sort(key=lambda c: c["score"], reverse=True)
    return candidates[0]

async def build_match_startup_packets(token, udp_key, match_code, account_id, block_val,
                                      server_ip="", region="IND", client_version="1.132.13",
                                      client_version_code="2019121229", access_token="",
                                      mode_id=BR_MODE_ID, map_id=BR_MAP_ID):
    token = token.strip()
    udp_key = bytes.fromhex(udp_key)
    match_code = [int(ch) for ch in str(match_code).strip()]
    thunder_jwt = token[:660] if len(token) > 660 else token
    sharma_jwt = token[660:] if len(token) > 660 else ""
    eth = thunder_jwt.encode() if isinstance(thunder_jwt, str) else thunder_jwt
    esh = sharma_jwt.encode() if isinstance(sharma_jwt, str) else sharma_jwt
    garena420 = await has_ssan_zig(len(eth)) + eth
    reg = str(region).upper() if region else "IND"
    csoversea_block = bytes.fromhex(
        "ca0163736f7665727365612e7374726f6e67686f6c642e66726565666972656d6f62696c652e636f6d"
        "3b302e302e302e303b33342e3132362e37362e34353b33342e38372e3137372e31343b33342e38372e"
        "3137302e3233303b33352e3138352e3138332e35370000000000000100000000000000000000000001"
        "00000800000100000000000100a8a2d7bebd8d8bdf110200")
    mid = bytes.fromhex('0000000001000102030101') + await has_ssan_zig(len(reg)) + reg.encode()
    mid += bytes.fromhex('0001030003000004')
    mid += await has_ssan_zig(len(client_version)) + client_version.encode()
    mid += await has_ssan_zig(len(client_version_code)) + client_version_code.encode()
    mid += csoversea_block
    clean_ip = server_ip.split(':')[0] if server_ip else "0.0.0.0"
    mid += await has_ssan_zig(len(clean_ip)) + clean_ip.encode()
    if access_token:
        clean_acc = access_token.strip()
        mid += await has_ssan_zig(len(clean_acc)) + clean_acc.encode()
    mid += await has_ssan_zig(len(esh)) + esh
    tg = (await uleb_encode(int(account_id)) + await uleb_encode(int(block_val)) +
          await uleb_encode(1) + await uleb_encode(int(mode_id)) +
          await uleb_encode(int(block_val)) + await uleb_encode(int(map_id)) + mid)
    process = await sv_frame(0x5E, match_code, 2, 447, 0, 1, garena420, udp_key)
    loading = await sv_frame(0x5A, match_code, 2, 448, 1, 1, tg, udp_key)
    return process.hex(), loading.hex()

# ═══════════════════════════ MOVEMENT ═══════════════════════════
def crc7_sync(data: bytes) -> int:
    c = 0
    for b in data:
        c = CRC7_TABLE[((2 * (c & 0xFF)) ^ (b & 0xFF)) & 0xFF] & 0x7F
    return c & 0x7F

def build_movement_packet_2001(key_bytes, msg_key, player_state, x, y, z,
                                tick, counter, move_state, account_uid,
                                room_code, phase="game"):
    if phase == "game":
        TAIL = (b"\x00" * 7 + b"\x93\xca\xd5\xf9\x0b" + b"\x8e\xfe\xfc\xf7\x0b"
                + b"\xf4\xe0\xfe\xf7\x03" + b"\x00\x00")
    else:
        TAIL = (b"\x00" * 7 + b"\xbd\xb6\xe1\xf3\x03" + b"\x00"
                + b"\xc4\xb6\xe1\xfb\x0b" + b"\x00\x00")
    body = bytearray()
    body += uleb_encode_sync(int(account_uid))
    body += uleb_encode_sync(int(player_state))
    body += zigzag_encode(int(x))
    body += zigzag_encode(int(y))
    body += zigzag_encode(int(z))
    body += uleb_encode_sync(0)
    body += uleb_encode_sync(int(move_state))
    body += TAIL
    body += uleb_encode_sync(int(tick) & 0xFFFF)
    body += b"\x00\x00\x00"
    body += uleb_encode_sync(int(counter) & 0xFFFF)
    body = bytes(body)
    k = key_bytes[0]; v80 = ((k << 8) | k) & 0xFFFF
    h = bytearray()
    h.append(msg_key & 0xFF); h.append(0x00); h.append(0x00 ^ k)
    h += ((2001 ^ v80) & 0xFFFF).to_bytes(2, "little")
    h += ((len(body) ^ v80) & 0xFFFF).to_bytes(2, "little")
    h.append(0x00 ^ k)
    h[1] = crc7_sync(bytes(h[2:]) + body) & 0x7F
    return bytes(h) + body

class MovementTracker:
    PLAYER_STATE = {"idle": 0, "walk": 1, "run": 2, "sprint": 3,
                    "jump": 4, "crouch": 5, "prone": 6}

    def __init__(self, pattern="circle", radius=180):
        self.pattern = pattern
        self.radius = int(radius)
        self.tick = 0
        self.counter = 0
        self.angle = random.uniform(0, 6.2832)
        self.speed_multiplier = 1.0
        self.dir_flip = 1
        self._next_speed_roll = time.time()
        self.state = "walk"
        self.state_start = time.time()
        self.state_duration = random.uniform(2.0, 4.0)
        self.curr_x = 0; self.curr_y = 0; self.curr_z = 0
        self.target_pos = None
        self._roll_new_speed()

    def set_target(self, x, y, z):
        self.target_pos = (x, y, z)
        self.state = "sprint"
        self.state_duration = 10.0

    def _roll_new_speed(self):
        try:
            lo, hi = float(MOVEMENT_SPEED_MIN), float(MOVEMENT_SPEED_MAX)
            if hi < lo: lo, hi = hi, lo
            self.speed_multiplier = round(random.uniform(lo, hi), 2)
        except Exception:
            self.speed_multiplier = 1.0
        self._next_speed_roll = time.time() + MOVEMENT_UPDATE_SPEED_EVERY

    def _pick_next_state(self):
        r = random.random()
        ci = MOVEMENT_STATE_IDLE_CHANCE
        cw = ci + MOVEMENT_STATE_WALK_CHANCE
        cr = cw + MOVEMENT_STATE_RUN_CHANCE
        cs = cr + MOVEMENT_STATE_SPRINT_CHANCE
        cj = cs + MOVEMENT_STATE_JUMP_CHANCE
        cc = cj + MOVEMENT_STATE_CROUCH_CHANCE
        if r < ci: return "idle", random.uniform(0.6, 1.6)
        if r < cw: return "walk", random.uniform(1.6, 3.0)
        if r < cr: return "run", random.uniform(2.0, 4.0)
        if r < cs: return "sprint", random.uniform(1.2, 2.5)
        if r < cj: return "jump", random.uniform(0.35, 0.65)
        if r < cc: return "crouch", random.uniform(1.2, 2.5)
        return "prone", random.uniform(1.5, 3.5)

    def _generate_movement(self):
        if self.target_pos:
            tx, ty, tz = self.target_pos
            dx = tx - self.curr_x; dy = ty - self.curr_y; dz = tz - self.curr_z
            dist = (dx*dx + dy*dy + dz*dz) ** 0.5
            if dist > 50:
                speed = 80
                self.curr_x += int(speed * dx / dist)
                self.curr_y += int(speed * dy / dist)
                self.curr_z += int(speed * dz / dist)
                self.state = "sprint"
                return self.curr_x, self.curr_y, self.curr_z, 0x0F
            self.curr_x = tx; self.curr_y = ty; self.curr_z = tz
            self.target_pos = None; self.state = "idle"
            return self.curr_x, self.curr_y, self.curr_z, 0x0F
        if (self.pattern or "circle").lower() == "circle":
            self.angle += 0.35 * self.dir_flip
            if self.angle > 6.2832: self.angle -= 6.2832
            elif self.angle < 0: self.angle += 6.2832
            x = int(self.radius * random.uniform(0.9, 1.1) * (1.0 if self.angle % 3.14 < 1.57 else -1.0))
            y = int(self.radius * random.uniform(0.4, 0.6))
            z = int(self.radius * random.uniform(0.9, 1.1) * (1.0 if self.angle % 6.28 < 3.14 else -1.0))
            self.curr_x = x; self.curr_y = y; self.curr_z = z
            return x, y, z, 0x0F
        self.curr_x = random.randint(-self.radius, self.radius)
        self.curr_y = random.randint(-40, 40)
        self.curr_z = random.randint(-self.radius, self.radius)
        return self.curr_x, self.curr_y, self.curr_z, random.choice([0x01, 0x02, 0x04, 0x08, 0x0F])

    def next(self):
        now = time.time()
        if now >= self._next_speed_roll: self._roll_new_speed()
        if now - self.state_start > self.state_duration:
            self.state, self.state_duration = self._pick_next_state()
            self.state_start = now
        self.tick = (self.tick + 1) & 0xFFFFFFFF
        self.counter = (self.counter + 1) & 0xFFFFFFFF
        ps = self.PLAYER_STATE.get(self.state, 1)
        if self.state in ("idle", "crouch", "prone") and not self.target_pos:
            x, y, z, move_state = self.curr_x, self.curr_y, self.curr_z, 0
        else:
            x, y, z, move_state = self._generate_movement()
        return ps, x, y, z, move_state, self.tick, self.counter, self.speed_multiplier, self.state

async def movement_worker(sock, ip, port, udp_key_bytes, match_code, account_id,
                          stop_event, match_index, tracker):
    loop = asyncio.get_event_loop(); addr = (ip, port)
    sent = 0
    try:
        await asyncio.sleep(random.uniform(2.5, 3.5))
        while not stop_event.is_set():
            try:
                ps, x, y, z, ms, tick, cnt, sm, st = tracker.next()
                pkt = build_movement_packet_2001(udp_key_bytes, 0x6B, ps, x, y, z,
                                                 tick, cnt, ms, account_id, match_code, phase="game")
                await loop.sock_sendto(sock, pkt, addr)
                sent += 1
                base = MOVEMENT_TICK_MS / 1000.0
                try: smx = max(0.7, min(float(sm), 1.6))
                except Exception: smx = 1.0
                wait = max(0.10, min(base / smx, 0.40))
                try:
                    await asyncio.wait_for(stop_event.wait(), timeout=wait); break
                except asyncio.TimeoutError: pass
            except asyncio.CancelledError: break
            except Exception: await asyncio.sleep(0.5)
    except asyncio.CancelledError: pass
    print_info(f"[MOVE] #{match_index} STOPPED | total sent={sent}")

# ═══════════════════════════ ANTI AFK ═══════════════════════════
async def send_anti_afk_fire(sock, addr, udp_key_bytes, match_code, account_id):
    try:
        _, nr = await layouts_from_mask(match_code)
        try: pid = int(account_id)
        except Exception: pid = 0
        ts = int(time.time() * 1000) & 0xFFFFFFFF
        wid = random.choice([101, 102, 103, 201, 202])
        fire = struct.pack("<IIHB", pid & 0xFFFFFFFF, ts, wid, 1)
        fp = await build_packet(0x68, nr, 0, 104, None, 0, fire, udp_key_bytes, encrypted=False)
        loop = asyncio.get_event_loop()
        await loop.sock_sendto(sock, fp, addr)
        await asyncio.sleep(bypass_jitter(random.uniform(0.15, 0.30), 0.05))
        stop = struct.pack("<IIHB", pid & 0xFFFFFFFF, ts + 200, wid, 0)
        sp = await build_packet(0x68, nr, 0, 105, None, 0, stop, udp_key_bytes, encrypted=False)
        await loop.sock_sendto(sock, sp, addr)
        return True
    except Exception: return False

async def anti_afk_worker(sock, ip, port, udp_key_bytes, match_code, account_id,
                          stop_event, match_index):
    addr = (ip, port); fires = 0
    try:
        await asyncio.sleep(bypass_jitter(2.5, 0.5))
        while not stop_event.is_set():
            try:
                if await send_anti_afk_fire(sock, addr, udp_key_bytes, match_code, account_id): fires += 1
                w = random.uniform(ANTI_AFK_MIN_INTERVAL, ANTI_AFK_MAX_INTERVAL)
                w = bypass_packet_jitter(w, 0.25)
                try: await asyncio.wait_for(stop_event.wait(), timeout=w); break
                except asyncio.TimeoutError: pass
            except asyncio.CancelledError: break
            except Exception: await asyncio.sleep(1.0)
    except asyncio.CancelledError: pass

# ═══════════════════════════ PLAY GAME ═══════════════════════════
async def play_game(server_ip_port, thunder, sharma, udp_key, match_code,
                    account_id, player_region, client_version, key, iv,
                    match_index, on_match_complete=None):
    t0 = time.time()
    ping_task = anti_task = move_task = None
    sock = None
    ping_stop = asyncio.Event(); anti_stop = asyncio.Event(); move_stop = asyncio.Event()
    uid_str = str(account_id); completed = False; died = False
    tracker = MovementTracker(pattern=MOVEMENT_PATTERN, radius=MOVEMENT_RADIUS)
    try:
        ip, port = server_ip_port.split(":"); port = int(port)
        rip = await resolve_host_cloudflare(ip)
        loop = asyncio.get_event_loop()
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        try: sock.bind(('0.0.0.0', 0))
        except Exception: pass
        optimize_udp_socket(sock); sock.setblocking(False)
        udp_key_bytes = bytes.fromhex(udp_key)
        await asyncio.sleep(bypass_hello_delay())
        hello = await build_hello_packet(f"{account_id}_2585", udp_key_bytes, match_code)
        await loop.sock_sendto(sock, bytes.fromhex(hello), (rip, port))
        ack_state = "waiting_for_hello_reply"
        thunder_sent = False; join_match_rcv = False; local_closed = False
        send_lock = asyncio.Lock(); anti_started = False
        ping_task = asyncio.create_task(keepalive_ping(sock, rip, port, udp_key_bytes, match_code, ping_stop))
        last_activity = time.time()
        print_colored(f"[MATCH #{match_index}] UDP -> {server_ip_port}", Colors.MAGENTA)

        async def start_workers():
            nonlocal anti_task, move_task, anti_started
            if anti_started: return
            anti_started = True
            anti_task = asyncio.create_task(anti_afk_worker(sock, rip, port, udp_key_bytes, match_code,
                                                            account_id, anti_stop, match_index))
            if ENABLE_SPEED_MOVEMENT:
                move_task = asyncio.create_task(movement_worker(sock, rip, port, udp_key_bytes, match_code,
                                                                account_id, move_stop, match_index, tracker))
                print_success(f"[MOVE] #{match_index} started | {MOVEMENT_PATTERN}")

        async def send_startup():
            nonlocal ack_state, thunder_sent
            if thunder_sent: return
            async with send_lock:
                if thunder_sent: return
                try:
                    await loop.sock_sendto(sock, bytes.fromhex(thunder), (rip, port))
                    thunder_sent = True
                    await asyncio.sleep(bypass_jitter(0.1, 0.05))
                    _, nr = await layouts_from_mask(match_code)
                    ack = await build_packet(0x68, nr, 0, 2, None, 1, b"\x01\x00", udp_key_bytes)
                    await loop.sock_sendto(sock, ack, (rip, port))
                    await asyncio.sleep(bypass_jitter(0.2, 0.05))
                    await loop.sock_sendto(sock, bytes.fromhex(sharma), (rip, port))
                    ack_state = "thunder_sharma_sent"
                    print_success(f"[MATCH #{match_index}] Startup delivered")
                    await start_workers()
                except Exception as e: print_error(f"[MATCH #{match_index}] startup: {e}")

        while not local_closed:
            if time.time() - t0 > MAX_MATCH_DURATION:
                completed = True; break
            if ack_state != "thunder_sharma_sent" and (time.time() - t0) > HANDSHAKE_TIMEOUT:
                print_warning(f"[MATCH #{match_index}] Handshake timeout")
                break
            try:
                resp, saddr = await asyncio.wait_for(loop.sock_recvfrom(sock, 65535), timeout=1.5)
                if resp:
                    last_activity = time.time()
                    frame = await decode_packet(resp, udp_key_bytes, match_code)
                    if frame:
                        pt = await classify(frame)

                        if frame['cmd'] == 2014:
                            try:
                                content = frame["content"]
                                if content:
                                    off = 0
                                    enemy_uid, off = decode_varint(content, off)
                                    ex, off = decode_varint(content, off)
                                    ey, off = decode_varint(content, off)
                                    ez, off = decode_varint(content, off)
                                    ex = decode_zigzag(ex); ey = decode_zigzag(ey); ez = decode_zigzag(ez)
                                    if str(enemy_uid) != uid_str:
                                        tracker.set_target(ex, ey, ez)
                            except Exception: pass
                            continue

                        if frame['cmd'] in [103, 107]:
                            if not died:
                                print_warning(f"[MATCH #{match_index}] Died/Ended cmd={frame['cmd']} -> requeue")
                                died = True; completed = True
                                move_stop.set(); anti_stop.set()
                            local_closed = True; continue

                        if frame['cmd'] == 101:
                            try:
                                _, nr = await layouts_from_mask(match_code)
                                a = await build_packet(0x68, nr, 0, 2, None, 1, b"\x01\x00", udp_key_bytes)
                                await loop.sock_sendto(sock, a, saddr)
                            except Exception: pass
                            continue
                        if pt in ["ACK", "PING", "HELLO", "JOIN_MATCH"]:
                            if pt == "HELLO" and ack_state == "waiting_for_hello_reply":
                                _, r = await reply_for(frame, udp_key_bytes, match_code, ack_style="short")
                                if r: await loop.sock_sendto(sock, r, saddr)
                                ack_state = "ack_sent_waiting"
                            elif pt == "ACK":
                                if ack_state == "waiting_for_hello_reply":
                                    _, r = await reply_for(frame, udp_key_bytes, match_code)
                                    if r: await loop.sock_sendto(sock, r, saddr)
                                    ack_state = "ready_to_send_thunder"
                                elif ack_state == "ack_sent_waiting":
                                    ack_state = "ready_to_send_thunder"
                                else:
                                    _, r = await reply_for(frame, udp_key_bytes, match_code)
                                    if r: await loop.sock_sendto(sock, r, saddr)
                            elif pt == "PING":
                                _, r = await reply_for(frame, udp_key_bytes, match_code)
                                if r: await loop.sock_sendto(sock, r, saddr)
                            elif pt == "JOIN_MATCH" and not join_match_rcv:
                                _, r = await reply_for(frame, udp_key_bytes, match_code)
                                if r: await loop.sock_sendto(sock, r, saddr); join_match_rcv = True
            except asyncio.TimeoutError:
                if ack_state == "ready_to_send_thunder" and not thunder_sent:
                    await send_startup()
                elif ack_state == "waiting_for_hello_reply":
                    if (time.time() - last_activity) > 7.0:
                        try:
                            hp = await build_hello_packet(f"{account_id}_2585", udp_key_bytes, match_code)
                            await loop.sock_sendto(sock, bytes.fromhex(hp), (rip, port))
                        except Exception: pass
                        last_activity = time.time()
                elif ack_state == "thunder_sharma_sent":
                    if (time.time() - last_activity) > MATCH_IDLE_TIMEOUT:
                        print_success(f"[MATCH #{match_index}] Finished naturally")
                        completed = True; break
                continue
            except BlockingIOError: await asyncio.sleep(0.05)
            except OSError: await asyncio.sleep(0.5); continue
            except Exception: await asyncio.sleep(0.5); continue
            if ack_state == "ready_to_send_thunder" and not thunder_sent:
                try: await send_startup()
                except Exception: pass
        return f"match #{match_index} finished"
    except Exception as e:
        print_error(f"[MATCH #{match_index}] {e}"); return f"match #{match_index} error"
    finally:
        if completed:
            try: bot_state.increment_match(uid_str)
            except Exception: pass
            if on_match_complete:
                try: asyncio.create_task(on_match_complete())
                except Exception: pass
        anti_stop.set(); move_stop.set()
        for t in (anti_task, move_task):
            if t:
                try: await asyncio.wait_for(t, timeout=2.0)
                except Exception:
                    t.cancel()
                    try: await t
                    except Exception: pass
        ping_stop.set()
        if ping_task:
            ping_task.cancel()
            try: await ping_task
            except asyncio.CancelledError: pass
        if sock:
            try: sock.close()
            except Exception: pass
        rem = await _dec_match(uid_str)
        print_info(f"[MATCH #{match_index}] Closed. UID:{rem}")
        try: bot_state.update_status(uid_str, "IN_MATCH" if rem > 0 else "IN_QUEUE", rem)
        except Exception: pass

# ═══════════════════════════ SOCIAL PACKETS ═══════════════════════════
async def _process_social_packet(raw_bytes, account_data, tag="MAIN"):
    try:
        hex_data = raw_bytes.hex()
        candidates = []
        if len(raw_bytes) >= 6:
            plen = raw_bytes[4]
            if 0 < plen <= (len(raw_bytes) - 5):
                try:
                    inner = bytes(raw_bytes[5:5 + plen])
                    d0 = decode_protobuf_dict(inner) or _wrap_manual(inner)
                    if d0: candidates.append((5, d0))
                except Exception: pass
        for off in [5, 6, 10, 8, 12, 4, 0]:
            if off >= len(hex_data): continue
            try: inner = bytes.fromhex(hex_data[off:])
            except Exception: continue
            decoded = decode_protobuf_dict(inner) or _wrap_manual(inner)
            if decoded: candidates.append((off, decoded))
        if not candidates: return
        candidates.sort(key=lambda x: len(x[1]) if isinstance(x[1], dict) else 0, reverse=True)
        best_off, decoded = candidates[0]
        def _v(c, k):
            if not isinstance(c, dict): return None
            v = c.get(k) if k in c else c.get(str(k))
            if isinstance(v, dict) and "data" in v: return v["data"]
            return v
        f5w = decoded.get("5") or decoded.get(5) if isinstance(decoded, dict) else None
        f5 = f5w["data"] if isinstance(f5w, dict) and "data" in f5w else f5w
        target = None
        if isinstance(f5, dict):
            for fk in [1, 2, 3, 4, 6]:
                c = _v(f5, fk)
                if c and str(c).isdigit() and 6 <= len(str(c)) <= 15:
                    target = str(c); break
        if not target: return
        own = str(account_data.get('account_id', '')) if account_data else ''
        if own and target == own: return
        if not _accept_friend_request or not account_data: return
        jwt = account_data.get('token'); srv = account_data.get('server_url')
        rel = account_data.get('release_version'); own_id = account_data.get('account_id')
        if not (jwt and srv and rel and own_id): return
        url = f"{srv.rstrip('/')}/ConfirmFriendRequest"
        fields = {"1": int(target), "2": int(own_id)}
        try:
            payload = bytes.fromhex(encrypt_api(create_proto(fields).hex()))
            hdrs = {
                "authorization": f"Bearer {jwt}",
                "host": srv.replace("https://", "").replace("http://", "").split("/")[0],
                "x-ga": "v1 1", "content-type": "application/x-www-form-urlencoded",
                "accept-encoding": "deflate, gzip", "releaseversion": f"{rel}",
                "user-agent": "UnityPlayer/2022.3.47f1", "accept": "*/*",
                "x-unity-version": "2022.3.47f1",
            }
            async with httpx.AsyncClient(verify=False, timeout=8.0) as s:
                r = await s.post(url, headers=hdrs, content=payload)
                if r.status_code == 200 and len(r.content) > 0:
                    print_success(f"[FRIEND-{tag}] ✅ {target}")
        except Exception: pass
    except Exception: pass

async def _handle_team_invite(hex_data, pl, uid_str, current_account_data,
                              current_key, current_iv, writer, grp: TeamGroup):
    try:
        candidates = []
        for off in [10, 8, 6, 12, 14, 4, 16, 0, 20, 2]:
            if off >= len(hex_data) or len(hex_data) - off < 4: continue
            try: inner = bytes.fromhex(hex_data[off:])
            except Exception: continue
            dec = decode_protobuf_dict(inner)
            if dec and isinstance(dec, dict) and len(dec) > 0:
                candidates.append((off, "parser", dec)); continue
            alt = _decode_proto_manual(inner)
            if alt and len(alt) > 0:
                candidates.append((off, "manual", {str(k): {"data": v} for k, v in alt.items()}))
        if not candidates: return False
        candidates.sort(key=lambda x: len(x[2]) if isinstance(x[2], dict) else 0, reverse=True)
        best_off, decoder, dec = candidates[0]

        def _unwrap(d, keys):
            if not isinstance(d, dict): return None
            for k in keys:
                v = d.get(k) if k in d else d.get(str(k))
                if isinstance(v, dict) and "data" in v: return v["data"]
                if isinstance(v, dict): return v
            return None

        target_dict = None
        for kp in [["5"], ["4"], ["6"], ["2"], ["1"]]:
            u = _unwrap(dec, kp)
            if isinstance(u, dict) and len(u) >= 3:
                target_dict = u; break
        if target_dict is None: target_dict = dec

        def _g(d, k):
            if not isinstance(d, dict): return None
            v = d.get(k) if k in d else d.get(str(k))
            if isinstance(v, dict) and "data" in v: return v["data"]
            if isinstance(v, dict):
                for kk in ["1","2","3","4","5","6","7","8"]:
                    vv = v.get(kk) if kk in v else v.get(int(kk))
                    if isinstance(vv, dict) and "data" in vv: return vv["data"]
            return v

        group_id = None
        for k in list(target_dict.keys()):
            c = _g(target_dict, k)
            if isinstance(c, str) and 20 <= len(c) <= 40:
                group_id = c; break
        if not group_id:
            for k in list(dec.keys()):
                c = _g(dec, k)
                if isinstance(c, str) and 20 <= len(c) <= 40:
                    group_id = c; break

        own_acc = str(current_account_data.get('account_id')) if current_account_data else None
        inviter = None
        all_f = list(target_dict.keys()) + list(dec.keys())
        for k in all_f:
            c = _g(target_dict, k) or _g(dec, k)
            if c and str(c).isdigit() and 6 <= len(str(c)) <= 15:
                if str(c) != uid_str and str(c) != own_acc:
                    inviter = str(c); break

        tc = None
        for k in all_f:
            c = _g(target_dict, k) or _g(dec, k)
            if c and str(c).isdigit() and len(str(c)) == 7:
                tc = str(c); break
        if tc:
            async with grp.lock:
                if grp.team_code != tc:
                    grp.team_code = tc
                    banner_team_code(tc, uid_str)

        is_member = (grp.leader_uid != uid_str)
        if inviter and group_id and is_member:
            async with grp.members_lock:
                already = uid_str in grp.members
            if already: return True
            accepted = False
            for attempt in range(3):
                try:
                    acc = accept_team_invite(int(inviter), group_id, current_key, current_iv)
                    if writer and not writer.is_closing():
                        writer.write(acc); await writer.drain()
                        accepted = True; break
                except Exception: pass
                await asyncio.sleep(0.8)
            if accepted:
                await team_member_join(grp, uid_str)
            return True
        return False
    except Exception: return False

# ═══════════════════════════ FUNCTIONAL ═══════════════════════════
async def functional_battle_royale(addrs, starter_packet, account_region, client_version,
                                    key, iv, account_id="", account_data=None,
                                    account_level=2, max_reconnects=10,
                                    grp: Optional[TeamGroup] = None):
    if grp is None:
        grp = TeamGroup(0, TEAM_SIZE)
    if not addrs or ":" not in str(addrs):
        print_error(f"[FUNC] Missing TCP address for {account_id}")
        return

    reconnects = 0
    ip, port = addrs.split(":")
    play_matches: List[asyncio.Task] = []
    no_response_count = 0
    uid_str = str(account_id)
    current_level = int(account_level or 2)
    current_token = starter_packet
    current_key = key; current_iv = iv
    current_account_data = account_data
    reconnect_count_total = 0
    region_index = 0
    current_search_region = account_region or REGION_ROTATION_LIST[0]
    _writer_ref = {"w": None}

    def _bg_match_done(t):
        play_matches[:] = [m for m in play_matches if not m.done()]
        print_info(f"[BG] match finished {uid_str} | running={len(play_matches)}")

    async def trigger_post_match_refresh():
        await asyncio.sleep(EXP_REFRESH_AFTER_MATCH_DELAY)
        try:
            cd = bot_state.account_credentials.get(uid_str)
            if cd: await refresh_account_profile(cd)
        except Exception: pass

    async def _team_coordinator():
        try:
            deadline = time.time() + TEAM_PEER_WAIT_TIMEOUT
            while time.time() < deadline:
                async with grp.lock:
                    n = len(grp.peers)
                if n >= grp.size: break
                await asyncio.sleep(0.4)

            async with grp.lock:
                is_leader = (grp.leader_uid == uid_str)
                peers_snapshot = dict(grp.peers)

            if not is_leader: return

            await asyncio.sleep(TEAM_READY_DELAY)
            print_success(f"[TEAM-{grp.tag()}] 👑 {uid_str} creating squad...")

            async with grp.lock:
                grp.team_code = None
                grp.pk_code = None

            own_id_num = None
            if current_account_data: own_id_num = current_account_data.get('account_id')
            if not own_id_num:
                try: own_id_num = int(uid_str)
                except Exception: own_id_num = 0

            try:
                pkt = create_team(current_key, current_iv, client_version)
                if _writer_ref["w"] and not _writer_ref["w"].is_closing():
                    _writer_ref["w"].write(pkt); await _writer_ref["w"].drain()
                    await team_member_reset(grp, keep_leader=False)
                    await team_member_join(grp, uid_str)
                    print_info(f"[TEAM-{grp.tag()}] create_team sent ({len(pkt)}B)")
            except Exception as e:
                print_error(f"[TEAM-{grp.tag()}] create_team: {e}")

            await asyncio.sleep(TEAM_CREATE_WAIT)

            try:
                await asyncio.sleep(2.0)
                async with grp.lock:
                    tc = grp.team_code
                if tc: banner_team_code(tc, uid_str)
                else: print_warning(f"[TEAM-{grp.tag()}] Team code not yet received")
            except Exception: pass

            peer_uids = []
            for peer_uid, info in peers_snapshot.items():
                if peer_uid == uid_str: continue
                pa = None
                try: pa = info["data"].get("account_id")
                except Exception: pass
                if not pa: pa = peer_uid
                peer_uids.append(int(pa))

            heartbeat_stop = asyncio.Event()
            async def heartbeat_loop():
                while not heartbeat_stop.is_set():
                    try:
                        if _writer_ref["w"] and not _writer_ref["w"].is_closing():
                            pkt = team_fresh(int(own_id_num), current_key, current_iv)
                            _writer_ref["w"].write(pkt); await _writer_ref["w"].drain()
                    except Exception: pass
                    try: await asyncio.wait_for(heartbeat_stop.wait(), timeout=TEAM_HEARTBEAT_INTERVAL)
                    except asyncio.TimeoutError: pass
            hb_task = asyncio.create_task(heartbeat_loop())

            invite_start = time.time()
            while time.time() - invite_start < TEAM_INVITE_MAX_TIME:
                if not grp.active["flag"]: break
                cnt = await team_member_count(grp)
                if cnt >= grp.size: break
                for tuid in peer_uids:
                    async with grp.members_lock:
                        joined = str(tuid) in grp.members
                    if joined: continue
                    try:
                        inv = invite_player_in_team(tuid, current_key, current_iv, region=account_region)
                        if _writer_ref["w"] and not _writer_ref["w"].is_closing():
                            _writer_ref["w"].write(inv); await _writer_ref["w"].drain()
                    except Exception: pass
                    await asyncio.sleep(0.5)
                try: await asyncio.wait_for(heartbeat_stop.wait(), timeout=TEAM_INVITE_CYCLE_WAIT)
                except asyncio.TimeoutError: pass

            final_cnt = await team_member_count(grp)
            if final_cnt < grp.size:
                heartbeat_stop.set()
                try: hb_task.cancel(); await hb_task
                except Exception: pass
                return

            await asyncio.sleep(TEAM_FINAL_WAIT)
            heartbeat_stop.set()
            try: hb_task.cancel(); await hb_task
            except Exception: pass

            while grp.active["flag"]:
                try:
                    async with grp.lock:
                        if grp.leader_uid != uid_str: break
                    oid = current_account_data.get('account_id', own_id_num) if current_account_data else own_id_num
                    try:
                        rdy = ready_for_game(int(oid), current_key, current_iv)
                        if _writer_ref["w"] and not _writer_ref["w"].is_closing():
                            _writer_ref["w"].write(rdy); await _writer_ref["w"].drain()
                    except Exception: pass
                    await asyncio.sleep(1.0)
                    sm = start_match_team(int(oid), current_key, current_iv, region=account_region)
                    if _writer_ref["w"] and not _writer_ref["w"].is_closing():
                        _writer_ref["w"].write(sm); await _writer_ref["w"].drain()
                except Exception: pass
                try: await asyncio.wait_for(asyncio.sleep(5.0), timeout=5.5)
                except asyncio.TimeoutError: pass
        except asyncio.CancelledError: raise
        except Exception as e:
            print_error(f"[TEAM-{grp.tag()}] coordinator: {e}")

    async def _member_match_trigger():
        try:
            await asyncio.sleep(TEAM_READY_DELAY + TEAM_MEMBER_START_DELAY)
            async with grp.lock:
                if grp.leader_uid == uid_str: return
            my_id = current_account_data.get('account_id', uid_str) if current_account_data else uid_str
            while grp.active["flag"]:
                try:
                    if _writer_ref["w"] and not _writer_ref["w"].is_closing():
                        try:
                            rdy = ready_for_game(int(my_id), current_key, current_iv)
                            _writer_ref["w"].write(rdy); await _writer_ref["w"].drain()
                        except Exception: pass
                        await asyncio.sleep(1.0)
                        sm = start_match_team(int(my_id), current_key, current_iv, region=account_region)
                        _writer_ref["w"].write(sm); await _writer_ref["w"].drain()
                except Exception: pass
                try: await asyncio.wait_for(asyncio.sleep(5.0), timeout=5.5)
                except asyncio.TimeoutError: pass
        except asyncio.CancelledError: raise
        except Exception: pass

    try:
        while True:
            writer = None; gateway_ping_task = None
            team_coord_task = None; member_trigger_task = None
            try:
                if current_account_data:
                    fresh = None
                    if current_account_data.get('auth_type') == 'guest' and current_account_data.get('auth_uid'):
                        fresh = cache_get(str(current_account_data['auth_uid']))
                    elif current_account_data.get('auth_type') == 'token' and current_account_data.get('auth_token'):
                        fresh = cache_get(f"tok_{current_account_data['auth_token'][:20]}")
                    if fresh:
                        current_account_data = fresh
                        current_key = fresh['aes_ak']; current_iv = fresh['iv_i']
                        current_token = await build_tcp_startup_packet(
                            fresh['account_id'], fresh['token'], fresh['server_time'],
                            current_key, current_iv,
                            region=fresh.get('region', account_region), typ='OnLine')
                        try:
                            lv = int(fresh.get('level', current_level) or current_level)
                            if lv != current_level: current_level = lv
                        except Exception: pass
                    else:
                        try:
                            if current_account_data.get('auth_uid'):
                                cache_invalidate(str(current_account_data['auth_uid']))
                            if current_account_data.get('auth_token'):
                                cache_invalidate(f"tok_{current_account_data['auth_token'][:20]}")
                        except Exception: pass
                        raise ConnectionError("Cache expired")

                rip = await resolve_host_cloudflare(ip)
                reader, writer = await asyncio.open_connection(rip, int(port))
                _writer_ref["w"] = writer
                raw_sock = writer.get_extra_info('socket')
                if raw_sock: optimize_tcp_socket(raw_sock)
                await asyncio.sleep(bypass_hello_delay())
                writer.write(bytes.fromhex(current_token)); await writer.drain()
                try:
                    ka = await send_keep_alive(account_region)
                    if ka and not writer.is_closing():
                        writer.write(ka); await asyncio.wait_for(writer.drain(), timeout=3)
                except Exception: pass

                async def func_gateway_keepalive():
                    ka_bytes = await send_keep_alive(account_region)
                    while True:
                        await asyncio.sleep(bypass_ka_jitter(5.0))
                        try:
                            if writer and not writer.is_closing():
                                writer.write(ka_bytes); await writer.drain()
                        except Exception: break
                gateway_ping_task = asyncio.create_task(func_gateway_keepalive())

                connection_start_time = asyncio.get_running_loop().time()
                last_watchdog_check = connection_start_time
                search_attempts = 0
                if reconnect_count_total > 0 and (reconnect_count_total % REGION_ROTATE_EVERY_N == 0):
                    region_index = (region_index + 1) % len(REGION_ROTATION_LIST)
                    current_search_region = REGION_ROTATION_LIST[region_index]
                else:
                    current_search_region = account_region or REGION_ROTATION_LIST[region_index]

                print_success(f"[FUNC-{grp.tag()}] TCP connected {uid_str} (DNS:{rip} Lvl:{current_level})")
                reconnects = 0; no_response_count = 0

                async with grp.lock:
                    grp.peers[uid_str] = {
                        "writer": writer, "data": current_account_data,
                        "key": current_key, "iv": current_iv}
                    if grp.leader_uid is None:
                        grp.leader_uid = uid_str
                        print_success(f"[TEAM-{grp.tag()}] 👑 {uid_str} is leader")

                if TEAM_MODE:
                    team_coord_task = asyncio.create_task(_team_coordinator())
                    member_trigger_task = asyncio.create_task(_member_match_trigger())
                else:
                    await start_game_battle_royale(current_search_region, client_version,
                                                   writer, current_key, current_iv)

                while True:
                    play_matches[:] = [m for m in play_matches if not m.done()]
                    active = await _get_match_count(uid_str)
                    try: bot_state.update_status(uid_str, "IN_QUEUE" if active == 0 else "IN_MATCH", active)
                    except Exception: pass

                    now = asyncio.get_running_loop().time()
                    if now - last_watchdog_check >= MATCH_WATCHDOG_CHECK:
                        last_watchdog_check = now
                        sd = now - connection_start_time
                        if sd > MATCH_SEARCH_TIMEOUT:
                            if active > 0:
                                connection_start_time = now
                            else:
                                raise ConnectionError("Search watchdog")
                    if search_attempts >= MAX_SEARCH_ATTEMPTS:
                        raise ConnectionError("Max attempts")

                    try:
                        data = await asyncio.wait_for(reader.read(8192), timeout=0.5)
                    except asyncio.TimeoutError:
                        no_response_count += 1
                        if TEAM_MODE:
                            if no_response_count > TEAM_IDLE_ITERS_TEAM:
                                raise ConnectionError("Team idle timeout")
                        else:
                            if no_response_count > 80: raise ConnectionError("idle")
                        continue

                    if not data: raise ConnectionError("closed")
                    hex_data = data.hex()
                    pl = len(data)
                    no_response_count = 0

                    try:
                        tc = extract_team_code_from_bytes(data)
                        if tc:
                            async with grp.lock:
                                if grp.team_code != tc:
                                    grp.team_code = tc
                                    should_banner = True
                                else:
                                    should_banner = False
                            if should_banner:
                                banner_team_code(tc, uid_str)
                    except Exception: pass

                    if hex_data.startswith("0600") and pl > 20:
                        await _process_social_packet(data, current_account_data, tag="MAIN")
                        continue

                    if hex_data.startswith("05") and pl > 10:
                        await _handle_team_invite(hex_data, pl, uid_str, current_account_data,
                                                  current_key, current_iv, writer, grp)
                        continue

                    if hex_data.startswith("0300") and 10 < pl < 30:
                        continue

                    if hex_data.startswith("0300") and pl >= 300:
                        print_colored("=" * 60, Colors.GREEN)
                        print_colored("MATCH FOUND! Loading...", Colors.GREEN)
                        print_colored("=" * 60, Colors.GREEN)

                        for tk in (team_coord_task, member_trigger_task):
                            if tk and not tk.done():
                                tk.cancel()
                                try: await tk
                                except asyncio.CancelledError: pass
                        team_coord_task = None; member_trigger_task = None
                        grp.active["flag"] = False

                        try:
                            res = json.loads(await decode_protobuf(hex_data[10:]))
                            token = udp_key = match_code = server_ip_port = None
                            match_account_id = block_val = None

                            if '42' in res and 'data' in res['42']:
                                match_code = res['42']['data']
                            if '2' in res and 'data' in res['2'] and isinstance(res['2']['data'], str):
                                server_ip_port = res['2']['data']
                            if '3' in res and 'data' in res['3']:
                                udp_key = res['3']['data']
                            if '4' in res and 'data' in res['4']:
                                token = res['4']['data']
                            if '1' in res and 'data' in res['1']:
                                match_account_id = res['1']['data']

                            if '5' in res and 'data' in res['5'] and isinstance(res['5']['data'], dict):
                                r5 = res['5']['data']
                                server_ip_port = r5.get('2', {}).get('data') or server_ip_port
                                udp_key = r5.get('3', {}).get('data') or udp_key
                                token = r5.get('4', {}).get('data') or token
                                if '42' in r5: match_code = r5['42']['data']
                                block_val = r5.get('1', {}).get('data') or block_val

                            effective = match_account_id or account_id or "BD_BOT"
                            if token and udp_key and match_code and server_ip_port:
                                acc_tok = current_account_data.get('access_token', '') if current_account_data else ""
                                thunder, sharma = await build_match_startup_packets(
                                    token, udp_key, match_code, effective, block_val or 0,
                                    server_ip=server_ip_port, region=account_region,
                                    client_version=client_version, access_token=acc_tok,
                                    mode_id=BR_MODE_ID, map_id=BR_MAP_ID)

                                try:
                                    _uid_num = None
                                    if current_account_data:
                                        _uid_num = current_account_data.get('uid') or \
                                                   current_account_data.get('auth_uid') or \
                                                   current_account_data.get('open_id')
                                    _uid_num = int(_uid_num) if _uid_num else int(effective)
                                    _name = (current_account_data or {}).get('nickname', f"Player_{_uid_num}")
                                    _acc_id = int(effective)
                                    sm_pkt = build_start_match_v2(
                                        _acc_id, _uid_num, _name, server_ip_port, udp_key,
                                        token, match_code=str(match_code), region=account_region,
                                        key=current_key, iv=current_iv, framed=True)
                                    if writer and not writer.is_closing():
                                        writer.write(sm_pkt); await writer.drain()
                                        print_success(f"[START-MATCH] sent {len(sm_pkt)}B uid={_uid_num} name={_name}")
                                except Exception as _e:
                                    print_warning(f"[START-MATCH] {_e}")

                                match_index = await _inc_match(uid_str)
                                print_colored(f"[MATCH #{match_index}] UDP -> {server_ip_port} (BACKGROUND)", Colors.CYAN)

                                new_match = asyncio.create_task(play_game(
                                    server_ip_port, thunder, sharma, udp_key, match_code,
                                    effective, current_search_region, client_version,
                                    current_key, current_iv,
                                    match_index=match_index, on_match_complete=trigger_post_match_refresh))
                                play_matches.append(new_match)
                                new_match.add_done_callback(_bg_match_done)

                                await team_member_leave(grp, uid_str)
                                await team_member_reset(grp, keep_leader=False)
                                async with grp.lock:
                                    grp.pk_code = None
                                    grp.team_code = None
                                    grp.peers[uid_str] = {
                                        "writer": writer,
                                        "data": current_account_data,
                                        "key": current_key, "iv": current_iv}
                                    if not grp.leader_uid:
                                        grp.leader_uid = uid_str

                                grp.active["flag"] = True

                                _w = 0.0
                                while (await _get_match_count(uid_str)) >= MAX_BG_MATCHES and _w < BG_CAP_WAIT_MAX:
                                    await asyncio.sleep(0.5); _w += 0.5

                                await asyncio.sleep(BG_RESTART_DELAY)

                                if TEAM_MODE:
                                    team_coord_task = asyncio.create_task(_team_coordinator())
                                    member_trigger_task = asyncio.create_task(_member_match_trigger())
                                else:
                                    await start_game_battle_royale(
                                        current_search_region, client_version,
                                        writer, current_key, current_iv)

                                connection_start_time = asyncio.get_running_loop().time()
                                last_watchdog_check = connection_start_time
                                no_response_count = 0
                                search_attempts = 0
                                reconnect_count_total += 1
                                continue
                            else:
                                await safe_close_writer(writer)
                                await asyncio.sleep(NON_MATCH_RECONNECT_DELAY)
                                break
                        except Exception as e:
                            print_error(f"[FUNC-{grp.tag()}] Match parse: {e}")
                            await safe_close_writer(writer)
                            await asyncio.sleep(NON_MATCH_RECONNECT_DELAY)
                            break

                    if 30 <= pl <= 40: continue

            except asyncio.CancelledError:
                for m in play_matches:
                    if not m.done(): m.cancel()
                if play_matches:
                    await asyncio.gather(*play_matches, return_exceptions=True)
                play_matches.clear()
                if gateway_ping_task: gateway_ping_task.cancel()
                async with grp.lock:
                    grp.peers.pop(uid_str, None)
                    if grp.leader_uid == uid_str:
                        grp.leader_uid = None
                await team_member_leave(grp, uid_str)
                raise
            except Exception as e:
                if gateway_ping_task: gateway_ping_task.cancel()
                print_error(f"[FUNC-{grp.tag()}] TCP state {uid_str}: {e}")
                play_matches[:] = [m for m in play_matches if not m.done()]
                await safe_close_writer(writer)
                if "Cache expired" in str(e):
                    break
                reconnect_count_total += 1
                reconnects += 1
                if reconnects > max_reconnects:
                    reconnects = 0
                    await asyncio.sleep(3)
                    continue
                await asyncio.sleep(bypass_human_reconnect_delay(reconnects))
            finally:
                grp.active["flag"] = False
                for tk in (team_coord_task, member_trigger_task):
                    if tk and not tk.done():
                        tk.cancel()
                        try: await tk
                        except (asyncio.CancelledError, Exception): pass
                if gateway_ping_task: gateway_ping_task.cancel()
                await safe_close_writer(writer)
                async with grp.lock:
                    grp.peers.pop(uid_str, None)
                    if grp.leader_uid == uid_str:
                        grp.leader_uid = None
                await team_member_leave(grp, uid_str)
                grp.active["flag"] = True
    except asyncio.CancelledError:
        for m in play_matches:
            if not m.done(): m.cancel()
        if play_matches: await asyncio.gather(*play_matches, return_exceptions=True)
        play_matches.clear()
        raise

# ═══════════════════════════ INFORMATIONAL ═══════════════════════════
async def informational(addrs, starter_packet, key, iv, region="IND", max_reconnects=3, account_data=None):
    if not addrs or ":" not in str(addrs): return
    uid_str = str(account_data.get('account_id')) if account_data else ""
    reconnects = 0
    ip, port = addrs.split(":")
    while True:
        writer = None; ping_task = None
        try:
            rip = await resolve_host_cloudflare(ip)
            reader, writer = await asyncio.open_connection(rip, int(port))
            if uid_str: bot_state.register_writer(uid_str, writer)
            rs = writer.get_extra_info('socket')
            if rs: optimize_tcp_socket(rs)
            writer.write(bytes.fromhex(starter_packet)); await writer.drain()
            reconnects = 0
            try:
                ka = await send_keep_alive(region)
                if ka and not writer.is_closing():
                    writer.write(ka); await asyncio.wait_for(writer.drain(), timeout=3)
            except Exception: pass
            async def info_ka():
                ka = await send_keep_alive(region)
                while True:
                    await asyncio.sleep(5)
                    try:
                        if writer and not writer.is_closing():
                            writer.write(ka); await writer.drain()
                    except Exception: break
            ping_task = asyncio.create_task(info_ka())
            while True:
                data = await reader.read(8192)
                if not data: raise ConnectionError("closed")
        except asyncio.CancelledError:
            if ping_task: ping_task.cancel()
            if uid_str: bot_state.unregister_writer(uid_str, writer)
            await safe_close_writer(writer); raise
        except Exception:
            if ping_task: ping_task.cancel()
            if uid_str: bot_state.unregister_writer(uid_str, writer)
            await safe_close_writer(writer)
            reconnects += 1
            if reconnects > max_reconnects:
                await asyncio.sleep(3); reconnects = 0
            else: await asyncio.sleep(1)

# ═══════════════════════════ GUILD (PROTO ONLY) ═══════════════════════════
def _guild_info_to_dict(resp):
    """Convert infoClan_pb2.GuildInfoResponse → display dict."""
    if resp is None or not resp.HasField('guildInfo'):
        return None
    g = resp.guildInfo
    return {
        "GuildId":              str(g.clanId),
        "GuildName":            g.clanName or "?",
        "GuildRegion":          g.region or "?",
        "GuildLevel":           int(g.clanLevel),
        "CurrentMembers":       int(g.memberNum),
        "MaxMembers":           int(g.capacity),
        "TotalActivityPoints":  int(g.totalActivity),
        "WeeklyActivityPoints": int(g.weeklyActivity),
        "GuildSlogan":          g.slogan or "",
        "CaptainUid":           str(g.captainUid),
        "Description":          g.description or "",
        "ApprovalMethod":       int(g.approvalMethod),
        "Badge":                int(g.badge),
        "HonorPoints":          int(g.honorPoints),
        "Status":               "success",
    }


async def _parse_guild_info_bytes(content: bytes):
    """Try plain protobuf first, then AES-CBC decrypted."""
    if not _GUILD_INFO_PB_AVAILABLE:
        return None
    # 1. plain
    for off in (0, 8, 16, 32, 48, 64):
        if off >= len(content): continue
        try:
            resp = infoClan_pb2.GuildInfoResponse()
            resp.ParseFromString(content[off:])
            if resp.HasField('guildInfo') and resp.guildInfo.clanId > 0:
                return resp
        except Exception:
            pass
    # 2. AES decrypt then parse
    try:
        trunc = content[:len(content) - (len(content) % 16)]
        if not trunc: return None
        dec = AES.new(AES_KEY, AES.MODE_CBC, AES_IV).decrypt(trunc)
        if dec and 1 <= dec[-1] <= 16:
            dec = dec[:-dec[-1]]
        for off in (0, 8, 16, 32, 48, 64):
            if off >= len(dec): continue
            try:
                resp = infoClan_pb2.GuildInfoResponse()
                resp.ParseFromString(dec[off:])
                if resp.HasField('guildInfo') and resp.guildInfo.clanId > 0:
                    return resp
            except Exception:
                pass
    except Exception:
        pass
    return None


def _get_region_from_jwt(jwt_token):
    try:
        p = jwt_token.split('.')[1]; p += '=' * (-len(p) % 4)
        d = json.loads(base64.urlsafe_b64decode(p))
        return (d.get('lock_region') or d.get('noti_region') or 'IND').upper()
    except Exception: return "IND"


def _get_region_url(region):
    region = str(region).upper()
    if region == "IND": return "https://client.ind.freefiremobile.com"
    if region in ["BR", "US", "NA"]: return "https://client.us.freefiremobile.com"
    return "https://clientbp.ggpolarbear.com"


async def get_guild_info(guild_id, region: str = "IND") -> Optional[dict]:
    """Proto-based guild/clan info via /GetClanInfo."""
    if not ENABLE_GUILD_PROTO or not _GUILD_INFO_PB_AVAILABLE:
        return None
    gid = str(guild_id or "").strip()
    if not gid.isdigit(): return None
    reg = str(region or "IND").strip().upper()
    cache_key = f"{gid}:{reg}"
    cached = bot_state.guild_cache.get(cache_key)
    if cached and (time.time() - cached.get("_ts", 0)) < 15:
        return cached.get("_data")

    base_url = _get_region_url(reg)
    url = base_url.rstrip("/") + "/GetClanInfo"

    try:
        req = infoClan_pb2.GuildReq()
        req.guildId = int(gid)
        req.garena = 1
        payload = AES.new(AES_KEY, AES.MODE_CBC, AES_IV).encrypt(
            pad(req.SerializeToString(), AES.block_size))
    except Exception as e:
        print_warning(f"[GUILD-INFO] build req: {e}")
        return None

    hdrs = {
        "Content-Type":    "application/octet-stream",
        "Host":            base_url.replace("https://", "").replace("http://", "").split("/")[0],
        "X-Unity-Version": "2018.4.11f1",
        "X-GA":            "v1 1",
        "ReleaseVersion":  "OB55",
        "Connection":      "Keep-Alive",
        "Accept-Encoding": "gzip",
    }
    ctx = ssl.create_default_context()
    ctx.check_hostname = False; ctx.verify_mode = ssl.CERT_NONE

    for attempt in range(3):
        try:
            async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=15)) as s:
                async with s.post(url, headers=hdrs, data=payload, ssl=ctx) as r:
                    if r.status != 200:
                        print_warning(f"[GUILD-INFO] HTTP {r.status} attempt {attempt+1}")
                        await asyncio.sleep(1.5); continue
                    content = await r.read()
                    resp = await _parse_guild_info_bytes(content)
                    if resp is None:
                        print_warning(f"[GUILD-INFO] decode failed ({len(content)}B) attempt {attempt+1}")
                        await asyncio.sleep(1.5); continue
                    data = _guild_info_to_dict(resp)
                    if data:
                        bot_state.guild_cache[cache_key] = {"_ts": time.time(), "_data": data}
                        return data
        except Exception as e:
            print_warning(f"[GUILD-INFO] err attempt {attempt+1}: {e}")
            await asyncio.sleep(1.5)
    return None


def display_guild_info(info: dict):
    if not info: return
    try:
        box_w = 58
        line = "═" * box_w
        name = str(info.get("GuildName", "?"))
        title = f" 🏰 GUILD: {name} "
        if len(title) > box_w: title = title[:box_w-3] + "... "
        pad_n = max(0, (box_w - len(title)) // 2)
        print()
        print_colored(f"╔{line}╗", Colors.MAGENTA)
        print_colored(f"║{' '*pad_n}{title}{' '*(box_w-pad_n-len(title))}║", Colors.MAGENTA)
        print_colored(f"╠{line}╣", Colors.MAGENTA)
        def row(label, val):
            s = f"  {label:<12} {val}"
            if len(s) > box_w: s = s[:box_w-3] + "..."
            print_colored(f"║{s:<{box_w}}║", Colors.CYAN)
        row("🆔 ID", str(info.get("GuildId", "?")))
        row("🌍 Region", str(info.get("GuildRegion", "?")))
        row("⭐ Level", str(info.get("GuildLevel", "?")))
        row("👥 Members", f"{info.get('CurrentMembers',0)}/{info.get('MaxMembers',0)}")
        row("🏆 Activity", f"{info.get('TotalActivityPoints',0)} / week {info.get('WeeklyActivityPoints',0)}")
        row("📢 Slogan", str(info.get("GuildSlogan", "") or "-"))
        print_colored(f"╚{line}╝", Colors.MAGENTA)
        print()
    except Exception: pass


def _create_clan_payload(clan_id):
    if not _CLAN_PB_AVAILABLE: return None
    try:
        msg = reqClan_pb2.MyMessage(); msg.field_1 = int(clan_id)
        return AES.new(AES_KEY, AES.MODE_CBC, AES_IV).encrypt(
            pad(msg.SerializeToString(), AES.block_size))
    except Exception: return None


async def join_clan(jwt_token, clan_id):
    if not _CLAN_PB_AVAILABLE: return False
    try:
        region = _get_region_from_jwt(jwt_token)
        base_url = _get_region_url(region)
        url = base_url.rstrip("/") + "/RequestJoinClan"
        payload = _create_clan_payload(clan_id)
        if not payload: return False
        hdrs = {"Authorization": f"Bearer {jwt_token}", "X-Unity-Version": "2018.4.11f1",
                "X-GA": "v1 1", "ReleaseVersion": "OB55",
                "Content-Type": "application/octet-stream",
                "Host": base_url.replace("https://", ""),
                "Connection": "Keep-Alive", "Accept-Encoding": "gzip"}
        ctx = ssl.create_default_context()
        ctx.check_hostname = False; ctx.verify_mode = ssl.CERT_NONE
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=15)) as s:
            async with s.post(url, headers=hdrs, data=payload, ssl=ctx) as r:
                return r.status == 200
    except Exception: return False


async def join_guild_with_info(guild_id, guest_uid, guest_password,
                               region: str = "IND", token: str = None) -> bool:
    """Join clan via proto /RequestJoinClan only. No HTTP danger API."""
    gid = str(guild_id or "").strip()
    if not gid:
        return False
    info = await get_guild_info(gid, region)
    if info and GUILD_INFO_SHOW_ON_JOIN:
        display_guild_info(info)
    if token:
        try:
            joined = await join_clan(token, gid)
            if joined:
                print_success(f"[GUILD] joined clan {gid}")
                return True
            else:
                print_info(f"[GUILD] clan {gid} → already joined / rejected")
        except Exception as e:
            print_error(f"[GUILD] join_clan error: {e}")
    return False

# ═══════════════════════════ ACCOUNT HELPERS ═══════════════════════════
def _gf_field(ld, key, default=None):
    if not ld: return default
    v = ld.get(str(key), {})
    if isinstance(v, dict): return v.get("data", default)
    return v if v is not None else default

def _register_credentials(ad):
    try:
        acc_id = str(ad['account_id'])
        bot_state.account_credentials[acc_id] = ad
        if ad.get('auth_uid'): bot_state.account_credentials[str(ad['auth_uid'])] = ad
        if ad.get('auth_token'): bot_state.account_credentials[f"tok_{ad['auth_token'][:20]}"] = ad
    except Exception: pass

async def refresh_account_profile(ad_or_uid):
    try:
        if isinstance(ad_or_uid, str):
            uid = str(ad_or_uid); ad = bot_state.account_credentials.get(uid)
        else:
            ad = ad_or_uid; uid = str(ad.get('account_id')) if ad else "?"
        if not ad: return
        token = ad.get('token'); acc_id = ad.get('account_id')
        srv = ad.get('server_url'); rel = ad.get('release_version')
        if not (token and acc_id and srv and rel): return
        data = await get_player_personal_show(int(acc_id), token, srv, rel)
        if not data: return
        pd = data.get(1, {}) if isinstance(data.get(1), dict) else {}
        nickname = pd.get(3); lvl = pd.get(6); exp = pd.get(7)
        if exp is None: return
        try:
            exp = int(exp); lvl = int(lvl) if lvl else 1
        except Exception: return
        aid = str(acc_id)
        if aid not in bot_state.accounts:
            bot_state.register_account(aid, nickname or f"Player_{aid}",
                                       region=ad.get('region', 'IND'), level=lvl,
                                       exp=exp, auth_uid=ad.get('auth_uid'))
            return
        bot_state.update_exp(aid, exp, lvl)
        if nickname: bot_state.accounts[aid]["nickname"] = nickname
        _update_cache_profile(ad, lvl, exp)
        ad['level'] = lvl; ad['exp'] = exp
        if nickname: ad['nickname'] = nickname
    except Exception: pass

async def choose_region(region, jwt_token, login_url, release_version):
    region_code = region.upper()
    url = f"{login_url.rstrip('/')}/ChooseRegion"
    proto = create_proto({1: region_code})
    payload = bytes.fromhex(encrypt_aes(proto.hex()))
    hdrs = {
        "Accept-Encoding": "gzip",
        "Authorization": f"Bearer {jwt_token}",
        "Connection": "Keep-Alive",
        "Content-Type": "application/x-www-form-urlencoded",
        "ReleaseVersion": f"{release_version}",
        "User-Agent": "UnityPlayer/2018.4.12f1 (UnityWebRequest/1.0, libcurl/8.5.0-DEV)",
        "X-GA": "v1 1", "X-GA-SV": str(int(time.time())),
        "X-Unity-Version": "2018.4.12f1",
    }
    try:
        ctx = ssl.create_default_context()
        ctx.check_hostname = False; ctx.verify_mode = ssl.CERT_NONE
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=15)) as s:
            async with s.post(url, data=payload, headers=hdrs, ssl=ctx) as r:
                body = await r.read()
                print_info(f"[CHOOSE-REGION] {region} → HTTP {r.status} | {body[:80]!r}")
                return r.status
    except Exception as e:
        print_error(f"[CHOOSE-REGION] {e}"); return None

async def process_account_uid_pass(uid, password, region_override=None):
    uid = str(uid)
    cached = cache_get(uid)
    if cached:
        acc_id = str(cached['account_id'])
        bot_state.register_account(uid=acc_id,
            nickname=cached.get('nickname', f"Player_{acc_id}"),
            region=cached.get('region', 'IND'),
            level=cached.get('level', 1), exp=cached.get('exp', 0),
            likes=cached.get('likes', 0), auth_uid=uid)
        print_success(f"[CACHE] {acc_id} loaded")
        _register_credentials(cached); return cached

    print_info(f"[LOGIN] UID {uid}...")
    try:
        async with _LOGIN_SEMAPHORE:
            region = (region_override or "IND").upper()
            vc = await version_config(region)
            if not vc: return None
            release_version, client_version, server_url, gop_1, app_version = vc
            lang = REGION_LANG.get(region, "en")

            tg = await get_access_token(uid, password)
            if not tg: return None
            open_id, access_token, platform = tg

            major_payload, login_payload = await get_payload(
                access_token, open_id, platform, client_version, lang)
            res_json = await major_login(major_payload, server_url, release_version)
            if not res_json: return None

            def _gd(k):
                v = res_json.get(str(k))
                if isinstance(v, dict) and "data" in v: return v["data"]
                if k in res_json and not isinstance(res_json[k], dict): return res_json[k]
                if isinstance(v, dict): return v.get("data")
                return None

            acc_id_raw = _gd(1); region_raw = _gd(2) or region
            jwt_token = _gd(8); server_url_raw = _gd(10); server_time = _gd(21)
            aes_ak, iv_i = _extract_key_iv(res_json)
            if not jwt_token or not server_url_raw or not aes_ak: return None

            getlogin_json = await get_login_data(login_payload, jwt_token, server_url_raw, release_version)
            if not getlogin_json: return None

        func_addrs = _gf_field(getlogin_json, 14)
        info_addrs = _gf_field(getlogin_json, 32)
        if not func_addrs or not info_addrs: return None

        level = int(_gf_field(getlogin_json, 6, 1) or 1)
        exp = int(_gf_field(getlogin_json, 7, 0) or 0)
        likes = int(_gf_field(getlogin_json, 8, 0) or 0)
        nickname = _gf_field(getlogin_json, 4, f"Player_{acc_id_raw}") or f"Player_{acc_id_raw}"
        region_final = region_raw or _gf_field(getlogin_json, 3, region) or region
        acc_id = str(acc_id_raw)

        bot_state.register_account(acc_id, nickname, region_final, level, exp, likes, auth_uid=uid)
        print_success(f"[OK] {acc_id} | {nickname} | Lvl{level}")

        ad = {
            'account_id': acc_id_raw, 'nickname': nickname, 'region': region_final,
            'level': level, 'exp': exp, 'likes': likes,
            'open_id': open_id, 'access_token': access_token, 'platform': str(platform),
            'uid': uid,
            'token': jwt_token, 'server_time': server_time,
            'aes_ak': aes_ak, 'iv_i': iv_i,
            'functional_addrs': func_addrs, 'informational_addrs': info_addrs,
            'release_version': release_version, 'client_version': client_version,
            'server_url': server_url_raw, 'login_payload_data': login_payload,
            'auth_type': 'guest', 'auth_uid': uid, 'auth_password': password,
        }
        _register_credentials(ad); cache_set(uid, ad); return ad
    except Exception as e:
        print_error(f"process_account_uid_pass: {e}")
        return None

async def process_account_token(access_token, region_override=None):
    cache_key = f"tok_{access_token[:20]}"
    cached = cache_get(cache_key)
    if cached:
        acc_id = str(cached['account_id'])
        bot_state.register_account(uid=acc_id,
            nickname=cached.get('nickname', f"Player_{acc_id}"),
            region=cached.get('region', 'IND'),
            level=cached.get('level', 1), exp=cached.get('exp', 0),
            likes=cached.get('likes', 0))
        print_success(f"[CACHE] token -> {acc_id}")
        _register_credentials(cached); return cached

    print_info("[LOGIN] Token...")
    try:
        async with _LOGIN_SEMAPHORE:
            region = (region_override or "IND").upper()
            vc = await version_config(region)
            if not vc: return None
            release_version, client_version, server_url, gop_1, app_version = vc
            lang = REGION_LANG.get(region, "en")

            url = f"https://100067.connect.garena.com/oauth/token/inspect?token={access_token}"
            hdrs = {"User-Agent": "GarenaMSDK/4.0.19P4(G011A ;Android 9;en;US;)"}
            resp = await asyncio.to_thread(
                lambda: httpx.get(url, headers=hdrs, timeout=10, verify=False))
            d = resp.json()
            if 'error' in d: return None
            open_id = d.get('open_id'); platform = d.get('platform', 4)
            if not open_id: return None

            major_payload, login_payload = await get_payload(
                access_token, open_id, str(platform), client_version, lang)
            res_json = await major_login(major_payload, server_url, release_version)
            if not res_json: return None

            def _gd(k):
                v = res_json.get(str(k))
                if isinstance(v, dict) and "data" in v: return v["data"]
                if k in res_json and not isinstance(res_json[k], dict): return res_json[k]
                if isinstance(v, dict): return v.get("data")
                return None

            acc_id_raw = _gd(1); region_raw = _gd(2) or region
            jwt_token = _gd(8); server_url_raw = _gd(10); server_time = _gd(21)
            aes_ak, iv_i = _extract_key_iv(res_json)
            if not jwt_token or not server_url_raw or not aes_ak: return None

            getlogin_json = await get_login_data(login_payload, jwt_token, server_url_raw, release_version)
            if not getlogin_json: return None

        func_addrs = _gf_field(getlogin_json, 14)
        info_addrs = _gf_field(getlogin_json, 32)
        if not func_addrs or not info_addrs: return None

        level = int(_gf_field(getlogin_json, 6, 1) or 1)
        exp = int(_gf_field(getlogin_json, 7, 0) or 0)
        likes = int(_gf_field(getlogin_json, 8, 0) or 0)
        nickname = _gf_field(getlogin_json, 4, f"Player_{acc_id_raw}") or f"Player_{acc_id_raw}"
        region_final = region_raw or _gf_field(getlogin_json, 3, region) or region
        acc_id = str(acc_id_raw)

        bot_state.register_account(acc_id, nickname, region_final, level, exp, likes)
        print_success(f"[OK] token {acc_id} | {nickname} | Lvl{level}")

        ad = {
            'account_id': acc_id_raw, 'nickname': nickname, 'region': region_final,
            'level': level, 'exp': exp, 'likes': likes,
            'open_id': open_id, 'access_token': access_token, 'platform': str(platform),
            'uid': open_id,
            'token': jwt_token, 'server_time': server_time,
            'aes_ak': aes_ak, 'iv_i': iv_i,
            'functional_addrs': func_addrs, 'informational_addrs': info_addrs,
            'release_version': release_version, 'client_version': client_version,
            'server_url': server_url_raw, 'login_payload_data': login_payload,
            'auth_type': 'token', 'auth_token': access_token,
        }
        _register_credentials(ad); cache_set(cache_key, ad); return ad
    except Exception as e:
        print_error(f"process_account_token: {e}")
        return None

async def run_account_worker(ad, label, grp: TeamGroup,
                             region_override=None, clan_override=None):
    acc_id = str(ad['account_id'])
    info_task = None; exp_task = None; ping_task = None
    try:
        reg = (region_override or ad.get('region') or 'IND').upper()
        tcp_online = await build_tcp_startup_packet(
            ad['account_id'], ad['token'], ad['server_time'],
            ad['aes_ak'], ad['iv_i'], region=reg, typ='OnLine')
        tcp_chat = await build_tcp_startup_packet(
            ad['account_id'], ad['token'], ad['server_time'],
            ad['aes_ak'], ad['iv_i'], region=reg, typ='ChaT')

        if clan_override:
            try:
                await asyncio.sleep(1.0)
                await join_guild_with_info(
                    clan_override, ad.get('auth_uid'), ad.get('auth_password'),
                    region=reg, token=ad.get('token'))
            except Exception as e:
                print_error(f"[GUILD] join error: {e}")

        info_task = asyncio.create_task(informational(
            ad.get('informational_addrs'), tcp_chat, ad['aes_ak'], ad['iv_i'],
            region=reg, account_data=ad))

        async def exp_refresher():
            try:
                f = bot_state.account_credentials.get(acc_id)
                if f: await refresh_account_profile(f)
            except Exception: pass
            while True:
                await asyncio.sleep(EXP_REFRESH_INTERVAL + random.uniform(-3.0, 3.0))
                try:
                    f = bot_state.account_credentials.get(acc_id)
                    if f: await refresh_account_profile(f)
                except Exception: pass
        exp_task = asyncio.create_task(exp_refresher())

        if ENABLE_HTTP_PING:
            try:
                _phost = str(ad.get("server_url") or PING_URL).rstrip("/")
                _purl = _phost if _phost.endswith("/Ping") else (_phost + "/Ping")
                ping_task = asyncio.create_task(ping_worker(
                    acc_id, ad["token"], ad["release_version"], region=reg, ping_url=_purl))
                print_success(f"[PING] started {acc_id}")
            except Exception: pass

        while True:
            try:
                await functional_battle_royale(
                    ad.get('functional_addrs'), tcp_online, reg, ad['client_version'],
                    ad['aes_ak'], ad['iv_i'], account_id=acc_id, account_data=ad,
                    account_level=int(ad.get('level', 2) or 2), grp=grp)
            except asyncio.CancelledError:
                raise
            except Exception as e:
                print_error(f"[RETRY] {label}: {e}")
            print_warning(f"[RETRY] {label} session ended, restart {SESSION_RETRY_DELAY}s")
            try: bot_state.update_status(acc_id, "RECONNECTING")
            except Exception: pass
            await asyncio.sleep(SESSION_RETRY_DELAY)
    except asyncio.CancelledError: raise
    except Exception as e: print_error(f"run_account_worker {label}: {e}")
    finally:
        for t in (info_task, exp_task, ping_task):
            if t and not t.done(): t.cancel()
        for t in (info_task, exp_task, ping_task):
            if t:
                try: await t
                except Exception: pass

async def account_loop_guest(uid, password, grp: TeamGroup,
                             region_override=None, clan_override=None):
    uid = str(uid)
    acc_id = None
    while True:
        try:
            try: bot_state.update_status(uid, "CONNECTING")
            except Exception: pass
            ad = await process_account_uid_pass(uid, password, region_override)
            if not ad:
                try: bot_state.update_status(uid, "ERROR")
                except Exception: pass
                await asyncio.sleep(15); continue
            acc_id = str(ad['account_id'])
            bot_state.auth_to_game_id[uid] = acc_id
            bot_state.game_to_auth_id[acc_id] = uid
            await run_account_worker(ad, uid, grp, region_override, clan_override)
            await asyncio.sleep(3)
        except asyncio.CancelledError:
            try:
                bot_state.update_status(uid, "OFFLINE")
                if acc_id: bot_state.update_status(acc_id, "OFFLINE")
            except Exception: pass
            break
        except Exception as e:
            print_error(f"Error {uid}: {e}, retry 10s")
            await asyncio.sleep(10)

async def account_loop_token(token, grp: TeamGroup,
                             region_override=None, clan_override=None):
    label = token[:10]
    while True:
        try:
            ad = await process_account_token(token, region_override)
            if not ad:
                await asyncio.sleep(15); continue
            await run_account_worker(ad, label, grp, region_override, clan_override)
            await asyncio.sleep(3)
        except asyncio.CancelledError: break
        except Exception as e:
            print_error(f"Token error: {e}, retry 10s")
            await asyncio.sleep(10)

# ═══════════════════════════ CREATE ACCOUNTS ═══════════════════════════
async def create_four_accounts(region: str, clan_id: str, count: int = 4, password: str = "SINGH"):
    bot_state.creating = True
    bot_state.create_progress = []

    def _prog(s):
        try:
            print(f"[CREATE] {s}"); bot_state.log(s, "info")
        except Exception: pass
        bot_state.create_progress.append(s)

    if clan_id and ENABLE_GUILD_PROTO:
        _prog(f"⌛ Guild info {clan_id}...")
        try:
            info = await get_guild_info(clan_id, region)
            if info:
                display_guild_info(info)
                _prog(f"✅ Guild: {info.get('GuildName')} | Lvl {info.get('GuildLevel')}")
        except Exception as e:
            _prog(f"⚠️ guild info: {e}")

    try:
        _prog(f"⌛ version config {region}...")
        vc = await version_config(region)
        if not vc:
            _prog("❌ version config failed"); return []
        release_v, remote_v, login_url, gop_1, app_version = vc
        if not login_url.endswith("/"): login_url += "/"
        lang = REGION_LANG.get(region.upper(), "en")
        game_version = remote_v or app_version
        _prog(f"✅ Version OK | rel={release_v} | game={game_version}")

        created = []
        for i in range(count):
            _prog(f"⌛ Creating bot {i+1}/{count}...")
            try:
                if i > 0:
                    _prog("   → wait 5s (rate limit)")
                    await asyncio.sleep(5.0)

                uid = None
                for ra in range(5):
                    uid = await register_account(password, gop_1, app_version)
                    if uid: break
                    _prog(f"   → register retry {ra+1}/5")
                    await asyncio.sleep(5.0)
                if not uid:
                    _prog(f"❌ bot {i+1}: register failed"); continue
                _prog(f"   → UID {uid}")
                await asyncio.sleep(2.0)

                tok = await grant_token(uid, password, gop_1, app_version)
                if not tok:
                    _prog(f"❌ bot {i+1}: grant failed"); continue
                open_id = tok["open_id"]; access_token = tok["access_token"]
                platform = tok.get("platform", 4)

                major_payload, login_payload = await get_payload(
                    access_token, open_id, platform, game_version, lang)
                if not major_payload:
                    _prog(f"❌ bot {i+1}: payload failed"); continue

                nickname_final = generate_bot_name()
                mr = await major_register(release_v, access_token, open_id,
                                          nickname_final, game_version, login_url, lang)
                if not mr:
                    _prog(f"❌ bot {i+1}: MajorRegister failed"); continue

                def _mrg(k, d=None):
                    v = mr.get(str(k))
                    if isinstance(v, dict) and "data" in v: return v["data"]
                    return v if v is not None else d
                mr_acc_id = _mrg(3)
                _prog(f"   → Register OK name={nickname_final} acc={mr_acc_id}")
                await asyncio.sleep(3.0)

                res_json = None
                for attempt in range(3):
                    mp, lp = await get_payload(access_token, open_id, platform, game_version, lang)
                    _prog(f"   → MajorLogin #{attempt+1}/3")
                    res_json = await major_login(mp, login_url, release_v)
                    if res_json and (("8" in res_json) or (8 in res_json)):
                        major_payload = mp; login_payload = lp; break
                    res_json = None
                    await asyncio.sleep(2.0)
                if not res_json:
                    _prog(f"❌ bot {i+1}: MajorLogin failed"); continue

                def _gd(k):
                    v = res_json.get(str(k))
                    if isinstance(v, dict) and "data" in v: return v["data"]
                    if k in res_json and not isinstance(res_json[k], dict): return res_json[k]
                    if isinstance(v, dict): return v.get("data")
                    return None

                jwt_token = _gd(8); server_url_raw = _gd(10)
                server_time = _gd(21); acc_id_raw = _gd(1)
                if not jwt_token:
                    _prog(f"❌ bot {i+1}: no JWT"); continue

                if not server_url_raw:
                    _prog(f"   → ChooseRegion({region})")
                    cr_status = await choose_region(region, jwt_token, login_url, release_v)
                    if cr_status != 200:
                        _prog(f"❌ bot {i+1}: ChooseRegion {cr_status}"); continue
                    await asyncio.sleep(2.0)
                    res_json2 = None
                    for attempt in range(3):
                        mp2, lp2 = await get_payload(access_token, open_id, platform, game_version, lang)
                        _prog(f"   → MajorLogin#2 {attempt+1}/3")
                        res_json2 = await major_login(mp2, login_url, release_v)
                        if res_json2 and (("10" in res_json2) or (10 in res_json2)):
                            res_json = res_json2; login_payload = lp2; break
                        res_json2 = None
                        await asyncio.sleep(2.0)
                    if not res_json2:
                        _prog(f"❌ bot {i+1}: no server_url"); continue
                    res_json = res_json2

                    def _gd2(k):
                        v = res_json.get(str(k))
                        if isinstance(v, dict) and "data" in v: return v["data"]
                        if k in res_json and not isinstance(res_json[k], dict): return res_json[k]
                        if isinstance(v, dict): return v.get("data")
                        return None
                    jwt_token = _gd2(8); server_url_raw = _gd2(10)
                    server_time = _gd2(21); acc_id_raw = _gd2(1)
                    if not server_url_raw:
                        _prog(f"❌ bot {i+1}: no server_url"); continue

                _prog(f"   ✅ server_url {server_url_raw}")

                aes_ak, iv_i = _extract_key_iv(res_json)
                if not aes_ak or not iv_i:
                    _prog(f"❌ bot {i+1}: AES fail"); continue

                ld = None; func_addrs = None; info_addrs = None
                for attempt in range(5):
                    if attempt > 0:
                        await asyncio.sleep(3.0)
                        _prog("   → refresh session...")
                        mp, lp = await get_payload(access_token, open_id, platform, game_version, lang)
                        res_json = await major_login(mp, login_url, release_v)
                        if res_json:
                            def _gdr(k):
                                v = res_json.get(str(k))
                                if isinstance(v, dict) and "data" in v: return v["data"]
                                if k in res_json and not isinstance(res_json[k], dict): return res_json[k]
                                if isinstance(v, dict): return v.get("data")
                                return None
                            jwt_token = _gdr(8); server_url_raw = _gdr(10)
                            login_payload = lp
                    ld = await get_login_data(login_payload, jwt_token, server_url_raw, release_v)
                    if ld:
                        func_addrs = _gf_field(ld, 14); info_addrs = _gf_field(ld, 32)
                        if func_addrs and info_addrs: break
                    _prog(f"   → TCP addrs missing {attempt+1}/5")

                if not func_addrs or not info_addrs:
                    _prog(f"❌ bot {i+1}: no TCP addrs"); continue

                level = 1; exp = 0; likes = 0
                if ld:
                    level = int(_gf_field(ld, 6, 1) or 1)
                    exp = int(_gf_field(ld, 7, 0) or 0)
                    likes = int(_gf_field(ld, 8, 0) or 0)
                    nickname_final = _gf_field(ld, 4, nickname_final) or nickname_final

                ad = {
                    'account_id': acc_id_raw, 'nickname': nickname_final,
                    'region': region, 'level': level, 'exp': exp, 'likes': likes,
                    'open_id': open_id, 'access_token': access_token,
                    'platform': str(platform), 'uid': uid,
                    'token': jwt_token, 'server_time': server_time,
                    'aes_ak': aes_ak, 'iv_i': iv_i,
                    'functional_addrs': func_addrs,
                    'informational_addrs': info_addrs,
                    'release_version': release_v, 'client_version': game_version,
                    'server_url': server_url_raw, 'login_payload_data': login_payload,
                    'auth_type': 'guest', 'auth_uid': uid, 'auth_password': password,
                }
                _register_credentials(ad); cache_set(uid, ad); created.append(ad)
                _prog(f"✅ bot {i+1}: {nickname_final} | UID {acc_id_raw} | Lvl {level}")
                await asyncio.sleep(0.6)
            except Exception as e:
                _prog(f"❌ bot {i+1}: {e}")
                traceback.print_exc()

        if not created:
            _prog("❌ No accounts created."); return []

        try:
            existing = []
            if os.path.exists(ACCOUNTS_FILE):
                try:
                    with open(ACCOUNTS_FILE, "r", encoding="utf-8") as f:
                        existing = json.load(f) or []
                        if not isinstance(existing, list): existing = []
                except Exception: existing = []
            known = {str(a.get("uid")) for a in existing if isinstance(a, dict)}
            for a in created:
                u = str(a['auth_uid'])
                if u not in known:
                    existing.append({"uid": u, "password": a['auth_password'],
                                     "region": region, "clan_id": clan_id})
            with open(ACCOUNTS_FILE, "w", encoding="utf-8") as f:
                json.dump(existing, f, indent=2)
            _prog(f"📦 {len(created)} accounts saved")
        except Exception as e:
            _prog(f"⚠️ save: {e}")

        _prog(f"🚀 Starting {len(created)} workers...")
        for i, a in enumerate(created):
            grp = _next_group()
            task = asyncio.create_task(account_loop_guest(
                str(a['auth_uid']), a['auth_password'], grp,
                region_override=region, clan_override=clan_id))
            bot_state.account_workers[str(a['auth_uid'])] = task
            _prog(f"   → worker {i+1}/{len(created)}")
            await asyncio.sleep(0.35)

        _prog(f"✅ {len(created)} bots launched.")
        return created
    except Exception as e:
        _prog(f"❌ create error: {e}")
        traceback.print_exc(); return []
    finally:
        bot_state.creating = False

# ═══════════════════════════ LOAD / GROUPS ═══════════════════════════
def load_accounts():
    accounts = []
    if os.path.exists(ACCOUNTS_FILE):
        try:
            with open(ACCOUNTS_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
                if isinstance(data, list): accounts = [a for a in data if isinstance(a, dict)]
        except Exception as e: print_error(f"load: {e}")
    if not accounts and FALLBACK_UID and FALLBACK_PASSWORD:
        accounts.append({"uid": FALLBACK_UID, "password": FALLBACK_PASSWORD})
    return accounts

def make_squad_groups(accounts: List[dict]) -> List[Tuple[TeamGroup, List[dict]]]:
    groups = []
    for gi, i in enumerate(range(0, len(accounts), TEAM_SIZE)):
        chunk = accounts[i:i + TEAM_SIZE]
        grp = TeamGroup(gi, size=len(chunk))
        _ACTIVE_GROUPS[gi] = grp
        groups.append((grp, chunk))
    return groups

_group_counter = {"n": 0}

def _next_group() -> TeamGroup:
    g = TeamGroup(_group_counter["n"], TEAM_SIZE)
    _ACTIVE_GROUPS[_group_counter["n"]] = g
    _group_counter["n"] += 1
    return g

_STARTED_KEYS: set = set()
_START_LOCK = asyncio.Lock()

async def spawn_worker_unique(key: str, coro):
    async with _START_LOCK:
        existing = bot_state.account_workers.get(key)
        if existing and not existing.done():
            print_warning(f"[SKIP] Worker running {key}")
            return existing
        _STARTED_KEYS.add(key)
        task = asyncio.create_task(coro)
        bot_state.account_workers[key] = task
        print_info(f"[START] Worker {key}")
        return task

# ═══════════════════════════ DASHBOARD ═══════════════════════════
async def _start_dashboard():
    try:
        await start_web_dashboard(
            WEB_HOST, WEB_PORT, bot_state, _ACTIVE_GROUPS,
            create_accounts_func=create_four_accounts,
            fetch_info_func=get_guild_info,
            join_guild_func=join_guild_with_info,
        )
    except TypeError:
        try:
            await start_web_dashboard(host=WEB_HOST, port=WEB_PORT)
        except Exception as e:
            print_error(f"Dashboard: {e}")
            return
    except Exception as e:
        print_error(f"Dashboard: {e}")
        return
    print_success(f"Dashboard: http://localhost:{WEB_PORT}")

# ═══════════════════════════ AUTOLOAD ═══════════════════════════
async def _autoload_accounts():
    accounts = load_accounts()
    if not accounts:
        print_warning(f"No accounts in {ACCOUNTS_FILE}. Add via dashboard.")
        return

    if GUILD_INFO_SHOW_ON_BOOT:
        seen = set()
        for a in accounts:
            gid = str(a.get("clan_id", "")).strip()
            reg = str(a.get("region", "IND")).strip() or "IND"
            if not gid or gid in seen: continue
            seen.add(gid)
            try:
                info = await get_guild_info(gid, reg)
                if info: display_guild_info(info)
            except Exception as e:
                print_warning(f"[BOOT] guild info {gid}: {e}")

    squads = make_squad_groups(accounts)
    _group_counter["n"] = len(squads)
    print_success(f"[BOOT] {len(accounts)} account(s) -> {len(squads)} squad(s)")

    for grp, chunk in squads:
        print_success(f"[SQUAD-{grp.tag()}] {len(chunk)} accounts")
        for acc in chunk:
            region = str(acc.get("region", "")).strip() or None
            clan = str(acc.get("clan_id", "")).strip() or CLAN_ID_DEFAULT
            if acc.get("token"):
                t = str(acc["token"]).strip()
                await spawn_worker_unique(t[:10], account_loop_token(t, grp, region, clan))
            elif acc.get("uid") and acc.get("password"):
                u = str(acc["uid"]).strip()
                await spawn_worker_unique(u, account_loop_guest(u, acc["password"], grp, region, clan))
            await asyncio.sleep(0.4)

# ═══════════════════════════ MAIN ═══════════════════════════
async def main():
    print_colored("=" * 62, Colors.CYAN)
    print_colored("  NG RAXX v6.1 — Squad Bot (BG + CHASE + GUILD-PROTO + CREATE)", Colors.GREEN)
    print_colored("=" * 62, Colors.CYAN)
    print_info("Mode: BATTLE ROYALE ONLY | always in game")
    print_success(f"[MOVE] {MOVEMENT_PATTERN} pattern | chase on cmd 2014")
    print_success(f"[BG] match start hote hi background | cap={MAX_BG_MATCHES} restart={BG_RESTART_DELAY}s")
    print_success(f"[FIX] Handshake {HANDSHAKE_TIMEOUT}s | Idle {MATCH_IDLE_TIMEOUT}s | Retry {SESSION_RETRY_DELAY}s")
    print_success(f"[SQUAD] {TEAM_SIZE}-{TEAM_SIZE} groups, auto requeue")
    print_success("[AUTH] MajorLogin -> _extract_key_iv -> GetLoginData | refresh via GetPlayerPersonalShow")
    print_success("[GUILD] proto-only: /GetClanInfo + /RequestJoinClan (no HTTP danger API)")
    print_colored("=" * 62, Colors.CYAN)

    await _start_dashboard()

    async def on_account_added(data):
        grp = _next_group()
        region = str(data.get("region", "")).strip() or None
        clan = str(data.get("clan_id", "")).strip() or CLAN_ID_DEFAULT
        if data.get("token"):
            t = str(data["token"]).strip()
            await spawn_worker_unique(t[:10], account_loop_token(t, grp, region, clan))
        elif data.get("uid") and data.get("password"):
            u = str(data["uid"]).strip()
            await spawn_worker_unique(u, account_loop_guest(u, data["password"], grp, region, clan))

    async def on_refresh_account(uid):
        await refresh_account_profile(uid)

    try:
        bot_state.refresh_callbacks["on_account_added"] = on_account_added
        bot_state.refresh_callbacks["on_refresh_account"] = on_refresh_account
    except Exception: pass

    try:
        await _autoload_accounts()
    except Exception as e:
        print_error(f"[BOOT] autoload: {e}")

    try:
        while True: await asyncio.sleep(1)
    except (KeyboardInterrupt, asyncio.CancelledError):
        print_warning("Shutting down...")
        for t in list(bot_state.account_workers.values()): t.cancel()
        await asyncio.gather(*bot_state.account_workers.values(), return_exceptions=True)
        try: await client.aclose()
        except Exception: pass
        print_success("Closed.")

if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        print_warning("stopped")