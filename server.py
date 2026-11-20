"""BSCS online server - accounts, leaderboards, friends, lobbies, clubs, trades and an admin panel.

Pure Python standard library (plus the optional `pg8000` package when DATABASE_URL is set).

Run locally:
    python server.py               -> listens on http://0.0.0.0:8000

Environment variables:
    PORT          port to listen on (cloud hosts set this for you)          default 8000
    ADMIN_CODE    the secret code that unlocks the admin panel               default 1111
    DATABASE_URL  postgres://user:pass@host/db  -> store data in Postgres    (optional)
    DATA_FILE     JSON file used when DATABASE_URL is not set                default server_data.json
"""

import hashlib
import hmac
import json
import os
import re
import secrets
import socket
import ssl
import string
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, unquote, urlparse

PORT = int(os.environ.get("PORT", "8000"))
ADMIN_CODE = os.environ.get("ADMIN_CODE", "1111")
DATABASE_URL = os.environ.get("DATABASE_URL", "").strip()
DATA_FILE = os.environ.get("DATA_FILE") or os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                                        "server_data.json")

RESOURCES = ("coins", "gems", "bling", "power_points", "credits")
TAKEABLE = RESOURCES + ("trophies",)
GIFT_KINDS = RESOURCES + ("experience", "trophies", "tokens")
DROP_KINDS = ("Starr Drop", "Box", "Chaos Drop", "Insane Drop", "Megapig")
UNTRADABLE_BRAWLERS = {"Shelly"}
UNTRADABLE_SKINS = {"Default"}
NICK_RE = re.compile(r"^[A-Za-z0-9_]{3,16}$")
ONLINE_SECS = 20          # "online" if synced within this many seconds
LOBBY_TIMEOUT = 30        # lobby members who stop syncing are removed
MAX_LOBBY = 8
MAX_FRIENDS = 100
MAX_PENDING_TRADES = 10
TRADE_EXPIRE = 24 * 3600
GROUP_DROP_COOLDOWN = 15
MAX_CLUB = 30
MEGAPIG_TIERS = (100, 250, 500, 900, 1500)  # pig points needed for 1..5 Megapigs each
MAX_PIG_POINTS_PER_SYNC = 500


class ApiError(Exception):
    def __init__(self, status, message, **extra):
        super().__init__(message)
        self.status = status
        self.message = message
        self.extra = extra


# ---------------------------------------------------------------------------
# STORAGE
# ---------------------------------------------------------------------------

class FileStore:
    def __init__(self, path):
        self.path = path

    def load(self):
        try:
            with open(self.path, encoding="utf8") as f:
                return json.load(f)
        except (OSError, ValueError):
            return None

    def save(self, text):
        tmp = self.path + ".tmp"
        with open(tmp, "w", encoding="utf8") as f:
            f.write(text)
        os.replace(tmp, self.path)

    def describe(self):
        return f"file {self.path}"


class PgStore:
    """Keeps the whole database as one JSON row - plenty for a game among friends."""

    def __init__(self, url):
        import pg8000.native  # only needed when DATABASE_URL is set
        self.pg = pg8000.native
        u = urlparse(url)
        self.args = dict(user=unquote(u.username or ""), password=unquote(u.password or ""),
                         host=u.hostname, port=u.port or 5432, database=(u.path or "/postgres")[1:])
        query = parse_qs(u.query)
        if query.get("sslmode", ["require"])[0] != "disable":
            self.args["ssl_context"] = ssl.create_default_context()
        self.conn = None

    def _connect(self):
        if self.conn is None:
            self.conn = self.pg.Connection(**self.args)
            self.conn.run("CREATE TABLE IF NOT EXISTS bscs_store (id INT PRIMARY KEY, data TEXT NOT NULL)")
        return self.conn

    def _run(self, sql, **params):
        for attempt in range(2):
            try:
                return self._connect().run(sql, **params)
            except Exception:
                self.conn = None
                if attempt:
                    raise

    def load(self):
        rows = self._run("SELECT data FROM bscs_store WHERE id = 1")
        return json.loads(rows[0][0]) if rows else None

    def save(self, text):
        self._run("INSERT INTO bscs_store (id, data) VALUES (1, :d) "
                  "ON CONFLICT (id) DO UPDATE SET data = EXCLUDED.data", d=text)

    def describe(self):
        return f"postgres {self.args['host']}/{self.args['database']}"


store = PgStore(DATABASE_URL) if DATABASE_URL else FileStore(DATA_FILE)

lock = threading.RLock()
db = {"players": {}, "trades": {}, "clubs": {}, "announcement": {"id": 0, "text": "", "t": 0}, "next_id": 1}
tokens = {}        # token -> player id
lobbies = {}       # code -> lobby (kept in memory only)
player_lobby = {}  # player id -> lobby code
admin_fails = {}   # player id -> [timestamps]
chat_last = {}     # player id -> time of last chat message
dirty = False


def mark_dirty():
    global dirty
    dirty = True


def load_db():
    data = store.load()
    if isinstance(data, dict) and isinstance(data.get("players"), dict):
        db.update(data)
    db.setdefault("clubs", {})
    for pid, p in db["players"].items():
        for t in p.get("tokens", []):
            tokens[t] = pid


def saver_loop():
    global dirty
    while True:
        time.sleep(2)
        with lock:
            if not dirty:
                continue
            text = json.dumps(db, separators=(",", ":"))
            dirty = False
        try:
            store.save(text)
        except Exception as e:  # keep running; retry on the next change
            print("SAVE FAILED:", e)
            mark_dirty()


# ---------------------------------------------------------------------------
# HELPERS
# ---------------------------------------------------------------------------

def now():
    return time.time()


def new_id(prefix):
    i = db["next_id"]
    db["next_id"] = i + 1
    return f"{prefix}{i}"


def hash_pw(password, salt):
    return hashlib.pbkdf2_hmac("sha256", password.encode("utf8"), bytes.fromhex(salt), 100_000).hex()


def find_by_nick(nick):
    low = str(nick or "").strip().lower()
    for p in db["players"].values():
        if p["nick_lower"] == low:
            return p
    return None


def get_player(pid):
    p = db["players"].get(str(pid))
    if not p:
        raise ApiError(404, "Player not found.")
    return p


def check_nick(nick):
    nick = str(nick or "").strip()
    if not NICK_RE.match(nick):
        raise ApiError(400, "Nickname must be 3-16 letters, numbers or _.")
    if find_by_nick(nick):
        raise ApiError(409, "That nickname is taken.")
    return nick


def is_online(p):
    return now() - p.get("last_seen", 0) < ONLINE_SECS


def auth(body):
    pid = tokens.get(str(body.get("token") or ""))
    if not pid or pid not in db["players"]:
        raise ApiError(401, "Please log in again.")
    p = db["players"][pid]
    if p.get("banned"):
        raise ApiError(403, "This account is banned.", banned=True)
    p["last_seen"] = now()
    return p


def require_admin(p):
    if not p.get("admin"):
        raise ApiError(403, "Admins only.")


def as_int(v, lo=0, hi=10 ** 9):
    try:
        return max(lo, min(hi, int(v)))
    except (TypeError, ValueError):
        return lo


def clean_str(v, n=40):
    return str(v or "")[:n]


def clean_names(v, n=300):
    out = []
    if isinstance(v, list):
        for x in v[:n]:
            s = clean_str(x, 60)
            if s and s not in out:
                out.append(s)
    return out


def clean_profile(d):
    d = d if isinstance(d, dict) else {}
    return {
        "trophies": as_int(d.get("trophies")),
        "highest_trophies": as_int(d.get("highest_trophies")),
        "brawlers": as_int(d.get("brawlers")),
        "skins": as_int(d.get("skins")),
        "power": as_int(d.get("power")),
        "level": as_int(d.get("level")),
        "rebirths": as_int(d.get("rebirths"), 0, 10 ** 6),
        "brawler": clean_str(d.get("brawler")) or "Shelly",
        "skin": clean_str(d.get("skin"), 60) or "Default",
        "icon": clean_str(d.get("icon")),
        "sandbox": bool(d.get("sandbox")),
    }


def clean_inv(d):
    d = d if isinstance(d, dict) else {}
    res = d.get("resources") if isinstance(d.get("resources"), dict) else {}
    return {"resources": {k: as_int(res.get(k)) for k in RESOURCES},
            "brawlers": clean_names(d.get("brawlers")), "skins": clean_names(d.get("skins"))}


def clean_bundle(d):
    d = d if isinstance(d, dict) else {}
    res = d.get("resources") if isinstance(d.get("resources"), dict) else {}
    return {"resources": {k: as_int(res.get(k)) for k in RESOURCES if as_int(res.get(k)) > 0},
            "brawlers": clean_names(d.get("brawlers"), 20), "skins": clean_names(d.get("skins"), 20)}


def bundle_empty(b):
    return not (b["resources"] or b["brawlers"] or b["skins"])


def check_can_give(p, b):
    inv = p.get("inv") or clean_inv({})
    for k, v in b["resources"].items():
        if inv["resources"].get(k, 0) < v:
            raise ApiError(400, f"{p['nickname']} doesn't have {v} {k.replace('_', ' ')}.")
    for name in b["brawlers"]:
        if name in UNTRADABLE_BRAWLERS:
            raise ApiError(400, f"{name} can't be traded.")
        if name not in inv["brawlers"]:
            raise ApiError(400, f"{p['nickname']} doesn't own {name}.")
    for name in b["skins"]:
        if name in UNTRADABLE_SKINS:
            raise ApiError(400, f"{name} can't be traded.")
        if name not in inv["skins"]:
            raise ApiError(400, f"{p['nickname']} doesn't own {name}.")


def check_can_receive(p, b):
    inv = p.get("inv") or clean_inv({})
    for name in b["brawlers"]:
        if name in inv["brawlers"]:
            raise ApiError(400, f"{p['nickname']} already has {name}.")
    for name in b["skins"]:
        if name in inv["skins"]:
            raise ApiError(400, f"{p['nickname']} already has {name}.")


def inv_move(p, remove, add):
    inv = p.setdefault("inv", clean_inv({}))
    for k, v in remove["resources"].items():
        inv["resources"][k] = max(0, inv["resources"].get(k, 0) - v)
    for k, v in add["resources"].items():
        inv["resources"][k] = inv["resources"].get(k, 0) + v
    inv["brawlers"] = [b for b in inv["brawlers"] if b not in remove["brawlers"]] + add["brawlers"]
    inv["skins"] = [s for s in inv["skins"] if s not in remove["skins"]] + add["skins"]


def deliver(p, op, **data):
    item = {"id": new_id("d"), "op": op, "t": now()}
    item.update(data)
    p.setdefault("deliveries", []).append(item)
    mark_dirty()


def clean_reward(r):
    """A reward as the game understands it: [kind, value] or ["drop", name, count] etc."""
    if not isinstance(r, list) or not r:
        raise ApiError(400, "Bad reward.")
    kind = clean_str(r[0], 20)
    if kind in GIFT_KINDS:
        return [kind, as_int(r[1] if len(r) > 1 else 0, 0, 10 ** 8)]
    if kind == "drop":
        name = clean_str(r[1] if len(r) > 1 else "")
        if name not in DROP_KINDS:
            raise ApiError(400, "Bad drop.")
        return ["drop", name, as_int(r[2] if len(r) > 2 else 1, 1, 1000)]
    if kind == "brawler":
        return ["brawler", clean_str(r[1] if len(r) > 1 else "", 60), clean_str(r[2] if len(r) > 2 else "Rare")]
    if kind in ("skin", "pin", "spray", "player_icon", "hypercharge"):
        return [kind, clean_str(r[1] if len(r) > 1 else "", 60)]
    raise ApiError(400, "Bad reward.")


def same_lobby(a, b):
    code = player_lobby.get(a["id"])
    return bool(code) and code == player_lobby.get(b["id"])


def can_interact(a, b):
    return b["id"] in a.get("friends", []) or same_lobby(a, b)


# --- lobbies ---------------------------------------------------------------

def lobby_code():
    alphabet = string.ascii_uppercase + string.digits
    while True:
        code = "".join(secrets.choice(alphabet) for _ in range(5))
        if code not in lobbies:
            return code


def lobby_system_msg(lobby, msg):
    lobby["chat"].append({"from": "", "text": msg, "t": now(), "sys": True})
    del lobby["chat"][:-50]


def leave_lobby(pid, reason="left"):
    code = player_lobby.pop(pid, None)
    lobby = lobbies.get(code)
    if not lobby:
        return
    lobby["members"].pop(pid, None)
    p = db["players"].get(pid)
    if p:
        lobby_system_msg(lobby, f"{p['nickname']} {reason}.")
    if not lobby["members"]:
        lobbies.pop(code, None)
    elif lobby["host"] == pid:
        lobby["host"] = next(iter(lobby["members"]))
        lobby_system_msg(lobby, f"{db['players'][lobby['host']]['nickname']} is now the host.")


def close_lobby(code, reason):
    lobby = lobbies.pop(code, None)
    if not lobby:
        return
    for pid in list(lobby["members"]):
        player_lobby.pop(pid, None)
        p = db["players"].get(pid)
        if p:
            deliver(p, "message", text=reason)


def cleanup():
    t = now()
    for code, lobby in list(lobbies.items()):
        for pid, seen in list(lobby["members"].items()):
            if t - seen > LOBBY_TIMEOUT:
                leave_lobby(pid, "disconnected")
    for tid, tr in list(db["trades"].items()):
        if t - tr["created"] > TRADE_EXPIRE:
            del db["trades"][tid]
            mark_dirty()


def lobby_view(lobby, viewer=None):
    members = []
    for pid in lobby["members"]:
        p = db["players"].get(pid)
        if not p:
            continue
        prof = p.get("profile") or clean_profile({})
        members.append({"id": pid, "nickname": p["nickname"], "trophies": prof["trophies"],
                        "brawler": prof["brawler"], "skin": prof["skin"], "host": pid == lobby["host"]})
    return {"code": lobby["code"], "name": lobby["name"], "public": lobby["public"], "host": lobby["host"],
            "members": members, "chat": lobby["chat"][-40:]}


def player_summary(p):
    prof = p.get("profile") or clean_profile({})
    return {"id": p["id"], "nickname": p["nickname"], "trophies": prof["trophies"], "online": is_online(p),
            "brawler": prof["brawler"], "skin": prof["skin"]}


def trade_view(tr):
    a = db["players"].get(tr["from"])
    b = db["players"].get(tr["to"])
    return {"id": tr["id"], "from": tr["from"], "to": tr["to"],
            "from_name": a["nickname"] if a else "?", "to_name": b["nickname"] if b else "?",
            "give": tr["give"], "want": tr["want"], "created": tr["created"]}


# ---------------------------------------------------------------------------
# API
# ---------------------------------------------------------------------------

def new_session(p):
    tok = secrets.token_urlsafe(24)
    p.setdefault("tokens", []).append(tok)
    for old in p["tokens"][:-5]:
        tokens.pop(old, None)
    p["tokens"] = p["tokens"][-5:]
    tokens[tok] = p["id"]
    mark_dirty()
    return {"token": tok, "id": p["id"], "nickname": p["nickname"], "admin": bool(p.get("admin"))}


def api_register(body):
    nick = check_nick(body.get("nickname"))
    pw = str(body.get("password") or "")
    if len(pw) < 4:
        raise ApiError(400, "Password must be at least 4 characters.")
    salt = secrets.token_hex(16)
    pid = new_id("p")
    p = {"id": pid, "nickname": nick, "nick_lower": nick.lower(), "salt": salt, "pw": hash_pw(pw, salt),
         "tokens": [], "created": now(), "last_seen": now(), "banned": False, "admin": False,
         "profile": clean_profile({}), "inv": clean_inv({}), "deliveries": [], "friends": [], "requests": []}
    db["players"][pid] = p
    return new_session(p)


def api_login(body):
    p = find_by_nick(body.get("nickname"))
    pw = str(body.get("password") or "")
    if not p or not hmac.compare_digest(p["pw"], hash_pw(pw, p["salt"])):
        raise ApiError(401, "Wrong nickname or password.")
    if p.get("banned"):
        raise ApiError(403, "This account is banned.", banned=True)
    return new_session(p)


def api_logout(body):
    p = auth(body)
    tok = str(body.get("token"))
    tokens.pop(tok, None)
    p["tokens"] = [t for t in p["tokens"] if t != tok]
    leave_lobby(p["id"])
    mark_dirty()
    return {}


def api_rename(body):
    p = auth(body)
    nick = str(body.get("nickname") or "").strip()
    if nick.lower() != p["nick_lower"]:
        nick = check_nick(nick)
    elif not NICK_RE.match(nick):
        raise ApiError(400, "Nickname must be 3-16 letters, numbers or _.")
    p["nickname"], p["nick_lower"] = nick, nick.lower()
    mark_dirty()
    return {"nickname": nick}


def api_sync(body):
    p = auth(body)
    ack = set(str(a) for a in body.get("ack", []) if a)
    if ack:
        p["deliveries"] = [d for d in p.get("deliveries", []) if d["id"] not in ack]
    if "profile" in body:
        p["profile"] = clean_profile(body["profile"])
    # Only trust the inventory snapshot once the client has applied everything we sent it,
    # otherwise a snapshot from before a trade would undo the trade on the server.
    if "inv" in body and not p.get("deliveries"):
        p["inv"] = clean_inv(body["inv"])
    if body.get("pig_points"):
        add_pig_points(p, body["pig_points"])
    mark_dirty()
    club = my_club(p, need=False)

    code = player_lobby.get(p["id"])
    lobby = lobbies.get(code)
    if lobby:
        lobby["members"][p["id"]] = now()

    friends = []
    for fid in p.get("friends", []):
        f = db["players"].get(fid)
        if f and not f.get("banned"):
            s = player_summary(f)
            fl = lobbies.get(player_lobby.get(fid))
            s["lobby"] = fl["code"] if fl else None
            s["lobby_name"] = fl["name"] if fl else None
            friends.append(s)
    friends.sort(key=lambda s: (not s["online"], s["nickname"].lower()))
    requests = [{"id": r, "nickname": db["players"][r]["nickname"]}
                for r in p.get("requests", []) if r in db["players"]]
    trades = [trade_view(t) for t in db["trades"].values() if p["id"] in (t["from"], t["to"])]
    trades.sort(key=lambda t: -t["created"])
    return {
        "id": p["id"], "nickname": p["nickname"], "admin": bool(p.get("admin")),
        "deliveries": p.get("deliveries", []),
        "friends": friends, "requests": requests, "trades": trades,
        "lobby": lobby_view(lobby) if lobby else None,
        "club": club_view(club, p["id"]) if club else None,
        "announcement": db["announcement"],
    }


SORTS = {
    "trophies": lambda pr: pr["trophies"], "highest": lambda pr: pr["highest_trophies"],
    "brawlers": lambda pr: pr["brawlers"], "power": lambda pr: pr["power"],
    "skins": lambda pr: pr["skins"], "level": lambda pr: pr["level"],
    "rebirths": lambda pr: pr.get("rebirths", 0),
}


def api_leaderboard(body):
    sort = body.get("sort") if body.get("sort") in SORTS else "trophies"
    key = SORTS[sort]
    me = tokens.get(str(body.get("token") or ""))
    viewer_is_admin = bool(db["players"].get(me, {}).get("admin"))
    # admins are hidden from the leaderboard; only other admins can see them
    rows = [p for p in db["players"].values()
            if not p.get("banned") and (viewer_is_admin or not p.get("admin"))]
    rows.sort(key=lambda p: (-key(p.get("profile") or clean_profile({})), p["nick_lower"]))
    out, my_rank = [], None
    for i, p in enumerate(rows):
        if p["id"] == me:
            my_rank = i + 1
        if i < 100:
            prof = p.get("profile") or clean_profile({})
            out.append({"rank": i + 1, "id": p["id"], "nickname": p["nickname"], "value": key(prof),
                        "trophies": prof["trophies"], "brawlers": prof["brawlers"], "brawler": prof["brawler"],
                        "skin": prof["skin"], "online": is_online(p),
                        "admin": bool(p.get("admin")) and viewer_is_admin})
    return {"sort": sort, "rows": out, "my_rank": my_rank, "total": len(rows)}


# --- friends ---------------------------------------------------------------

def make_friends(a, b):
    for x, y in ((a, b), (b, a)):
        if y["id"] not in x.setdefault("friends", []):
            x["friends"].append(y["id"])
        x["requests"] = [r for r in x.get("requests", []) if r != y["id"]]
    mark_dirty()


def api_friend_request(body):
    p = auth(body)
    other = find_by_nick(body.get("nickname")) if body.get("nickname") else db["players"].get(str(body.get("player")))
    if not other or other.get("banned"):
        raise ApiError(404, "No player with that nickname.")
    if other["id"] == p["id"]:
        raise ApiError(400, "That's you!")
    if other["id"] in p.get("friends", []):
        raise ApiError(400, f"{other['nickname']} is already your friend.")
    if len(p.get("friends", [])) >= MAX_FRIENDS:
        raise ApiError(400, "Your friend list is full.")
    if other["id"] in p.get("requests", []):
        make_friends(p, other)
        return {"message": f"You and {other['nickname']} are now friends!"}
    reqs = other.setdefault("requests", [])
    if p["id"] not in reqs:
        reqs.append(p["id"])
        mark_dirty()
    return {"message": f"Friend request sent to {other['nickname']}."}


def api_friend_respond(body):
    p = auth(body)
    other = get_player(body.get("player"))
    if other["id"] not in p.get("requests", []):
        raise ApiError(400, "No request from that player.")
    if body.get("accept"):
        make_friends(p, other)
        return {"message": f"You and {other['nickname']} are now friends!"}
    p["requests"].remove(other["id"])
    mark_dirty()
    return {"message": "Request declined."}


def api_friend_remove(body):
    p = auth(body)
    other = get_player(body.get("player"))
    p["friends"] = [f for f in p.get("friends", []) if f != other["id"]]
    other["friends"] = [f for f in other.get("friends", []) if f != p["id"]]
    mark_dirty()
    return {"message": f"Removed {other['nickname']}."}


# --- lobbies ---------------------------------------------------------------

def api_lobby_list(body):
    out = []
    for lobby in lobbies.values():
        if lobby["public"]:
            host = db["players"].get(lobby["host"])
            out.append({"code": lobby["code"], "name": lobby["name"], "host": host["nickname"] if host else "?",
                        "members": len(lobby["members"]), "max": MAX_LOBBY})
    out.sort(key=lambda x: -x["members"])
    return {"lobbies": out[:50]}


def api_lobby_create(body):
    p = auth(body)
    leave_lobby(p["id"])
    name = clean_str(body.get("name"), 24).strip() or f"{p['nickname']}'s lobby"
    code = lobby_code()
    lobby = {"code": code, "name": name, "public": bool(body.get("public", True)), "host": p["id"],
             "members": {p["id"]: now()}, "chat": [], "created": now(), "last_group_drop": 0}
    lobbies[code] = lobby
    player_lobby[p["id"]] = code
    lobby_system_msg(lobby, f"{p['nickname']} created the lobby.")
    return {"lobby": lobby_view(lobby)}


def api_lobby_join(body):
    p = auth(body)
    code = clean_str(body.get("code"), 10).strip().upper()
    lobby = lobbies.get(code)
    if not lobby:
        raise ApiError(404, "No lobby with that code.")
    if p["id"] in lobby["members"]:
        return {"lobby": lobby_view(lobby)}
    if len(lobby["members"]) >= MAX_LOBBY:
        raise ApiError(400, "That lobby is full.")
    leave_lobby(p["id"])
    lobby["members"][p["id"]] = now()
    player_lobby[p["id"]] = code
    lobby_system_msg(lobby, f"{p['nickname']} joined.")
    return {"lobby": lobby_view(lobby)}


def api_lobby_leave(body):
    p = auth(body)
    leave_lobby(p["id"])
    return {}


def my_lobby(p):
    lobby = lobbies.get(player_lobby.get(p["id"]))
    if not lobby:
        raise ApiError(400, "You're not in a lobby.")
    return lobby


def api_lobby_chat(body):
    p = auth(body)
    lobby = my_lobby(p)
    msg = " ".join(str(body.get("text") or "").split())[:120]
    if not msg:
        raise ApiError(400, "Type a message first.")
    if now() - chat_last.get(p["id"], 0) < 0.7:
        raise ApiError(429, "Slow down!")
    chat_last[p["id"]] = now()
    lobby["chat"].append({"from": p["nickname"], "text": msg, "t": now(), "sys": False})
    del lobby["chat"][:-50]
    return {"lobby": lobby_view(lobby)}


def api_lobby_kick(body):
    p = auth(body)
    lobby = my_lobby(p)
    if lobby["host"] != p["id"]:
        raise ApiError(403, "Only the host can kick.")
    target = str(body.get("player"))
    if target == p["id"] or target not in lobby["members"]:
        raise ApiError(400, "Can't kick that player.")
    leave_lobby(target, "was kicked")
    t = db["players"].get(target)
    if t:
        deliver(t, "message", text=f"You were kicked from {lobby['name']}.")
    return {"lobby": lobby_view(lobby)}


def api_lobby_group_drop(body):
    p = auth(body)
    lobby = my_lobby(p)
    if lobby["host"] != p["id"]:
        raise ApiError(403, "Only the host can open a group drop.")
    wait = GROUP_DROP_COOLDOWN - (now() - lobby["last_group_drop"])
    if wait > 0:
        raise ApiError(429, f"Wait {int(wait) + 1}s before the next group drop.")
    reward = clean_reward(body.get("reward"))
    stages = [clean_str(s, 20) for s in (body.get("stages") or [])[:8]] or ["Rare"]
    lobby["last_group_drop"] = now()
    for pid in lobby["members"]:
        deliver(db["players"][pid], "group_drop", reward=reward, stages=stages, host=p["nickname"])
    lobby_system_msg(lobby, f"{p['nickname']} opened a {stages[-1]} group Starr Drop for everyone!")
    return {"lobby": lobby_view(lobby)}


# --- clubs -----------------------------------------------------------------
# Clubs are saved (unlike lobbies). Every club has a Megapig that its members fill by opening
# drops in their game; when it is smashed, everyone who helped gets Megapig drops.

def pig_week():
    return time.strftime("%G-W%V", time.gmtime())


def pig_tier(points):
    return sum(1 for need in MEGAPIG_TIERS if points >= need)


def new_pig():
    return {"points": 0, "week": pig_week(), "started": now()}


def club_tag():
    alphabet = string.ascii_uppercase + string.digits
    tags = {c["tag"] for c in db["clubs"].values()}
    while True:
        tag = "".join(secrets.choice(alphabet) for _ in range(6))
        if tag not in tags:
            return tag


def club_msg(club, msg, sender=""):
    club["chat"].append({"from": sender, "text": msg, "t": now(), "sys": not sender})
    del club["chat"][:-60]
    mark_dirty()


def smash_pig(club, reason):
    """Hand out the Megapig's rewards to everyone who helped, then start a new one."""
    pig = club["pig"]
    tier = pig_tier(pig["points"])
    helpers = 0
    if tier:
        for pid, m in club["members"].items():
            p = db["players"].get(pid)
            if p and m.get("pig", 0) > 0:
                deliver(p, "megapig", count=tier, club=club["name"], points=m["pig"])
                helpers += 1
        club_msg(club, f"The Megapig was smashed ({reason})! {helpers} helper{'s' if helpers != 1 else ''} "
                       f"got {tier} Megapig{'s' if tier != 1 else ''} each.")
    for m in club["members"].values():
        m["pig"] = 0
    club["pig"] = new_pig()
    mark_dirty()
    return tier


def club_tick(club):
    if club["pig"].get("week") != pig_week():
        smash_pig(club, "the week ended")


def my_club(p, need=True):
    club = db["clubs"].get(p.get("club") or "")
    if club and p["id"] not in club["members"]:
        club = None
    if not club:
        p.pop("club", None)
        if need:
            raise ApiError(400, "You're not in a club.")
        return None
    club_tick(club)
    return club


def remove_from_club(p, reason="left"):
    club = db["clubs"].get(p.get("club") or "")
    p.pop("club", None)
    if not club or p["id"] not in club["members"]:
        return
    del club["members"][p["id"]]
    club_msg(club, f"{p['nickname']} {reason}.")
    if not club["members"]:
        del db["clubs"][club["id"]]
    elif club["president"] == p["id"]:
        nxt = min(club["members"], key=lambda pid: club["members"][pid]["joined"])
        club["president"] = nxt
        club_msg(club, f"{db['players'][nxt]['nickname']} is now the president.")
    mark_dirty()


def club_view(club, viewer):
    members = []
    for pid, m in club["members"].items():
        q = db["players"].get(pid)
        if not q:
            continue
        prof = q.get("profile") or clean_profile({})
        members.append({"id": pid, "nickname": q["nickname"], "trophies": prof["trophies"], "online": is_online(q),
                        "president": pid == club["president"], "pig": m.get("pig", 0),
                        "brawler": prof["brawler"], "skin": prof["skin"]})
    members.sort(key=lambda m: (not m["president"], -m["trophies"], m["nickname"].lower()))
    pts = club["pig"]["points"]
    return {"id": club["id"], "tag": club["tag"], "name": club["name"], "desc": club["desc"],
            "open": club["open"], "president": club["president"], "members": members, "max": MAX_CLUB,
            "trophies": sum(m["trophies"] for m in members), "chat": club["chat"][-40:],
            "pig": {"points": pts, "tier": pig_tier(pts), "tiers": list(MEGAPIG_TIERS), "week": club["pig"]["week"],
                    "mine": club["members"].get(viewer, {}).get("pig", 0)}}


def add_pig_points(p, n):
    club = my_club(p, need=False)
    n = as_int(n, 0, MAX_PIG_POINTS_PER_SYNC)
    if not club or not n:
        return
    club["members"][p["id"]]["pig"] = club["members"][p["id"]].get("pig", 0) + n
    club["pig"]["points"] += n
    if club["pig"]["points"] >= MEGAPIG_TIERS[-1]:
        smash_pig(club, "it was completely full")
    mark_dirty()


def api_club_list(body):
    search = clean_str(body.get("search"), 30).strip().lower()
    out = []
    for c in db["clubs"].values():
        if search and search not in c["name"].lower() and search != c["tag"].lower():
            continue
        if not c["open"] and search != c["tag"].lower():
            continue
        trophies = sum((db["players"].get(pid, {}).get("profile") or {}).get("trophies", 0) for pid in c["members"])
        out.append({"id": c["id"], "tag": c["tag"], "name": c["name"], "desc": c["desc"], "open": c["open"],
                    "members": len(c["members"]), "max": MAX_CLUB, "trophies": trophies})
    out.sort(key=lambda c: (-c["trophies"], c["name"].lower()))
    return {"clubs": out[:50]}


def api_club_create(body):
    p = auth(body)
    if my_club(p, need=False):
        raise ApiError(400, "Leave your club first.")
    name = " ".join(clean_str(body.get("name"), 24).split())
    if len(name) < 3:
        raise ApiError(400, "Club name must be at least 3 characters.")
    if any(c["name"].lower() == name.lower() for c in db["clubs"].values()):
        raise ApiError(409, "A club with that name already exists.")
    cid = new_id("c")
    club = {"id": cid, "tag": club_tag(), "name": name, "desc": " ".join(clean_str(body.get("desc"), 80).split()),
            "open": bool(body.get("open", True)), "president": p["id"], "created": now(),
            "members": {p["id"]: {"joined": now(), "pig": 0}}, "chat": [], "pig": new_pig()}
    db["clubs"][cid] = club
    p["club"] = cid
    club_msg(club, f"{p['nickname']} founded the club.")
    return {"club": club_view(club, p["id"]), "message": f"Club {name} created!"}


def api_club_join(body):
    p = auth(body)
    if my_club(p, need=False):
        raise ApiError(400, "Leave your club first.")
    key = clean_str(body.get("tag"), 30).strip()
    club = db["clubs"].get(clean_str(body.get("club"), 20)) or next(
        (c for c in db["clubs"].values() if c["tag"] == key.upper()), None)
    if not club:
        raise ApiError(404, "No club with that tag.")
    if not club["open"] and key.upper() != club["tag"]:
        raise ApiError(403, "That club is invite-only - you need its tag.")
    if len(club["members"]) >= MAX_CLUB:
        raise ApiError(400, "That club is full.")
    club["members"][p["id"]] = {"joined": now(), "pig": 0}
    p["club"] = club["id"]
    club_msg(club, f"{p['nickname']} joined the club.")
    return {"club": club_view(club, p["id"]), "message": f"Welcome to {club['name']}!"}


def api_club_leave(body):
    p = auth(body)
    my_club(p)
    remove_from_club(p)
    return {"message": "You left the club."}


def api_club_chat(body):
    p = auth(body)
    club = my_club(p)
    msg = " ".join(str(body.get("text") or "").split())[:120]
    if not msg:
        raise ApiError(400, "Type a message first.")
    if now() - chat_last.get(p["id"], 0) < 0.7:
        raise ApiError(429, "Slow down!")
    chat_last[p["id"]] = now()
    club_msg(club, msg, sender=p["nickname"])
    return {"club": club_view(club, p["id"])}


def api_club_kick(body):
    p = auth(body)
    club = my_club(p)
    if club["president"] != p["id"]:
        raise ApiError(403, "Only the president can kick.")
    t = db["players"].get(str(body.get("player")))
    if not t or t["id"] == p["id"] or t["id"] not in club["members"]:
        raise ApiError(400, "Can't kick that player.")
    remove_from_club(t, "was kicked")
    deliver(t, "message", text=f"You were kicked from the club {club['name']}.")
    return {"club": club_view(club, p["id"])}


def api_club_settings(body):
    p = auth(body)
    club = my_club(p)
    if club["president"] != p["id"]:
        raise ApiError(403, "Only the president can change club settings.")
    if "open" in body:
        club["open"] = bool(body["open"])
    if "desc" in body:
        club["desc"] = " ".join(clean_str(body.get("desc"), 80).split())
    mark_dirty()
    return {"club": club_view(club, p["id"])}


def api_club_smash(body):
    p = auth(body)
    club = my_club(p)
    if club["president"] != p["id"]:
        raise ApiError(403, "Only the president can smash the Megapig early.")
    if not pig_tier(club["pig"]["points"]):
        raise ApiError(400, f"Fill the Megapig to {MEGAPIG_TIERS[0]} points first.")
    smash_pig(club, f"{p['nickname']} smashed it")
    return {"club": club_view(club, p["id"])}


# --- trades ----------------------------------------------------------------

def api_inventory(body):
    p = auth(body)
    other = get_player(body.get("player"))
    if not can_interact(p, other) and not p.get("admin"):
        raise ApiError(403, "You can only see friends' and lobby members' items.")
    inv = other.get("inv") or clean_inv({})
    return {"id": other["id"], "nickname": other["nickname"],
            "resources": inv["resources"],
            "brawlers": [b for b in inv["brawlers"] if b not in UNTRADABLE_BRAWLERS],
            "skins": [s for s in inv["skins"] if s not in UNTRADABLE_SKINS]}


def api_trade_offer(body):
    p = auth(body)
    other = get_player(body.get("player"))
    if other["id"] == p["id"]:
        raise ApiError(400, "You can't trade with yourself.")
    if not can_interact(p, other):
        raise ApiError(403, "You can only trade with friends or players in your lobby.")
    give, want = clean_bundle(body.get("give")), clean_bundle(body.get("want"))
    if bundle_empty(give) and bundle_empty(want):
        raise ApiError(400, "Add something to the trade first.")
    if sum(1 for t in db["trades"].values() if t["from"] == p["id"]) >= MAX_PENDING_TRADES:
        raise ApiError(400, "You have too many open offers - cancel some first.")
    check_can_give(p, give)
    check_can_give(other, want)
    check_can_receive(other, give)
    check_can_receive(p, want)
    tid = new_id("t")
    db["trades"][tid] = {"id": tid, "from": p["id"], "to": other["id"], "give": give, "want": want,
                         "created": now()}
    mark_dirty()
    return {"message": f"Offer sent to {other['nickname']}."}


def api_trade_respond(body):
    p = auth(body)
    tr = db["trades"].get(str(body.get("trade")))
    if not tr or p["id"] not in (tr["from"], tr["to"]):
        raise ApiError(404, "That trade is gone.")
    if not body.get("accept"):
        del db["trades"][tr["id"]]
        mark_dirty()
        return {"message": "Trade cancelled." if p["id"] == tr["from"] else "Trade declined."}
    if p["id"] != tr["to"]:
        raise ApiError(400, "Wait for the other player to accept.")
    a = get_player(tr["from"])
    if a.get("banned"):
        raise ApiError(400, "That player is banned.")
    try:
        check_can_give(a, tr["give"])
        check_can_give(p, tr["want"])
        check_can_receive(p, tr["give"])
        check_can_receive(a, tr["want"])
    except ApiError as e:
        del db["trades"][tr["id"]]
        mark_dirty()
        raise ApiError(400, "Trade no longer possible: " + e.message)
    del db["trades"][tr["id"]]
    inv_move(a, tr["give"], tr["want"])
    inv_move(p, tr["want"], tr["give"])
    deliver(a, "trade", give=tr["give"], get=tr["want"], partner=p["nickname"])
    deliver(p, "trade", give=tr["want"], get=tr["give"], partner=a["nickname"])
    return {"message": f"Trade with {a['nickname']} complete!"}


# --- admin -----------------------------------------------------------------

def api_admin_login(body):
    p = auth(body)
    fails = [t for t in admin_fails.get(p["id"], []) if now() - t < 600]
    if len(fails) >= 5:
        raise ApiError(429, "Too many wrong codes. Try again in 10 minutes.")
    if not hmac.compare_digest(str(body.get("code") or "").strip(), ADMIN_CODE):
        fails.append(now())
        admin_fails[p["id"]] = fails
        raise ApiError(403, "Invalid code.")
    p["admin"] = True
    mark_dirty()
    return {"admin": True, "message": "Admin panel unlocked!"}


def api_admin_leave(body):
    p = auth(body)
    p["admin"] = False
    mark_dirty()
    return {"admin": False}


def api_admin_overview(body):
    p = auth(body)
    require_admin(p)
    players = []
    for q in sorted(db["players"].values(), key=lambda q: q["nick_lower"]):
        prof = q.get("profile") or clean_profile({})
        players.append({"id": q["id"], "nickname": q["nickname"], "trophies": prof["trophies"],
                        "brawlers": prof["brawlers"], "online": is_online(q), "banned": bool(q.get("banned")),
                        "admin": bool(q.get("admin")), "lobby": player_lobby.get(q["id"]),
                        "sandbox": prof.get("sandbox", False),
                        "resources": (q.get("inv") or clean_inv({}))["resources"]})
    lob = [{"code": l["code"], "name": l["name"], "members": len(l["members"]), "public": l["public"],
            "host": db["players"][l["host"]]["nickname"] if l["host"] in db["players"] else "?"}
           for l in lobbies.values()]
    return {"players": players, "lobbies": lob, "announcement": db["announcement"]}


def api_admin_give(body):
    p = auth(body)
    require_admin(p)
    target = get_player(body.get("player"))
    rewards = [clean_reward(r) for r in (body.get("rewards") or [])[:20]]
    if not rewards:
        raise ApiError(400, "Nothing to give.")
    deliver(target, "grant", rewards=rewards, by=p["nickname"])
    return {"message": f"Sent to {target['nickname']}."}


def api_admin_take(body):
    p = auth(body)
    require_admin(p)
    target = get_player(body.get("player"))
    res = body.get("resources") if isinstance(body.get("resources"), dict) else {}
    take = {k: as_int(res.get(k)) for k in TAKEABLE if as_int(res.get(k)) > 0}
    if not take:
        raise ApiError(400, "Nothing to take.")
    inv_move(target, {"resources": {k: v for k, v in take.items() if k in RESOURCES}, "brawlers": [], "skins": []},
             {"resources": {}, "brawlers": [], "skins": []})
    deliver(target, "take", resources=take, by=p["nickname"])
    return {"message": f"Taken from {target['nickname']}."}


def api_admin_sandbox(body):
    """Switch unlimited free drops on or off for a player."""
    p = auth(body)
    require_admin(p)
    target = get_player(body.get("player"))
    on = bool(body.get("on"))
    target.setdefault("profile", clean_profile({}))["sandbox"] = on  # shown right away in the panel
    deliver(target, "sandbox", on=on, by=p["nickname"])
    return {"message": f"Unlimited free drops {'ON' if on else 'OFF'} for {target['nickname']}."}


def api_admin_ban(body):
    p = auth(body)
    require_admin(p)
    target = get_player(body.get("player"))
    if target["id"] == p["id"]:
        raise ApiError(400, "You can't ban yourself.")
    target["banned"] = bool(body.get("banned"))
    if target["banned"]:
        leave_lobby(target["id"], "was banned")
        remove_from_club(target, "was banned")
        db["trades"] = {k: t for k, t in db["trades"].items() if target["id"] not in (t["from"], t["to"])}
    mark_dirty()
    return {"message": f"{target['nickname']} {'banned' if target['banned'] else 'unbanned'}."}


def api_admin_rename(body):
    p = auth(body)
    require_admin(p)
    target = get_player(body.get("player"))
    nick = str(body.get("nickname") or "").strip()
    if nick.lower() != target["nick_lower"]:
        nick = check_nick(nick)
    target["nickname"], target["nick_lower"] = nick, nick.lower()
    deliver(target, "message", text=f"An admin changed your nickname to {nick}.")
    return {"message": f"Renamed to {nick}."}


def api_admin_announce(body):
    p = auth(body)
    require_admin(p)
    msg = " ".join(str(body.get("text") or "").split())[:140]
    db["announcement"] = {"id": db["announcement"].get("id", 0) + 1, "text": msg, "t": now()}
    mark_dirty()
    return {"message": "Announcement sent." if msg else "Announcement cleared."}


def api_admin_close_lobby(body):
    p = auth(body)
    require_admin(p)
    code = clean_str(body.get("code"), 10)
    if code not in lobbies:
        raise ApiError(404, "No such lobby.")
    close_lobby(code, "An admin closed your lobby.")
    return {"message": "Lobby closed."}


ROUTES = {
    "/api/register": api_register, "/api/login": api_login, "/api/logout": api_logout,
    "/api/rename": api_rename, "/api/sync": api_sync, "/api/leaderboard": api_leaderboard,
    "/api/friends/request": api_friend_request, "/api/friends/respond": api_friend_respond,
    "/api/friends/remove": api_friend_remove,
    "/api/lobby/list": api_lobby_list, "/api/lobby/create": api_lobby_create, "/api/lobby/join": api_lobby_join,
    "/api/lobby/leave": api_lobby_leave, "/api/lobby/chat": api_lobby_chat, "/api/lobby/kick": api_lobby_kick,
    "/api/lobby/group_drop": api_lobby_group_drop,
    "/api/club/list": api_club_list, "/api/club/create": api_club_create, "/api/club/join": api_club_join,
    "/api/club/leave": api_club_leave, "/api/club/chat": api_club_chat, "/api/club/kick": api_club_kick,
    "/api/club/settings": api_club_settings, "/api/club/smash": api_club_smash,
    "/api/inventory": api_inventory, "/api/trade/offer": api_trade_offer, "/api/trade/respond": api_trade_respond,
    "/api/admin/login": api_admin_login, "/api/admin/leave": api_admin_leave,
    "/api/admin/overview": api_admin_overview, "/api/admin/give": api_admin_give,
    "/api/admin/take": api_admin_take, "/api/admin/sandbox": api_admin_sandbox,
"/api/admin/ban": api_admin_ban, "/api/admin/rename": api_admin_rename,
    "/api/admin/announce": api_admin_announce, "/api/admin/close_lobby": api_admin_close_lobby,
}


class Handler(BaseHTTPRequestHandler):
    server_version = "BSCS/1.0"

    def log_message(self, fmt, *args):
        pass  # keep the console quiet

    def _send(self, status, data):
        raw = json.dumps(data).encode("utf8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(raw)))
        self._cors()
        self.end_headers()
        self.wfile.write(raw)

    def _cors(self):
        # Lets the browser version of the game talk to this server. Logins use a
        # token in the request body (no cookies), so allowing any site is safe.
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.send_header("Access-Control-Max-Age", "86400")

    def do_OPTIONS(self):
        self.send_response(204)
        self._cors()
        self.send_header("Content-Length", "0")
        self.end_headers()

    def do_GET(self):
        path = urlparse(self.path).path
        if path in ("/", "/health"):
            with lock:
                n = len(db["players"])
            self._send(200, {"ok": True, "server": "BSCS", "players": n, "lobbies": len(lobbies)})
        else:
            self._send(404, {"ok": False, "error": "Not found."})

    def do_POST(self):
        path = urlparse(self.path).path
        fn = ROUTES.get(path)
        if not fn:
            self._send(404, {"ok": False, "error": "Not found."})
            return
        try:
            length = int(self.headers.get("Content-Length") or 0)
            if length > 256 * 1024:
                raise ApiError(413, "Request too large.")
            body = json.loads(self.rfile.read(length) or b"{}") if length else {}
            if not isinstance(body, dict):
                raise ApiError(400, "Bad request.")
            with lock:
                cleanup()
                result = fn(body)
            out = {"ok": True}
            out.update(result or {})
            self._send(200, out)
        except ApiError as e:
            out = {"ok": False, "error": e.message}
            out.update(e.extra)
            self._send(e.status, out)
        except ValueError:
            self._send(400, {"ok": False, "error": "Bad request."})
        except Exception as e:  # never crash the server on one bad request
            print("ERROR", path, repr(e))
            self._send(500, {"ok": False, "error": "Server error."})


class DualStackServer(ThreadingHTTPServer):
    address_family = socket.AF_INET6

    def server_bind(self):
        self.socket.setsockopt(socket.IPPROTO_IPV6, socket.IPV6_V6ONLY, 0)
        super().server_bind()


def main():
    load_db()
    threading.Thread(target=saver_loop, daemon=True).start()
    try:  # listen on IPv6 and IPv4 so "localhost" doesn't wait for an IPv6 timeout first
        httpd = DualStackServer(("::", PORT), Handler)
    except OSError:
        httpd = ThreadingHTTPServer(("0.0.0.0", PORT), Handler)
    print(f"BSCS server running on port {PORT}  ({len(db['players'])} players, storage: {store.describe()})")
    if ADMIN_CODE == "1111":
        print("Admin code is the default 1111 - set the ADMIN_CODE environment variable to change it.")
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        with lock:
            text = json.dumps(db, separators=(",", ":"))
        store.save(text)
        print("Saved. Bye!")


if __name__ == "__main__":
    main()
