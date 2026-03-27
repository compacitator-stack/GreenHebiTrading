#!/usr/bin/env python3
"""GreenClaw Trading Bot — Standalone | Zero Dependencies | Telegram Commands
Ross Cameron Bull Flag Strategy on Alpaca Paper"""

import os, sys, json, time, ssl, signal
import urllib.request, urllib.error
from datetime import datetime, timezone, timedelta
try:
    from zoneinfo import ZoneInfo
    ET = ZoneInfo("America/New_York")
except ImportError:
    ET = timezone(timedelta(hours=-4))

# ── Config ───────────────────────────────────────────────
POLYGON_KEY = os.environ.get("POLYGON_API_KEY", "")
ALPACA_KEY  = os.environ.get("ALPACA_API_KEY", "")
ALPACA_SEC  = os.environ.get("ALPACA_SECRET_KEY", "")
ALPACA_URL  = os.environ.get("ALPACA_BASE_URL", "https://paper-api.alpaca.markets")
TG_TOKEN    = os.environ.get("TELEGRAM_BOT_TOKEN", "")
TG_CHAT     = os.environ.get("TELEGRAM_CHAT_ID", "")

RISK_PCT = 0.005       # 0.5% equity risk per trade
MAX_LOSS = -200.0      # daily loss halt
GAP_MIN  = 3.0         # min gap %
PRICE_LO = 2.0
PRICE_HI = 20.0
RVOL_MIN = 3.0
MIN_RR   = 2.0         # min risk:reward

LOG_FILE    = "greenclaw.log"
STATUS_FILE = "greenclaw_status.json"
PID_FILE    = "greenclaw.pid"
_ssl = ssl.create_default_context()
TG = f"https://api.telegram.org/bot{TG_TOKEN}"

# ── Helpers ──────────────────────────────────────────────
def now_et():
    return datetime.now(ET)

def log(lvl, msg):
    line = f"{now_et().strftime('%Y-%m-%d %H:%M:%S ET')} | {lvl:<5} | {msg}"
    print(line, flush=True)
    try:
        with open(LOG_FILE, "a") as f:
            f.write(line + "\n")
    except Exception:
        pass

def http(method, url, data=None, headers=None, timeout=15):
    try:
        hdrs = dict(headers) if headers else {}
        body = None
        if data is not None:
            body = json.dumps(data).encode()
            hdrs.setdefault("Content-Type", "application/json")
        req = urllib.request.Request(url, data=body, headers=hdrs, method=method)
        with urllib.request.urlopen(req, timeout=timeout, context=_ssl) as r:
            raw = r.read().decode()
            return json.loads(raw) if raw.strip() else {}
    except Exception as e:
        if "/getUpdates" not in url:
            log("ERROR", f"{method} {url[:80]} -> {e}")
        return None

def GET(url, h=None):
    return http("GET", url, headers=h)

def POST(url, d, h=None):
    return http("POST", url, d, h)

# ── Telegram ─────────────────────────────────────────────
def tg_send(text):
    if not TG_TOKEN or not TG_CHAT:
        return
    r = POST(f"{TG}/sendMessage",
             {"chat_id": TG_CHAT, "text": text[:4000], "parse_mode": "Markdown"})
    if not r:
        POST(f"{TG}/sendMessage",
             {"chat_id": TG_CHAT, "text": text[:4000]})

def tg_poll(offset=0, timeout=25):
    if not TG_TOKEN:
        time.sleep(timeout)
        return []
    url = f"{TG}/getUpdates?offset={offset}&timeout={timeout}"
    try:
        req = urllib.request.Request(url)
        with urllib.request.urlopen(req, timeout=timeout + 10, context=_ssl) as r:
            return json.loads(r.read().decode()).get("result", [])
    except Exception:
        return []

# ── Alpaca ───────────────────────────────────────────────
def alp_h():
    return {"APCA-API-KEY-ID": ALPACA_KEY,
            "APCA-API-SECRET-KEY": ALPACA_SEC}

def alp_get(path):
    return GET(f"{ALPACA_URL}{path}", h=alp_h())

def alp_post(path, data):
    return POST(f"{ALPACA_URL}{path}", data, h=alp_h())

def get_account():
    return alp_get("/v2/account") or {}

def get_equity():
    return float(get_account().get("equity", 0))

def get_positions():
    return alp_get("/v2/positions") or []

def get_bars(sym, tf="5Min", limit=20):
    url = (f"https://data.alpaca.markets/v2/stocks/{sym}/bars"
           f"?timeframe={tf}&limit={limit}&feed=iex")
    return GET(url, h=alp_h())

def place_bracket(sym, qty, entry, stop, target):
    order = {
        "symbol": sym, "qty": str(qty), "side": "buy",
        "type": "limit", "time_in_force": "day",
        "limit_price": str(round(entry, 2)),
        "order_class": "bracket",
        "take_profit": {"limit_price": str(round(target, 2))},
        "stop_loss": {"stop_price": str(round(stop, 2))}
    }
    log("INFO", f"ORDER: {sym} BUY {qty} @ {entry:.2f}"
                f" SL {stop:.2f} TP {target:.2f}")
    r = alp_post("/v2/orders", order)
    if r and r.get("id"):
        log("INFO", f"Order accepted: {r['id']}")
        tg_send(f"✅ ORDER PLACED\n{sym} BUY {qty}\n"
                f"Entry: ${entry:.2f}\nStop: ${stop:.2f}\n"
                f"Target: ${target:.2f}")
    else:
        log("ERROR", f"Order FAILED: {r}")
        tg_send(f"❌ ORDER FAILED {sym}\n{r}")
    return r

# ── Scanner ──────────────────────────────────────────────
def scan_premarket():
    log("INFO", "Running pre-market scan...")
    data = GET(f"https://api.polygon.io/v2/snapshot/locale/us/markets/stocks/gainers"
               f"?apiKey={POLYGON_KEY}")
    if not data:
        log("ERROR", "Polygon scan failed")
        return []

    results = []
    for t in data.get("tickers", []):
        try:
            sym = t.get("ticker", "")
            day = t.get("day", {})
            prev = t.get("prevDay", {})
            pc = float(prev.get("c") or 0)
            if pc <= 0:
                continue

            price = float(day.get("c") or 0)
            if price == 0:
                lt = t.get("lastTrade", {})
                price = float(lt.get("p") or 0)
            if price == 0:
                price = pc + float(t.get("todaysChange") or 0)
            if price <= 0:
                continue

            vol = int(day.get("v") or 0)
            pvol = int(prev.get("v") or 1)
            gap = ((price - pc) / pc) * 100
            rvol = vol / max(pvol, 1)

            if (gap >= GAP_MIN and PRICE_LO <= price <= PRICE_HI
                    and rvol >= RVOL_MIN):
                results.append({
                    "symbol": sym, "price": round(price, 2),
                    "gap": round(gap, 1), "rvol": round(rvol, 1),
                    "volume": vol
                })
                log("INFO", f"  + {sym}: ${price:.2f}"
                            f" gap {gap:.1f}% rvol {rvol:.1f}x")
        except Exception:
            continue

    results.sort(key=lambda x: x["gap"], reverse=True)
    results = results[:5]
    log("INFO", f"Scan done: {len(results)} candidates")
    return results

# ── Bull Flag Detector ───────────────────────────────────
def detect_flag(sym):
    resp = get_bars(sym, "5Min", 12)
    if not resp or "bars" not in resp:
        return None
    bars = resp["bars"]
    if len(bars) < 6:
        return None

    best_i, best_body = -1, 0
    for i in range(len(bars) - 3):
        o = float(bars[i]["o"])
        h = float(bars[i]["h"])
        l = float(bars[i]["l"])
        c = float(bars[i]["c"])
        body = c - o
        rng = h - l
        if body > 0 and rng > 0 and (body / rng) > 0.5:
            if body > best_body:
                best_i, best_body = i, body

    if best_i < 0:
        return None

    pole = bars[best_i]
    ph, pl = float(pole["h"]), float(pole["l"])
    pole_ht = ph - pl
    pole_vol = int(pole["v"])
    if pole_ht <= 0:
        return None

    flag = bars[best_i + 1:]
    if len(flag) < 2:
        return None
    fh = max(float(b["h"]) for b in flag)
    fl = min(float(b["l"]) for b in flag)
    avg_fv = sum(int(b["v"]) for b in flag) / len(flag)

    retrace = (ph - fl) / pole_ht
    if retrace > 0.50:
        return None
    if avg_fv >= pole_vol * 0.7:
        return None
    if fl < pl + pole_ht * 0.5:
        return None

    entry = round(fh + 0.02, 2)
    stop = round(fl - 0.02, 2)
    target = round(entry + pole_ht, 2)
    risk = entry - stop
    rr = (target - entry) / risk if risk > 0 else 0
    if rr < MIN_RR:
        return None

    log("INFO", f"FLAG: {sym} E=${entry} S=${stop}"
                f" T=${target} RR={rr:.1f}")
    return {"entry": entry, "stop": stop,
            "target": target, "rr": round(rr, 1)}

# ── State ────────────────────────────────────────────────
class State:
    def __init__(self):
        self.watchlist = []
        self.trades = 0
        self.pnl = 0.0
        self.scanned = False
        self.halted = False
        self.stopped = False
        self.date = ""
        self.equity = 0.0
        self.offset = 0
        self.force_scan = False
        self.start_time = now_et().isoformat()

    def save(self):
        try:
            with open(STATUS_FILE, "w") as f:
                json.dump({
                    "time": now_et().isoformat(),
                    "equity": self.equity,
                    "watchlist": self.watchlist,
                    "trades": self.trades,
                    "pnl": self.pnl,
                    "scanned": self.scanned,
                    "halted": self.halted,
                    "stopped": self.stopped,
                    "started": self.start_time
                }, f, indent=2)
        except Exception:
            pass

    def new_day(self, d):
        self.watchlist = []
        self.trades = 0
        self.pnl = 0.0
        self.scanned = False
        self.halted = False
        self.date = d
        self.force_scan = False

S = State()

# ── Commands ─────────────────────────────────────────────
def handle_cmd(text, cid):
    if str(cid) != str(TG_CHAT):
        return
    cmd = (text.strip().split()[0] if text else "").lower()

    if cmd == "/status":
        try:
            with open(STATUS_FILE) as f:
                d = json.load(f)
        except Exception:
            d = {}
        tg_send(
            f"📊 Status\n"
            f"Time: {d.get('time', '?')}\n"
            f"Equity: ${d.get('equity', 0):,.2f}\n"
            f"Watchlist: {len(d.get('watchlist', []))} symbols\n"
            f"Trades: {d.get('trades', 0)}\n"
            f"P&L: ${d.get('pnl', 0):+.2f}\n"
            f"Scanned: {d.get('scanned', False)}\n"
            f"Halted: {d.get('halted', False)}\n"
            f"Stopped: {d.get('stopped', False)}")

    elif cmd == "/logs":
        try:
            with open(LOG_FILE) as f:
                lines = f.readlines()[-15:]
            tg_send("📜 Logs\n" + "".join(lines))
        except Exception:
            tg_send("No logs found")

    elif cmd == "/watchlist":
        if S.watchlist:
            msg = "📋 Watchlist\n" + "\n".join(
                f"  {w['symbol']}: ${w['price']:.2f}"
                f" gap {w['gap']}% rvol {w['rvol']}x"
                for w in S.watchlist)
            tg_send(msg)
        else:
            tg_send("📋 Watchlist empty")

    elif cmd == "/scan":
        S.force_scan = True
        tg_send("🔄 Scan queued for next cycle")

    elif cmd == "/stop":
        S.stopped = True
        S.save()
        tg_send("⏹ Trading halted. Send /resume to restart")

    elif cmd == "/resume":
        S.stopped = False
        S.save()
        tg_send("▶ Trading resumed")

    elif cmd == "/help":
        tg_send(
            "🤖 GreenClaw Commands\n"
            "/status  - current state\n"
            "/logs    - recent log lines\n"
            "/watchlist - today's scan\n"
            "/scan    - force re-scan\n"
            "/stop    - halt trading\n"
            "/resume  - resume trading\n"
            "/help    - this message")

# ── Main Loop ────────────────────────────────────────────
def startup():
    log("INFO", "=" * 50)
    log("INFO", "GreenClaw starting (standalone)")
    log("INFO", f"  Python:  {sys.version.split()[0]}")
    log("INFO", f"  PID:     {os.getpid()}")
    log("INFO", f"  Polygon: {'OK' if POLYGON_KEY else 'MISSING'}")
    log("INFO", f"  Alpaca:  {'OK' if ALPACA_KEY else 'MISSING'}")
    log("INFO", f"  TG:      {'OK' if TG_TOKEN else 'MISSING'}")
    S.equity = get_equity()
    log("INFO", f"  Equity:  ${S.equity:,.2f}")
    t = now_et()
    log("INFO", f"  Time:    {t.strftime('%Y-%m-%d %H:%M:%S ET')}")
    log("INFO", "=" * 50)
    with open(PID_FILE, "w") as f:
        f.write(str(os.getpid()))
    tg_send(
        f"🟢 GreenClaw Started\n"
        f"Mode: Standalone Paper\n"
        f"Equity: ${S.equity:,.2f}\n"
        f"Time: {t.strftime('%Y-%m-%d %H:%M:%S ET')}\n"
        f"Send /help for commands")
    S.save()

def cycle():
    t = now_et()
    hh, mm = t.hour, t.minute
    today = t.strftime("%Y-%m-%d")

    if S.date != today:
        S.new_day(today)

    # Pre-market scan 9:00-9:05 ET (or forced)
    if (hh == 9 and mm < 5 and not S.scanned) or S.force_scan:
        S.watchlist = scan_premarket()
        S.scanned = True
        S.force_scan = False
        S.equity = get_equity()
        if S.watchlist:
            tg_send("🔍 PRE-MARKET SCAN\n" + "\n".join(
                f"  {w['symbol']} ${w['price']:.2f}"
                f" gap {w['gap']}% rvol {w['rvol']}x"
                for w in S.watchlist))
        else:
            tg_send("🔍 SCAN - No candidates today")
        S.save()

    # Trading window: 9:30-11:00 ET
    in_window = ((hh == 9 and mm >= 30) or hh == 10
                 or (hh == 11 and mm == 0))

    if (in_window and S.watchlist
            and not S.halted and not S.stopped):

        if S.pnl <= MAX_LOSS:
            S.halted = True
            tg_send(f"🛑 LOSS LIMIT HIT: ${S.pnl:+.2f}")
            S.save()
            return

        positions = get_positions()
        held = {p.get("symbol") for p in (positions or [])}

        for w in S.watchlist:
            sym = w["symbol"]
            if sym in held:
                continue

            sig = detect_flag(sym)
            if not sig:
                continue

            risk_ps = sig["entry"] - sig["stop"]
            if risk_ps <= 0:
                continue
            qty = int(S.equity * RISK_PCT / risk_ps)
            max_qty = int(S.equity * 0.25 / sig["entry"])
            qty = min(qty, max(max_qty, 0))
            if qty < 1:
                continue

            tg_send(
                f"🚩 BULL FLAG: {sym}\n"
                f"Entry ${sig['entry']:.2f}"
                f" Stop ${sig['stop']:.2f}"
                f" Target ${sig['target']:.2f}\n"
                f"R:R {sig['rr']}:1 | {qty} shares")
            r = place_bracket(sym, qty,
                              sig["entry"], sig["stop"],
                              sig["target"])
            if r and r.get("id"):
                S.trades += 1
                S.save()

    # EOD scorecard at 16:00
    if hh == 16 and mm < 5 and S.scanned:
        acc = get_account()
        S.equity = float(acc.get("equity", 0))
        last_eq = float(acc.get("last_equity", S.equity))
        S.pnl = round(S.equity - last_eq, 2)
        tg_send(
            f"📊 EOD SCORECARD\n"
            f"Trades: {S.trades}\n"
            f"P&L: ${S.pnl:+.2f}\n"
            f"Equity: ${S.equity:,.2f}")
        S.save()

    # Heartbeat log every 30 min outside market
    if (hh < 9 or hh >= 16) and mm % 30 == 0:
        log("INFO", f"Heartbeat {t.strftime('%H:%M ET')}")

def main():
    startup()
    log("INFO", "Main loop active (polling + trading)")
    while True:
        try:
            updates = tg_poll(S.offset, 25)
            for u in updates:
                msg = u.get("message", {})
                txt = msg.get("text", "")
                cid = msg.get("chat", {}).get("id", "")
                if txt:
                    handle_cmd(txt, cid)
                S.offset = u["update_id"] + 1
            cycle()
            S.save()
        except KeyboardInterrupt:
            log("INFO", "Shutdown (keyboard)")
            tg_send("🔴 GreenClaw stopped")
            break
        except Exception as e:
            log("ERROR", f"Loop error: {e}")
            time.sleep(10)

def _sig(s, _f):
    log("INFO", f"Signal {s}, shutting down")
    tg_send("🔴 GreenClaw stopped")
    sys.exit(0)

if __name__ == "__main__":
    signal.signal(signal.SIGTERM, _sig)
    signal.signal(signal.SIGINT, _sig)
    main()
