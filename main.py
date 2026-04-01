#!/usr/bin/env python3
"""
GreenClaw v3 — Ross Cameron Bull Flag Strategy
Standalone | Alpaca Paper | Polygon Scanner | Telegram

Changes from v2 based on Ross Cameron's full training video:
  - Float filter: ≤10M shares (Ross's exact non-negotiable rule)
  - RVOL is now time-of-day adjusted (today vol vs expected vol at
    this time, derived from prior day), matching Ross's "5x at this
    time of day" definition
  - High-of-day (HOD) used as primary profit target when available,
    measured move as fallback — matches Ross's exact target definition
  - Bull flag total length tightened to 5-7 candles (Ross: "usually
    5 to 7 individual candles")
  - FLAG_MAX_BARS reduced to 4 (so pole 3 + flag 4 = 7 max)
  - Quarter-size start, scale to full after cushion built
    (Ross: start 25% size, only go full size after first winner)
  - Cold market detection: if no trade in 30 min window, stop for day
  - Intraday re-scan every 15 min during 9:35-11:00 ET — catches mid-session
    momentum stocks that were not visible at 9:15 pre-market scan
  - Manual /scan always resets the cold-market halt timer if candidates found
  - Max loss = daily goal (Ross's exact symmetry rule)
  - Intraday HOD tracked live from 1-min bars
  - Breakeven stop move logged and noted after entry
  - All five criteria verified and logged for every scan candidate

Extended Hours (EXTENDED_HOURS=true):
  - Experimental, togglable via env var or /extended Telegram command
  - Premarket watchlist scan starts at 7:00 AM ET (always, even if EH off)
  - Re-scans every 15 min, merging new candidates (never overwrites)
  - Early session trading 8:00–9:14 ET with premarket bars
  - Late session trading 11:01–15:30 ET with same bull flag criteria
  - Uses standalone limit orders (bracket orders incompatible with EH)
  - Software-based stop-loss: bot polls price and sells via limit order
  - Half position size (EH_SIZE_MULT=0.50)
  - Max 1 EH trade per day (EH_MAX_TRADES=1)
  - Shared daily loss limit and max trades counter with core window
  - Cold market halt only affects core window, not EH sessions
  - Session tagging in Sheets: core / early / late for win-rate analysis
  - EOD forced liquidation at 15:55 for any open EH positions
"""

import os, sys, json, time, ssl, signal, math, threading
import urllib.request, urllib.error, urllib.parse
from datetime import datetime, timezone, timedelta, date
from http.server import HTTPServer, BaseHTTPRequestHandler

try:
    from zoneinfo import ZoneInfo
    ET = ZoneInfo("America/New_York")
except ImportError:
    ET = timezone(timedelta(hours=-4))

# ── Config ────────────────────────────────────────────────────────────────────
POLYGON_KEY  = os.environ.get("POLYGON_API_KEY", "")
ALPACA_KEY   = os.environ.get("ALPACA_API_KEY", "")
ALPACA_SEC   = os.environ.get("ALPACA_SECRET_KEY", "")
ALPACA_URL   = os.environ.get("ALPACA_BASE_URL", "https://paper-api.alpaca.markets")
TG_TOKEN     = os.environ.get("TELEGRAM_BOT_TOKEN", "")
TG_CHAT      = os.environ.get("TELEGRAM_CHAT_ID", "")
SHEETS_URL   = os.environ.get("SHEETS_WEBHOOK_URL", "")  # Google Apps Script webhook
DASH_TOKEN   = os.environ.get("DASHBOARD_TOKEN",    "")  # protects /api/dashboard & /api/log
DRY_RUN      = os.environ.get("DRY_RUN", "").lower() in ("1","true","yes")  # set DRY_RUN=true to simulate without placing orders
EXTENDED_HOURS = os.environ.get("EXTENDED_HOURS", "").lower() in ("1","true","yes")  # enable pre/post core window trading

# ── Extended hours parameters ─────────────────────────────────────────────────
# Experimental: allows trading outside the core 9:35–11:00 window.
# Uses standalone limit orders + software-based stop (no bracket orders).
# Alpaca stops do NOT fire in extended hours — bot polls and sells via limit.
EH_MAX_TRADES   = 1          # max extended-hours trades per day
EH_SIZE_MULT    = 0.50       # half position size for EH trades
EH_EARLY_START  = (8, 0)     # 8:00 AM ET — EH early trading window opens
EH_EARLY_END    = (9, 14)    # 9:14 AM ET — core takes over at 9:15
EH_LATE_START   = (11, 1)    # 11:01 AM ET — core window ends at 11:00
EH_LATE_END     = (15, 30)   # 3:30 PM ET — stop 30 min before close
EH_STOP_POLL_SEC = 15        # poll price every N seconds for software stop
PM_SCAN_START   = (7, 0)     # 7:00 AM ET — first premarket scan (always runs)
PM_SCAN_INTERVAL = 15        # re-scan every 15 min during premarket

# ── Strategy parameters (all sourced from Ross's exact rules) ─────────────────
RISK_PCT       = 0.005   # 0.5% equity at risk per trade
DAILY_TARGET   = 200.0   # daily profit goal  (set per account size)
MAX_LOSS       = -200.0  # daily loss limit = daily goal (Ross's rule)
CUSHION_PCT    = 0.25    # build cushion = 25% of daily target before full size

GAP_MIN        = 10.0    # Ross: "10% and higher is my real cutoff" (2% is minimum)
GAP_FLOOR      = 2.0     # absolute minimum gap — only used in B-mode
PRICE_LO       = 2.0     # Ross: $2–$20 range
PRICE_HI       = 20.0
RVOL_MIN       = 5.0     # Ross: "5× above average volume at this time of day"
FLOAT_MAX      = 10_000_000   # Ross: "under 10 million shares" — non-negotiable
MIN_RR         = 2.0     # Ross: 2:1 minimum
MAX_TRADES     = 3       # Ross: 2–3 quality setups per day max

# Bull flag candle geometry (Ross: "5 to 7 individual candles total")
POLE_MIN_BARS  = 3       # flagpole: at least 3 strong green candles
POLE_MIN_MOVE  = 0.10    # flagpole must move at least 10 cents
RETRACE_MAX    = 0.50    # flag pullback ≤ 50% of pole height
FLAG_VOL_RATIO = 0.70    # flag avg volume < 70% of pole avg volume (dry-up)
FLAG_MIN_BARS  = 2       # flag: at least 2 consolidation candles
FLAG_MAX_BARS  = 4       # flag: at most 4 candles (pole+flag = 7 max per Ross)

# Cold market rules (Ross: "if no trade in 30 min, call it")
NO_TRADE_HALT_MINS   = 30   # stop trying if no valid setup for this many minutes
INTRADAY_SCAN_MINS   = 15   # re-scan every N minutes during trading window
                            # catches stocks that emerge mid-session (today: ELAB, ASTC)

# B-mode (looser criteria, only if no A-quality by 10:00 ET, max 1 trade)
B_GAP_MIN      = 2.0
B_RVOL_MIN     = 4.0
B_FLOAT_MAX    = 15_000_000

LOG_FILE     = "greenclaw.log"
STATUS_FILE  = "greenclaw_status.json"
TRADES_FILE  = "greenclaw_trades.json"
PID_FILE     = "greenclaw.pid"

_ssl = ssl.create_default_context()
TG   = f"https://api.telegram.org/bot{TG_TOKEN}"

# ── Logging ───────────────────────────────────────────────────────────────────
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

# ── HTTP ──────────────────────────────────────────────────────────────────────
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
            log("ERROR", f"{method} {url[:80]} → {e}")
        return None

def GET(url, h=None):       return http("GET",    url, headers=h)
def POST(url, d, h=None):   return http("POST",   url, d, h)
def PATCH(url, d, h=None):  return http("PATCH",  url, d, h)
def DELETE(url, h=None):    return http("DELETE", url, headers=h)

# ── Telegram ──────────────────────────────────────────────────────────────────
def tg_send(text):
    if not TG_TOKEN or not TG_CHAT:
        return
    r = POST(f"{TG}/sendMessage",
             {"chat_id": TG_CHAT, "text": text[:4000], "parse_mode": "Markdown"})
    if not r:
        POST(f"{TG}/sendMessage", {"chat_id": TG_CHAT, "text": text[:4000]})

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

# ── Google Sheets webhook ────────────────────────────────────────────────────
def sheets_push(payload):
    """POST trade/eod/scan data to Google Apps Script webhook. Never crashes bot."""
    if not SHEETS_URL:
        return
    try:
        payload["bot_version"] = "GreenClaw v3"
        payload["timestamp"]   = now_et().isoformat()
        body = json.dumps(payload, default=str).encode()
        req  = urllib.request.Request(
            SHEETS_URL, data=body,
            headers={"Content-Type": "application/json"},
            method="POST")
        urllib.request.urlopen(req, timeout=10, context=_ssl)
        log("DEBUG", "Sheets push OK: " + payload.get("type", "?"))
    except Exception as e:
        log("DEBUG", "Sheets push failed (non-fatal): " + str(e))


# ── Alpaca ────────────────────────────────────────────────────────────────────
def alp_h():
    return {"APCA-API-KEY-ID": ALPACA_KEY, "APCA-API-SECRET-KEY": ALPACA_SEC}

def alp_get(p):    return GET(f"{ALPACA_URL}{p}", h=alp_h())
def alp_post(p,d): return POST(f"{ALPACA_URL}{p}", d, h=alp_h())
def alp_patch(p,d):return PATCH(f"{ALPACA_URL}{p}", d, h=alp_h())
def alp_del(p):    return DELETE(f"{ALPACA_URL}{p}", h=alp_h())

def get_account():   return alp_get("/v2/account") or {}
def get_equity():    return float(get_account().get("equity", 0))
def get_positions(): return alp_get("/v2/positions") or []
def get_orders():    return alp_get("/v2/orders?status=open&limit=50") or []

def get_live_pnl():
    """
    Fetch real-time intraday P&L from Alpaca account.
    Uses equity - last_equity (same calc as EOD, but live).
    Returns (pnl_float, equity_float) or (None, None) on failure.
    """
    try:
        acc = get_account()
        if not acc:
            return None, None
        equity   = float(acc.get("equity", 0))
        last_eq  = float(acc.get("last_equity", equity))
        return round(equity - last_eq, 2), equity
    except Exception as e:
        log("DEBUG", f"Live P&L fetch failed: {e}")
        return None, None

def manage_breakeven_stops(trades_today, be_moved_set):
    """
    Autonomous breakeven stop management.

    For each trade where the parent (buy) order has been FILLED,
    find the stop-loss child leg and PATCH its stop_price to the
    breakeven level (entry + $0.02).

    Uses Alpaca PATCH /v2/orders/{order_id} which is supported for
    bracket order legs to update stop_price.

    Args:
        trades_today: list of trade dicts from S.trades_today
        be_moved_set: set of order_ids already moved to breakeven
                      (prevents repeat attempts)
    Returns:
        set of newly-moved order_ids (caller should add to be_moved_set)
    """
    newly_moved = set()
    for tr in trades_today:
        order_id = tr.get("order_id", "")
        if not order_id or order_id in be_moved_set:
            continue
        if tr.get("dry_run"):
            continue  # skip simulated orders

        be_price = tr.get("breakeven_stop")
        if not be_price:
            continue

        try:
            # Fetch the parent order with nested legs
            full = alp_get(f"/v2/orders/{order_id}?nested=true")
            if not full:
                continue

            parent_status = full.get("status", "")
            if parent_status != "filled":
                continue  # buy not yet filled — nothing to move

            # Find the stop-loss child leg
            legs = full.get("legs", [])
            sl_leg = None
            for lg in legs:
                # Stop-loss leg: type is "stop" or "stop_limit"
                if lg.get("type") in ("stop", "stop_limit"):
                    sl_leg = lg
                    break

            if not sl_leg:
                log("WARN", f"  [{tr['symbol']}] BE: no stop leg found in order {order_id}")
                be_moved_set.add(order_id)  # don't retry
                continue

            sl_id     = sl_leg.get("id")
            sl_status = sl_leg.get("status", "")

            # Only modify if the stop leg is still pending (new/accepted/held)
            if sl_status not in ("new", "accepted", "held", "pending_new"):
                log("INFO", f"  [{tr['symbol']}] BE: stop leg status={sl_status}, "
                            f"skipping (already filled/cancelled)")
                be_moved_set.add(order_id)
                continue

            current_stop = float(sl_leg.get("stop_price", 0))
            if current_stop >= be_price:
                log("DEBUG", f"  [{tr['symbol']}] BE: stop already at ${current_stop:.2f} "
                             f">= BE ${be_price:.2f}")
                be_moved_set.add(order_id)
                continue

            # PATCH the stop-loss leg to breakeven
            log("INFO", f"  [{tr['symbol']}] Moving stop to breakeven: "
                        f"${current_stop:.2f} -> ${be_price:.2f}")
            patch_data = {"stop_price": str(round(be_price, 2))}
            result = alp_patch(f"/v2/orders/{sl_id}", patch_data)

            if result and result.get("id"):
                log("INFO", f"  [{tr['symbol']}] BE stop CONFIRMED | "
                            f"new stop=${be_price:.2f} | "
                            f"order={result.get('id')}")
                tg_send(f"🔒 *{tr['symbol']}* stop moved to breakeven "
                        f"${be_price:.2f}\n"
                        f"(was ${current_stop:.2f})")
                newly_moved.add(order_id)
            else:
                log("WARN", f"  [{tr['symbol']}] BE stop PATCH failed: {result}")
                tg_send(f"⚠️ {tr['symbol']} breakeven stop move failed\n"
                        f"Tried: ${current_stop:.2f} -> ${be_price:.2f}\n"
                        f"Check Alpaca dashboard")
                # Don't add to be_moved_set — will retry next cycle

        except Exception as e:
            log("ERROR", f"  [{tr.get('symbol','?')}] BE stop error: {e}")

    return newly_moved

def get_1min_bars(sym, limit=60):
    """Fetch 1-min bars from Alpaca IEX (Ross's primary chart timeframe)."""
    url = (f"https://data.alpaca.markets/v2/stocks/{sym}/bars"
           f"?timeframe=1Min&limit={limit}&feed=iex&adjustment=raw")
    resp = GET(url, h=alp_h())
    if not resp or "bars" not in resp:
        return []
    return resp["bars"]  # [{t, o, h, l, c, v, vw, n}, ...]

def place_bracket(sym, qty, entry, stop, target):
    """
    Submit bracket order to Alpaca and verify all three legs were accepted.
    In DRY_RUN mode, simulates the order without touching Alpaca.
    Returns order dict or None.
    """
    log("INFO", f"ORDER: {sym} BUY {qty} @ ${entry:.2f} "
                f"SL ${stop:.2f} TP ${target:.2f}")

    # ── Dry-run mode: simulate without placing ────────────────────────────────
    if DRY_RUN:
        fake_id = f"DRY-{sym}-{int(time.time())}"
        log("INFO", f"  🔵 DRY RUN — simulated order id={fake_id}")
        tg_send(f"🔵 *DRY RUN* — would place:\n"
                f"{sym} BUY {qty}sh @ ${entry:.2f}\n"
                f"SL ${stop:.2f} | TP ${target:.2f}")
        return {
            "id":          fake_id,
            "status":      "simulated",
            "symbol":      sym,
            "qty":         str(qty),
            "limit_price": str(entry),
            "legs":        "simulated",
            "dry_run":     True,
        }

    # ── Live order ────────────────────────────────────────────────────────────
    order = {
        "symbol": sym, "qty": str(qty), "side": "buy",
        "type": "limit", "time_in_force": "day",
        "limit_price": str(round(entry, 2)),
        "order_class": "bracket",
        "take_profit": {"limit_price": str(round(target, 2))},
        "stop_loss":   {"stop_price":  str(round(stop,  2))}
    }
    r = alp_post("/v2/orders", order)
    if not r or not r.get("id"):
        log("ERROR", f"  ❌ ORDER REJECTED: {r}")
        tg_send(f"❌ ORDER FAILED {sym}\n{str(r)[:200]}")
        return None

    order_id = r["id"]
    log("INFO", f"  ✅ Order accepted | id={order_id}")

    # ── Verify bracket legs were created (Alpaca-specific check) ─────────────
    # Query the order back after a short delay to confirm legs exist
    time.sleep(1.5)
    full = alp_get(f"/v2/orders/{order_id}")
    if not full:
        log("WARN", f"  ⚠️  Could not re-query order {order_id} for leg verification")
        tg_send(f"⚠️ {sym} order placed but could not verify bracket legs\n"
                f"Check Alpaca dashboard manually | id={order_id}")
        return r

    legs     = full.get("legs", [])
    statuses = [lg.get("status","?") for lg in legs] if legs else []
    tp_leg   = next((lg for lg in legs if lg.get("type") == "limit"),  None)
    sl_leg   = next((lg for lg in legs if lg.get("type") == "stop"),   None)

    if tp_leg and sl_leg:
        log("INFO", f"  ✅ Bracket legs verified: "
                    f"TP={tp_leg.get('limit_price','?')} "
                    f"SL={sl_leg.get('stop_price','?')} "
                    f"statuses={statuses}")
    else:
        log("WARN", f"  ⚠️  Bracket legs missing or unexpected: legs={legs}")
        tg_send(f"⚠️ {sym} bracket legs may be missing\n"
                f"legs found: {len(legs)} | statuses: {statuses}\n"
                f"id={order_id} — check Alpaca dashboard")

    return full  # return the verified full order (includes legs)

# ── Extended Hours Order Management ──────────────────────────────────────────
# Alpaca extended hours requires: type=limit, time_in_force=day, extended_hours=true
# Bracket orders are NOT compatible — so we use standalone limit orders
# and a software-based stop that polls price each cycle.

def place_eh_order(sym, qty, entry, stop, target):
    """
    Submit a standalone limit buy for extended hours trading.
    Cannot use bracket orders — Alpaca rejects non-limit order types in EH.
    Stop-loss is managed by software polling (monitor_eh_stops).
    Take-profit limit sell is submitted after fill is confirmed.

    In DRY_RUN mode, simulates without touching Alpaca.
    Returns order dict or None.
    """
    log("INFO", f"EH ORDER: {sym} BUY {qty} @ ${entry:.2f} "
                f"SL ${stop:.2f} (software) TP ${target:.2f}")

    if DRY_RUN:
        fake_id = f"DRY-EH-{sym}-{int(time.time())}"
        log("INFO", f"  🔵 DRY RUN EH — simulated order id={fake_id}")
        tg_send(f"🔵 *DRY RUN EH* — would place:\n"
                f"{sym} BUY {qty}sh @ ${entry:.2f}\n"
                f"SL ${stop:.2f} (software) | TP ${target:.2f}")
        # Register software stop even in dry-run so monitoring logic is tested
        S.eh_active_stops[fake_id] = {
            "symbol": sym, "stop_price": stop, "target": target,
            "qty": qty, "entry": entry, "filled": False,
            "fill_price": None, "tp_order_id": None, "dry_run": True,
        }
        return {"id": fake_id, "status": "simulated", "symbol": sym,
                "qty": str(qty), "dry_run": True}

    # Submit standalone limit buy with extended_hours flag
    order = {
        "symbol": sym, "qty": str(qty), "side": "buy",
        "type": "limit", "time_in_force": "day",
        "limit_price": str(round(entry, 2)),
        "extended_hours": True,
    }
    r = alp_post("/v2/orders", order)
    if not r or not r.get("id"):
        log("ERROR", f"  ❌ EH ORDER REJECTED: {r}")
        tg_send(f"❌ EH ORDER FAILED {sym}\n{str(r)[:200]}")
        return None

    order_id = r["id"]
    log("INFO", f"  ✅ EH order accepted | id={order_id}")
    tg_send(f"✅ *EH Order Placed: {sym}*\n"
            f"BUY {qty}sh @ ${entry:.2f} (limit)\n"
            f"SL ${stop:.2f} (software-managed)\n"
            f"TP ${target:.2f}\n"
            f"⚠️ Stop is bot-managed — not broker-side")

    # Register for software stop monitoring
    S.eh_active_stops[order_id] = {
        "symbol": sym, "stop_price": stop, "target": target,
        "qty": qty, "entry": entry, "filled": False,
        "fill_price": None, "tp_order_id": None, "dry_run": False,
    }
    return r


def monitor_eh_stops():
    """
    Software-based stop-loss and take-profit management for extended hours trades.

    Called every cycle. For each active EH trade:
    1. If buy not yet filled: check order status, submit TP on fill
    2. If filled: poll current price, trigger stop if breached
    3. Clean up completed/cancelled orders

    This exists because Alpaca stop orders do NOT trigger outside
    regular market hours (9:30 AM – 4:00 PM ET).
    """
    if not S.eh_active_stops:
        return

    for order_id in list(S.eh_active_stops.keys()):
        info = S.eh_active_stops[order_id]
        sym  = info["symbol"]

        try:
            # ── Phase 1: Check if buy order filled ────────────────────────
            if not info["filled"]:
                if info.get("dry_run"):
                    # Simulate instant fill for dry-run
                    info["filled"]     = True
                    info["fill_price"] = info["entry"]
                    log("INFO", f"  [{sym}] EH DRY RUN: simulated fill @ ${info['entry']:.2f}")
                else:
                    order = alp_get(f"/v2/orders/{order_id}")
                    if not order:
                        continue
                    status = order.get("status", "")
                    if status == "filled":
                        fill_px = float(order.get("filled_avg_price", info["entry"]))
                        info["filled"]     = True
                        info["fill_price"] = fill_px
                        log("INFO", f"  [{sym}] EH buy FILLED @ ${fill_px:.2f}")
                        tg_send(f"✅ *EH Fill: {sym}* @ ${fill_px:.2f}\n"
                                f"Software stop active @ ${info['stop_price']:.2f}")

                        # Submit take-profit limit sell
                        tp_order = {
                            "symbol": sym, "qty": str(info["qty"]), "side": "sell",
                            "type": "limit", "time_in_force": "day",
                            "limit_price": str(round(info["target"], 2)),
                            "extended_hours": True,
                        }
                        tp_r = alp_post("/v2/orders", tp_order)
                        if tp_r and tp_r.get("id"):
                            info["tp_order_id"] = tp_r["id"]
                            log("INFO", f"  [{sym}] EH take-profit submitted: "
                                        f"SELL @ ${info['target']:.2f} | id={tp_r['id']}")
                        else:
                            log("WARN", f"  [{sym}] EH take-profit submit FAILED: {tp_r}")
                            tg_send(f"⚠️ {sym} EH take-profit order failed\n"
                                    f"Tried: SELL @ ${info['target']:.2f}\n"
                                    f"Software stop still active")

                    elif status in ("canceled", "cancelled", "expired", "rejected"):
                        log("INFO", f"  [{sym}] EH buy order {status} — removing")
                        del S.eh_active_stops[order_id]
                    # else: still pending, check next cycle
                    continue

            # ── Phase 2: Buy is filled — monitor price for stop ───────────
            # Check if TP already filled (position closed)
            if info.get("tp_order_id") and not info.get("dry_run"):
                tp_check = alp_get(f"/v2/orders/{info['tp_order_id']}")
                if tp_check and tp_check.get("status") == "filled":
                    tp_fill = float(tp_check.get("filled_avg_price", info["target"]))
                    log("INFO", f"  [{sym}] EH take-profit FILLED @ ${tp_fill:.2f}")
                    tg_send(f"🎯 *EH Target Hit: {sym}* @ ${tp_fill:.2f}\n"
                            f"Entry: ${info['fill_price']:.2f} | "
                            f"Gain: ${tp_fill - info['fill_price']:.2f}/sh")
                    del S.eh_active_stops[order_id]
                    continue

            # Dry-run: simulate TP hit if price reaches target
            if info.get("dry_run"):
                bars = get_1min_bars(sym, limit=2)
                if bars:
                    current_price = float(bars[-1]["c"])
                    if current_price >= info["target"]:
                        log("INFO", f"  [{sym}] DRY RUN — simulated TP hit @ ${current_price:.2f}")
                        tg_send(f"🎯 *EH Target Hit (DRY RUN): {sym}* @ ${current_price:.2f}\n"
                                f"Entry: ${info['fill_price']:.2f} | "
                                f"Gain: ${current_price - info['fill_price']:.2f}/sh")
                        del S.eh_active_stops[order_id]
                        continue

            # Poll current price via 1-min bars
            bars = get_1min_bars(sym, limit=2)
            if not bars:
                continue
            current_price = float(bars[-1]["c"])

            # Check stop breach
            if current_price <= info["stop_price"]:
                log("WARN", f"  [{sym}] EH SOFTWARE STOP TRIGGERED: "
                            f"${current_price:.2f} <= ${info['stop_price']:.2f}")

                if info.get("dry_run"):
                    log("INFO", f"  [{sym}] DRY RUN — simulated stop exit")
                    tg_send(f"🛑 *EH STOP HIT (DRY RUN): {sym}*\n"
                            f"Price ${current_price:.2f} <= stop ${info['stop_price']:.2f}\n"
                            f"Entry was ${info['fill_price']:.2f} | "
                            f"Loss: ${current_price - info['fill_price']:.2f}/sh")
                    del S.eh_active_stops[order_id]
                    continue

                # Cancel TP order first
                if info.get("tp_order_id"):
                    alp_del(f"/v2/orders/{info['tp_order_id']}")
                    log("INFO", f"  [{sym}] Cancelled TP order before stop exit")

                # Submit aggressive limit sell (price - 5¢ to ensure fill)
                stop_sell = alp_post("/v2/orders", {
                    "symbol": sym, "qty": str(info["qty"]), "side": "sell",
                    "type": "limit", "time_in_force": "day",
                    "limit_price": str(round(current_price - 0.05, 2)),
                    "extended_hours": True,
                })
                if stop_sell and stop_sell.get("id"):
                    log("INFO", f"  [{sym}] EH stop sell submitted @ "
                                f"${current_price - 0.05:.2f} | id={stop_sell['id']}")
                else:
                    log("ERROR", f"  [{sym}] EH stop sell FAILED: {stop_sell}")

                tg_send(f"🛑 *EH STOP HIT: {sym}*\n"
                        f"Price ${current_price:.2f} <= stop ${info['stop_price']:.2f}\n"
                        f"Entry: ${info['fill_price']:.2f} | "
                        f"Loss: ${current_price - info['fill_price']:.2f}/sh\n"
                        f"Selling at ~${current_price - 0.05:.2f}")
                del S.eh_active_stops[order_id]

        except Exception as e:
            log("ERROR", f"  [{sym}] EH stop monitor error: {e}")


# ── Polygon helpers ───────────────────────────────────────────────────────────
def get_float(sym):
    """
    Fetch share float from Polygon reference API.
    Ross: "under 10 million shares" is non-negotiable.
    Returns float in shares or None if unavailable.
    """
    resp = GET(f"https://api.polygon.io/v3/reference/tickers/{sym}"
               f"?apiKey={POLYGON_KEY}")
    if not resp:
        return None
    result = resp.get("results", {})
    # Polygon provides share_class_shares_outstanding and weighted_shares_outstanding
    # The float (tradeable shares) is best approximated by share_class_shares_outstanding
    float_val = result.get("share_class_shares_outstanding")
    if float_val:
        return int(float_val)
    # Fallback: weighted shares outstanding
    wso = result.get("weighted_shares_outstanding")
    if wso:
        return int(wso)
    return None

def check_catalyst(sym):
    """
    Check multiple sources for a recent news catalyst.
    Ross: "there must be a headline that justifies why the stock is moving."
    Ross: "my best trades are when the catalyst is obvious."

    Sources checked (in order):
      1. Polygon News API — financial news articles mentioning the ticker
      2. SEC EDGAR EFTS  — recent 8-K (material events), S-1 (IPO), or
                           other significant filings (free, no API key)

    Returns (bool, headline_string).
    """
    headlines = []

    # ── Source 1: Polygon News ────────────────────────────────────────────
    try:
        yesterday = (now_et().date() - timedelta(days=2)).isoformat()
        url = (f"https://api.polygon.io/v2/reference/news"
               f"?ticker={sym}&published_utc.gte={yesterday}"
               f"&limit=3&apiKey={POLYGON_KEY}")
        resp = GET(url)
        if resp and resp.get("results"):
            headline = resp["results"][0].get("title", "News found")
            headlines.append(("📰 Polygon", headline))
    except Exception:
        pass

    # ── Source 2: SEC EDGAR EFTS (full-text search) ───────────────────────
    # Free API, no key needed. Searches recent filings mentioning the ticker.
    # Covers 8-K (material events like FDA, contracts, offerings),
    # S-1 (IPO registrations), and other catalyst-type filings.
    try:
        # EDGAR EFTS requires a User-Agent header with contact info
        today_str = now_et().date().isoformat()
        three_days_ago = (now_et().date() - timedelta(days=3)).isoformat()
        edgar_url = (f"https://efts.sec.gov/LATEST/search-index"
                     f"?q=%22{sym}%22&dateRange=custom"
                     f"&startdt={three_days_ago}&enddt={today_str}"
                     f"&forms=8-K,S-1,424B4,6-K"
                     f"&from=0&size=3")
        edgar_headers = {"User-Agent": "GreenClaw/3.0 (trading-bot@example.com)"}
        edgar_resp = http("GET", edgar_url, headers=edgar_headers, timeout=8)
        if edgar_resp and edgar_resp.get("hits"):
            hits = edgar_resp["hits"].get("hits", [])
            if hits:
                filing = hits[0].get("_source", {})
                form_type = filing.get("forms", "filing")
                filed_date = filing.get("file_date", "")
                entity = filing.get("entity_name", sym)
                headlines.append(("📋 SEC", f"{form_type} filed {filed_date} by {entity}"))
    except Exception as e:
        log("DEBUG", f"  [{sym}] EDGAR check failed: {e}")

    # ── Fallback: SEC EDGAR submissions API (company recent filings) ──────
    # If EFTS didn't find anything, try the submissions endpoint
    # which lists all recent filings for a company by CIK.
    if not headlines:
        try:
            # First get CIK from ticker via SEC company tickers JSON
            tickers_url = "https://www.sec.gov/files/company_tickers.json"
            tickers_resp = http("GET", tickers_url,
                                headers={"User-Agent": "GreenClaw/3.0 (trading-bot@example.com)"},
                                timeout=8)
            if tickers_resp:
                cik = None
                for entry in tickers_resp.values():
                    if entry.get("ticker", "").upper() == sym.upper():
                        cik = str(entry.get("cik_str", "")).zfill(10)
                        break
                if cik:
                    sub_url = f"https://data.sec.gov/submissions/CIK{cik}.json"
                    sub_resp = http("GET", sub_url,
                                    headers={"User-Agent": "GreenClaw/3.0 (trading-bot@example.com)"},
                                    timeout=8)
                    if sub_resp and sub_resp.get("filings"):
                        recent = sub_resp["filings"].get("recent", {})
                        forms = recent.get("form", [])
                        dates = recent.get("filingDate", [])
                        descs = recent.get("primaryDocDescription", [])
                        # Look for significant filings in last 3 days
                        catalyst_forms = {"8-K", "S-1", "S-1/A", "424B4", "424B5",
                                          "6-K", "8-K/A", "SC 13D", "SC 13D/A"}
                        cutoff = (now_et().date() - timedelta(days=3)).isoformat()
                        for i in range(min(10, len(forms))):
                            if dates[i] >= cutoff and forms[i] in catalyst_forms:
                                desc = descs[i] if i < len(descs) else forms[i]
                                headlines.append(("📋 SEC", f"{forms[i]} filed {dates[i]}: {desc}"))
                                break
        except Exception as e:
            log("DEBUG", f"  [{sym}] EDGAR submissions check failed: {e}")

    # ── Return best result ────────────────────────────────────────────────
    if headlines:
        source, headline = headlines[0]
        return True, f"{source}: {headline}"
    return False, "No recent news"

# ── Time-of-day RVOL ──────────────────────────────────────────────────────────
def calc_tod_rvol(today_vol, prev_day_vol, minutes_traded):
    """
    Ross's definition: "5× above average volume based on what it would
    typically have at this time of day."

    We estimate expected volume at this time of day by assuming a roughly
    uniform intraday distribution over a 6.5-hour (390-minute) session.
    So expected volume at `minutes_traded` minutes into the day =
        prev_day_vol × (minutes_traded / 390)

    This avoids the problem of comparing 30 minutes of today's volume
    against a full prior day — which massively understates RVOL early.
    """
    if prev_day_vol <= 0 or minutes_traded <= 0:
        return 0.0
    expected_vol = prev_day_vol * (minutes_traded / 390.0)
    if expected_vol <= 0:
        return 0.0
    return today_vol / expected_vol

# ── Pre-market high ───────────────────────────────────────────────────────────
def get_premarket_high(sym):
    """
    Fetch today's pre-market (4:00–9:29 ET) high from Polygon 1-min bars.
    This is Ross's key level — a stock clearing its pre-market high on
    the bull flag breakout is a much stronger signal.
    """
    try:
        today = now_et().date().isoformat()
        url = (f"https://api.polygon.io/v2/aggs/ticker/{sym}/range/1/minute"
               f"/{today}/{today}?adjusted=false&sort=asc&limit=200"
               f"&apiKey={POLYGON_KEY}")
        resp = GET(url)
        if not resp or not resp.get("results"):
            return None
        pm_bars = []
        for bar in resp["results"]:
            ts_et = datetime.fromtimestamp(bar["t"] / 1000, tz=ET)
            if ts_et.hour < 9 or (ts_et.hour == 9 and ts_et.minute < 30):
                pm_bars.append(bar)
        if not pm_bars:
            return None
        return max(float(b["h"]) for b in pm_bars)
    except Exception as e:
        log("DEBUG", f"PMH fetch failed {sym}: {e}")
        return None

# ── VWAP ─────────────────────────────────────────────────────────────────────
def calc_vwap(bars):
    """Cumulative VWAP from a list of bar dicts. Returns list aligned to bars."""
    vwap_vals, cum_tpv, cum_v = [], 0.0, 0.0
    for b in bars:
        try:
            h, l, c, v = float(b["h"]), float(b["l"]), float(b["c"]), float(b["v"])
            cum_tpv += ((h + l + c) / 3) * v
            cum_v   += v
            vwap_vals.append(cum_tpv / cum_v if cum_v > 0 else c)
        except Exception:
            vwap_vals.append(vwap_vals[-1] if vwap_vals else 0.0)
    return vwap_vals

# ── Bull Flag Detector ────────────────────────────────────────────────────────
def detect_flag(sym, premarket_high=None, session="core"):
    """
    Ross Cameron Bull Flag on 1-minute chart.

    Ross's exact pattern (from transcript):
    - "Usually constructed of 5 to 7 individual candles"
    - "First one is a green candle" (the flagpole surge)
    - Volume ramps up on the pole, decreases on the flag ("lighter volume on selling")
    - "First candle to make a new high — that's the moment you're buying"
    - "My stop is the low of the pullback"
    - "Profit target: retest of the high of day"

    session parameter controls which bars are eligible:
      "core"  — 9:35–11:00 ET (default, original behavior)
      "early" — 8:00–9:14 ET (premarket, extended hours)
      "late"  — 9:35–15:30 ET (extended hours afternoon)

    Returns signal dict or None. Logs reason for every rejection.
    """
    bars = get_1min_bars(sym, limit=60)
    if not bars:
        log("INFO", f"  [{sym}] SKIP: no 1-min bar data")
        return None

    # Filter to today's bars only
    today_str = now_et().date().isoformat()
    bars = [b for b in bars if b["t"][:10] == today_str]

    # Determine the bar window based on session
    if session == "early":
        # Premarket: accept bars from 8:00 through 9:14 ET
        start_hour, start_min = EH_EARLY_START  # (8, 0)
        end_hour, end_min = EH_EARLY_END        # (9, 14)
    elif session == "late":
        # Extended hours afternoon: accept bars from 9:35 through 15:30 ET
        start_hour, start_min = 9, 35
        end_hour, end_min = EH_LATE_END  # (15, 30)
    else:
        # Core window: 9:35–11:00 ET (original behavior)
        start_hour, start_min = 9, 35
        end_hour, end_min = 11, 0

    # Collect bars for VWAP computation and pattern detection
    # all_today: all bars from 9:30+ (for VWAP) or 8:00+ (for early session)
    # market_bars: only bars within the active session window
    all_today = []
    market_bars = []
    vwap_start_hour = start_hour if session == "early" else 9
    vwap_start_min  = start_min  if session == "early" else 30
    for b in bars:
        ts_et = datetime.fromisoformat(b["t"].replace("Z", "+00:00")).astimezone(ET)
        if ts_et.hour > vwap_start_hour or (ts_et.hour == vwap_start_hour and ts_et.minute >= vwap_start_min):
            all_today.append(b)
        if ts_et.hour > start_hour or (ts_et.hour == start_hour and ts_et.minute >= start_min):
            if ts_et.hour < end_hour or (ts_et.hour == end_hour and ts_et.minute <= end_min):
                market_bars.append(b)

    min_needed = POLE_MIN_BARS + FLAG_MIN_BARS + 1
    if len(market_bars) < min_needed:
        log("INFO", f"  [{sym}] SKIP: only {len(market_bars)} usable bars "
                    f"(need ≥{min_needed})")
        return None

    # VWAP from full session including pre-35 bars for accuracy
    vwap_all  = calc_vwap(all_today)
    vwap_dict = {}
    for i, b in enumerate(all_today):
        vwap_dict[b["t"]] = vwap_all[i]

    current_vwap  = vwap_dict.get(all_today[-1]["t"], float(market_bars[-1]["c"]))
    current_price = float(market_bars[-1]["c"])
    intraday_hod  = max(float(b["h"]) for b in all_today) if all_today else current_price

    # Price below VWAP is a quick exit for the whole symbol
    if current_price < current_vwap * 0.995:
        log("INFO", f"  [{sym}] NO FLAG: price ${current_price:.2f} "
                    f"below VWAP ${current_vwap:.2f}")
        return None

    # ── Slide window looking for pole + flag (total 5-7 candles) ─────────────
    # Use last 20 bars max so patterns are fresh
    window     = market_bars[-20:] if len(market_bars) >= 20 else market_bars
    best       = None

    for pole_start in range(len(window) - POLE_MIN_BARS - FLAG_MIN_BARS - 1):
        for pole_len in range(POLE_MIN_BARS, min(6, len(window) - pole_start - FLAG_MIN_BARS)):
            pole = window[pole_start : pole_start + pole_len]

            # ── Flagpole validation ───────────────────────────────────────────
            pole_bottom = float(pole[0]["l"])
            pole_top    = max(float(b["h"]) for b in pole)
            pole_height = pole_top - pole_bottom

            if pole_height < POLE_MIN_MOVE:
                continue

            # ≥60% of pole candles green
            green = sum(1 for b in pole if float(b["c"]) > float(b["o"]))
            if green < len(pole) * 0.6:
                continue

            # ≥50% of pole candles have real bodies (body/range ≥ 40%)
            strong = sum(
                1 for b in pole
                if (float(b["h"]) - float(b["l"])) > 0
                and abs(float(b["c"]) - float(b["o"])) /
                    (float(b["h"]) - float(b["l"])) >= 0.40
            )
            if strong < len(pole) * 0.5:
                continue

            pole_avg_vol = sum(float(b["v"]) for b in pole) / len(pole)

            # ── Flag validation ───────────────────────────────────────────────
            for flag_len in range(FLAG_MIN_BARS, FLAG_MAX_BARS + 1):
                fi = pole_start + pole_len
                fe = fi + flag_len
                if fe >= len(window):
                    break

                flag = window[fi:fe]
                flag_low  = min(float(b["l"]) for b in flag)
                flag_high = max(float(b["h"]) for b in flag)
                flag_avg_vol = sum(float(b["v"]) for b in flag) / len(flag)

                # Retracement ≤ 50% of pole (Ross's rule)
                retrace = (pole_top - flag_low) / pole_height if pole_height else 1.0
                if retrace > RETRACE_MAX:
                    continue

                # Volume dry-up in flag (Ross: "lighter volume on the selling")
                if pole_avg_vol > 0 and flag_avg_vol >= pole_avg_vol * FLAG_VOL_RATIO:
                    continue

                # Flag must hold above VWAP
                vwap_at_flag = vwap_dict.get(flag[0]["t"], current_vwap)
                if flag_low < vwap_at_flag * 0.997:
                    continue

                # Pre-market high check: flag holding near/above PMH is stronger
                if premarket_high and premarket_high > 0:
                    if flag_low < premarket_high * 0.98:
                        continue  # failed to hold PMH support

                # ── Breakout signal: bar AFTER flag makes new high ────────────
                # Ross: "first candle to make a new high — that's when you buy"
                breakout = False
                for ci in range(fe, min(fe + 3, len(window))):
                    if float(window[ci]["h"]) > flag_high:
                        breakout = True
                        break
                if not breakout:
                    continue

                # ── Trade levels ──────────────────────────────────────────────
                entry = round(flag_high + 0.02, 2)   # 2¢ above flag high
                stop  = round(flag_low  - 0.02, 2)   # Ross: "stop = low of pullback"
                risk  = entry - stop
                if risk < 0.05:
                    continue

                # Target: Ross's primary target = HIGH OF DAY retest
                # If HOD > entry, use it; otherwise use measured move
                if intraday_hod > entry:
                    target = round(intraday_hod, 2)
                else:
                    target = round(entry + pole_height, 2)  # measured move fallback

                # Pre-market high can also serve as a target if it's above entry
                if premarket_high and premarket_high > target:
                    target = round(premarket_high, 2)

                rr = (target - entry) / risk if risk > 0 else 0
                if rr < MIN_RR:
                    continue

                # Breakeven stop level = entry + 2¢ (move stop here after first fill)
                breakeven_stop = round(entry + 0.02, 2)

                candidate = {
                    "symbol":          sym,
                    "entry":           entry,
                    "stop":            stop,
                    "target":          target,
                    "breakeven_stop":  breakeven_stop,
                    "rr":              round(rr, 2),
                    "risk":            round(risk, 2),
                    "pole_height":     round(pole_height, 2),
                    "retrace_pct":     round(retrace * 100, 1),
                    "flag_vol_ratio":  round(flag_avg_vol / max(pole_avg_vol, 1), 2),
                    "vwap":            round(current_vwap, 2),
                    "hod":             round(intraday_hod, 2),
                    "premarket_high":  premarket_high,
                    "pole_bars":       pole_len,
                    "flag_bars":       flag_len,
                    "total_candles":   pole_len + flag_len,
                    "target_is_hod":   (target == round(intraday_hod, 2)),
                    "session":         session,
                }

                if best is None or rr > best["rr"]:
                    best = candidate

    if best:
        s = best
        hod_label = "HOD retest" if s["target_is_hod"] else "measured move"
        pmh_line  = (f" | PMH ${s['premarket_high']:.2f}"
                     if s["premarket_high"] else "")
        log("INFO",
            f"  [{sym}] ✅ BULL FLAG | "
            f"E=${s['entry']} SL=${s['stop']} T=${s['target']} ({hod_label}) "
            f"RR={s['rr']} | {s['total_candles']} candles "
            f"(pole {s['pole_bars']} flag {s['flag_bars']}) | "
            f"pullback {s['retrace_pct']}% flagvol {s['flag_vol_ratio']:.0%} | "
            f"VWAP ${s['vwap']} HOD ${s['hod']}{pmh_line}")
        return best

    # No pattern — log most informative reason
    log("INFO", f"  [{sym}] NO FLAG: no valid 5-7 candle bull flag pattern "
                f"(price ${current_price:.2f} HOD ${intraday_hod:.2f} "
                f"VWAP ${current_vwap:.2f})")
    return None

# ── Scanner ───────────────────────────────────────────────────────────────────
def scan_premarket(b_mode=False):
    """
    Polygon gainers scan filtered to Ross's exact 5 criteria:
    1. ≥5× relative volume (time-of-day adjusted)
    2. Gap up ≥10% (2% minimum / floor)
    3. Price $2–$20
    4. Float ≤10 million shares  ← NEW in v3
    5. News catalyst

    Logs ALL 5 criteria pass/fail for every candidate.
    """
    gap_thr   = B_GAP_MIN    if b_mode else GAP_MIN
    rvol_thr  = B_RVOL_MIN   if b_mode else RVOL_MIN
    float_thr = B_FLOAT_MAX  if b_mode else FLOAT_MAX
    mode      = "B-MODE" if b_mode else "A-QUALITY"

    log("INFO", f"=== SCAN [{mode}] gap≥{gap_thr}% rvol≥{rvol_thr}x "
                f"float≤{float_thr/1e6:.0f}M ${PRICE_LO}-${PRICE_HI} ===")

    data = GET(f"https://api.polygon.io/v2/snapshot/locale/us/markets/stocks/gainers"
               f"?apiKey={POLYGON_KEY}&include_otc=false")
    if not data:
        log("ERROR", "Polygon gainers API failed — check POLYGON_API_KEY")
        return []

    tickers = data.get("tickers", [])
    log("INFO", f"  Polygon returned {len(tickers)} gainers — applying filters:")

    # Estimate RVOL denominator based on time of day
    now       = now_et()
    open_time = now.replace(hour=9, minute=30, second=0, microsecond=0)
    is_premarket = now.hour < 9 or (now.hour == 9 and now.minute < 30)
    if is_premarket:
        mins_traded = None  # use raw vol/prev_vol ratio pre-market
    else:
        mins_traded = max(1, int((now - open_time).total_seconds() / 60))

    results = []
    for t in tickers:
        try:
            sym = t.get("ticker", "").upper()
            if not sym or len(sym) > 5:
                continue

            day  = t.get("day", {})
            prev = t.get("prevDay", {})
            pc   = float(prev.get("c") or 0)
            if pc <= 0:
                continue

            price = float(day.get("c") or 0)
            if price == 0:
                lt    = t.get("lastTrade", {})
                price = float(lt.get("p") or 0)
            if price == 0:
                price = pc + float(t.get("todaysChange") or 0)
            if price <= 0:
                continue

            vol      = int(day.get("v") or 0)
            prev_vol = int(prev.get("v") or 1)
            gap      = ((price - pc) / pc) * 100

            # Time-of-day adjusted RVOL (Ross's actual definition)
            if mins_traded is None:
                tod_rvol = vol / max(prev_vol, 1)  # raw pre-mkt ratio
            else:
                tod_rvol = calc_tod_rvol(vol, prev_vol, mins_traded)
            # Also compute raw RVOL for display
            raw_rvol = vol / max(prev_vol, 1)

            # ── Apply all 5 criteria with explicit pass/fail logging ──────────
            fails = []
            if price < PRICE_LO:     fails.append(f"price ${price:.2f}<${PRICE_LO}")
            if price > PRICE_HI:     fails.append(f"price ${price:.2f}>${PRICE_HI}")
            if gap < gap_thr:        fails.append(f"gap {gap:.1f}%<{gap_thr}%")
            # pre-mkt raw 0.5x ~ intraday 5x — scale threshold down
            effective_rvol_thr = rvol_thr / 10.0 if mins_traded is None else rvol_thr
            if tod_rvol < effective_rvol_thr:
                fails.append("rvol " + str(round(tod_rvol,2)) + "x<" + str(round(effective_rvol_thr,2)) + "x")

            if fails:
                log("DEBUG", f"  SKIP {sym}: {' | '.join(fails)}")
                continue

            # ── Float check (API call per candidate — only for passing stocks) ─
            share_float = get_float(sym)
            float_str   = f"{share_float/1e6:.1f}M" if share_float else "unknown"
            if share_float and share_float > float_thr:
                log("INFO", f"  SKIP {sym}: float {float_str} > "
                            f"{float_thr/1e6:.0f}M (too large)")
                continue
            if not share_float:
                log("INFO", f"  WARN {sym}: float unknown — including anyway "
                            f"(verify manually)")

            # ── Catalyst check ────────────────────────────────────────────────
            # Always a SOFT WARNING in the scanner — watchlist should cast the
            # widest net. The A-quality hard gate is enforced at TRADE TIME
            # in cycle(), not here. This way B-mode can still trade no-catalyst
            # stocks even if A-mode was active when the scan ran.
            has_news, headline = check_catalyst(sym)
            if not has_news:
                log("INFO", f"  WARN {sym}: no catalyst found "
                            f"— watchlisting anyway (gate enforced at trade time)")
                headline = "⚠️ No catalyst found — verify"

            results.append({
                "symbol":     sym,
                "price":      round(price, 2),
                "prev_close": round(pc, 2),
                "gap":        round(gap, 1),
                "rvol":       round(tod_rvol, 1),
                "raw_rvol":   round(raw_rvol, 1),
                "volume":     vol,
                "float":      share_float,
                "float_str":  float_str,
                "catalyst":   headline[:80],
                "has_news":   has_news,
            })

            # Criteria scorecard in log
            log("INFO",
                f"  ✅ CANDIDATE {sym}: ${price:.2f} | "
                f"gap {gap:.1f}% ✓ | "
                f"rvol {tod_rvol:.1f}x ({'✓' if tod_rvol >= rvol_thr else '⚠️'}) | "
                f"float {float_str} ({'✓' if share_float and share_float <= float_thr else '⚠️'}) | "
                f"news {'✓' if has_news else '⚠️'} | "
                f"{headline[:50]}")

        except Exception as ex:
            log("DEBUG", f"  Error parsing {t.get('ticker','?')}: {ex}")
            continue

    results.sort(key=lambda x: x["gap"], reverse=True)
    results = results[:5]
    log("INFO", f"=== SCAN DONE: {len(results)} candidates ===")
    return results

def merge_scan_results(fresh, label="scan"):
    """
    Merge new scan results into S.watchlist without dropping existing candidates.
    Also fetches pre-market highs for any new symbols.
    Returns list of newly added candidates (not already in watchlist or traded).
    """
    existing_syms = {w["symbol"] for w in S.watchlist}
    all_traded = S.traded_today | S.eh_traded_today
    new_found = [w for w in fresh if w["symbol"] not in existing_syms
                 and w["symbol"] not in all_traded]
    if new_found:
        S.watchlist.extend(new_found)
        for w in new_found:
            pmh = get_premarket_high(w["symbol"])
            if pmh:
                S.premarket_highs[w["symbol"]] = pmh
        log("INFO", f"  {label}: {len(new_found)} new candidate(s) added: "
                    f"{[w['symbol'] for w in new_found]}")
    return new_found

# ── State ─────────────────────────────────────────────────────────────────────
class State:
    def __init__(self):
        self.watchlist        = []
        self.premarket_highs  = {}     # sym -> float
        self.traded_today     = set()  # syms with submitted orders
        self.trades_today     = []     # list of trade detail dicts
        self.trade_count      = 0
        self.pnl              = 0.0
        self.scanned          = False
        self.halted           = False  # loss-limit auto-halt
        self.stopped          = False  # manual /stop
        self.core_cold_halted = False  # cold market halt (core window only)
        self.b_mode           = False
        self.cushion_built    = False  # True once 25% of daily target earned
        self.last_trade_time  = None   # datetime of last trade attempt
        self.date             = ""
        self.equity           = 0.0
        self.offset           = 0
        self.force_scan         = False
        self.start_time         = now_et().isoformat()
        self.last_heartbeat     = 0.0
        self.last_intraday_scan = 0.0  # unix ts of last intraday re-scan
        self.be_moved           = set() # order_ids with stop already at breakeven
        # Extended hours state
        self.eh_trade_count     = 0        # EH trades placed today
        self.eh_traded_today    = set()    # symbols traded in EH
        self.eh_trades_today    = []       # EH trade detail dicts
        self.eh_active_stops    = {}       # order_id -> stop info for software stops
        self.pm_last_scan       = 0.0      # unix ts of last premarket scan (7:00+ AM)
        self.pm_empty_notified  = False    # already sent "no candidates" message?
        self.eh_last_late_scan  = 0.0      # unix ts of last late-session re-scan

    def new_day(self, d):
        log("INFO", f"=== NEW DAY: {d} — state reset ===")
        self.watchlist       = []
        self.premarket_highs = {}
        self.traded_today    = set()
        self.trades_today    = []
        self.trade_count     = 0
        self.pnl             = 0.0
        self.scanned         = False
        self.halted          = False
        self.stopped         = False   # reset cold-market / manual stop
        self.core_cold_halted = False  # reset cold market core halt
        self.b_mode          = False   # reset B-mode for fresh day
        self.cushion_built   = False
        self.last_trade_time = None
        self.date            = d
        self.force_scan         = False
        self.last_intraday_scan = 0.0
        self.be_moved           = set()
        # Extended hours resets
        self.eh_trade_count     = 0
        self.eh_traded_today    = set()
        self.eh_trades_today    = []
        self.eh_active_stops    = {}
        self.pm_last_scan       = 0.0
        self.pm_empty_notified  = False
        self.eh_last_late_scan  = 0.0

    def save(self):
        try:
            with open(STATUS_FILE, "w") as f:
                json.dump({
                    "time":          now_et().isoformat(),
                    "equity":        self.equity,
                    "watchlist":     self.watchlist,
                    "trade_count":   self.trade_count,
                    "pnl":           round(self.pnl, 2),
                    "cushion_built": self.cushion_built,
                    "scanned":       self.scanned,
                    "halted":        self.halted,
                    "stopped":       self.stopped,
                    "b_mode":        self.b_mode,
                    "started":       self.start_time,
                }, f, indent=2)
        except Exception:
            pass
        try:
            with open(TRADES_FILE, "w") as f:
                json.dump(self.trades_today, f, indent=2)
        except Exception:
            pass

S = State()

# ── Commands ──────────────────────────────────────────────────────────────────
def handle_cmd(text, cid):
    if str(cid) != str(TG_CHAT):
        log("WARN", f"Ignored message from unauthorized chat {cid}")
        return
    cmd = (text.strip().split()[0] if text else "").lower()

    if cmd == "/status":
        try:
            with open(STATUS_FILE) as f:
                d = json.load(f)
        except Exception:
            d = {}
        pmh_str = ""
        if S.premarket_highs:
            pmh_str = "\nPMH: " + " | ".join(
                f"{k} ${v:.2f}" for k, v in S.premarket_highs.items())
        tg_send(
            f"📊 *GreenClaw v3 Status*\n"
            f"Time:    {d.get('time','?')}\n"
            f"Equity:  ${d.get('equity',0):,.2f}\n"
            f"Watchlist: {len(d.get('watchlist',[]))} symbols\n"
            f"Trades:  {d.get('trade_count',0)} / {MAX_TRADES}\n"
            f"P&L:     ${d.get('pnl',0):+.2f} (goal ${DAILY_TARGET:.0f})\n"
            f"Cushion: {'✅ built' if d.get('cushion_built') else '⏳ not yet'}\n"
            f"Scanned: {d.get('scanned',False)}\n"
            f"B-mode:  {d.get('b_mode',False)}\n"
            f"Halted:  {d.get('halted',False)}\n"
            f"Stopped: {d.get('stopped',False)}\n"
            f"Core cold halt: {S.core_cold_halted}\n"
            f"Dry-run: {'🔵 ON' if DRY_RUN else '🟢 OFF'}\n"
            f"Extended hours: {'🌙 ON' if EXTENDED_HOURS else '⚪ OFF'}"
            + (f"\n  EH trades: {S.eh_trade_count}/{EH_MAX_TRADES}"
               f" | active stops: {len(S.eh_active_stops)}"
               if EXTENDED_HOURS else "") +
            f"\nNext rescan: every {INTRADAY_SCAN_MINS}min in 9:35–11ET"
            + pmh_str)

    elif cmd == "/watchlist":
        if S.watchlist:
            lines = []
            for w in S.watchlist:
                pmh   = S.premarket_highs.get(w["symbol"])
                pmh_s = f" PMH ${pmh:.2f}" if pmh else ""
                news_icon = "📰" if w.get("has_news") else "⚠️"
                lines.append(
                    f"  *{w['symbol']}* ${w['price']:.2f} "
                    f"gap {w['gap']}% rvol {w['rvol']}x "
                    f"float {w.get('float_str','?')}{pmh_s}\n"
                    f"    {news_icon} {w.get('catalyst','?')[:60]}")
            tg_send("📋 *Watchlist*\n" + "\n".join(lines))
        else:
            tg_send("📋 Watchlist empty")

    elif cmd == "/trades":
        if S.trades_today:
            lines = []
            for tr in S.trades_today:
                lines.append(
                    f"  *{tr['symbol']}* {tr['qty']}sh @ ${tr['entry']:.2f}\n"
                    f"    SL ${tr['stop']:.2f} → BE ${tr['breakeven_stop']:.2f} "
                    f"TP ${tr['target']:.2f} ({tr.get('target_type','?')})\n"
                    f"    RR {tr['rr']} | size: {tr.get('size_label','?')} | {tr['time']}")
            tg_send("🗂 *Today's Trades*\n" + "\n".join(lines))
        else:
            tg_send("🗂 No trades yet today")

    elif cmd == "/logs":
        try:
            with open(LOG_FILE) as f:
                lines = f.readlines()[-20:]
            tg_send("📜 *Last 20 lines*\n```\n" + "".join(lines) + "```")
        except Exception:
            tg_send("Log file not found")

    elif cmd == "/scan":
        S.force_scan = True
        # Will auto-resume if candidates found (see cycle())
        tg_send("🔄 Manual scan queued (~30 sec)")

    elif cmd == "/stop":
        S.stopped = True
        S.save()
        tg_send(f"⏹ *Trading STOPPED*\n"
                f"Trades: {S.trade_count} | P&L: ${S.pnl:+.2f}\n"
                f"Send /resume to restart")

    elif cmd == "/resume":
        S.stopped = False
        S.halted  = False
        S.core_cold_halted = False
        S.save()
        tg_send("▶ *Trading RESUMED*")

    elif cmd == "/bmode":
        S.b_mode = not S.b_mode
        st = "ENABLED" if S.b_mode else "DISABLED"
        tg_send(f"⚙️ B-Mode *{st}*\n"
                + (f"Criteria: gap≥{B_GAP_MIN}% rvol≥{B_RVOL_MIN}x "
                   f"float≤{B_FLOAT_MAX/1e6:.0f}M | max 1 trade"
                   if S.b_mode else
                   f"Back to A-quality: gap≥{GAP_MIN}% rvol≥{RVOL_MIN}x "
                   f"float≤{FLOAT_MAX/1e6:.0f}M"))
        log("INFO", f"B-Mode {st}")

    elif cmd == "/extended":
        # Toggle extended hours mode at runtime
        import sys as _sys
        _mod = _sys.modules[__name__]
        _mod.EXTENDED_HOURS = not EXTENDED_HOURS
        # Re-read from module to get the updated value
        _eh = _mod.EXTENDED_HOURS
        st = "ENABLED" if _eh else "DISABLED"
        log("INFO", f"Extended hours {st} via Telegram command")
        tg_send(f"🌙 *Extended Hours {st}*\n"
                + (f"Early session: {EH_EARLY_START[0]}:{EH_EARLY_START[1]:02d}–"
                   f"{EH_EARLY_END[0]}:{EH_EARLY_END[1]:02d} ET\n"
                   f"Late session: {EH_LATE_START[0]}:{EH_LATE_START[1]:02d}–"
                   f"{EH_LATE_END[0]}:{EH_LATE_END[1]:02d} ET\n"
                   f"Max EH trades: {EH_MAX_TRADES}/day\n"
                   f"Position size: {EH_SIZE_MULT:.0%} of normal\n"
                   f"⚠️ Stop-loss is software-managed (no broker-side stop)"
                   if _eh else
                   "Back to core window only (9:35–11:00 ET)"))

    elif cmd == "/dryrun":
        # Toggle dry-run mode at runtime (overrides env var for this session)
        import builtins
        # We modify the module-level DRY_RUN by using a mutable wrapper in S
        S.dry_run_override = not getattr(S, "dry_run_override", DRY_RUN)
        # Patch the global for this process
        import sys as _sys
        _mod = _sys.modules[__name__]
        _mod.DRY_RUN = S.dry_run_override
        st = "ENABLED" if DRY_RUN else "DISABLED"
        log("INFO", f"Dry-run mode {st} via Telegram command")
        tg_send(f"🔵 *Dry-run {st}*\n"
                + ("No real orders will be placed — simulating only"
                   if DRY_RUN else
                   "Live trading mode — real orders will be placed"))

    elif cmd == "/cancel":
        orders = get_orders()
        if orders:
            c = sum(1 for o in orders if alp_del(f"/v2/orders/{o['id']}"))
            tg_send(f"🚫 Cancelled {c} open order(s)")
        else:
            tg_send("No open orders")

    elif cmd == "/help":
        tg_send(
            "🤖 *GreenClaw v3 Commands*\n"
            "/status    — equity, P&L, cushion, state\n"
            "/watchlist — candidates with float + catalyst\n"
            "/trades    — today's entries with all levels\n"
            "/logs      — last 20 log lines\n"
            "/scan      — force manual re-scan\n"
            "/stop      — halt all trading\n"
            "/resume    — resume after stop or halt\n"
            "/cancel    — cancel open orders\n"
            "/dryrun    — toggle dry-run mode (no real orders)\n"
            "/extended  — toggle extended hours (late session)\n"
            "/orders    — show open orders from Alpaca\n"
            "/report    — daily summary (trades + watchlist)\n"
            "/bmode     — toggle B-mode (looser criteria)\n"
            "/help      — this message\n\n"
            f"*A-quality*: gap≥{GAP_MIN}% rvol≥{RVOL_MIN}x "
            f"float≤{FLOAT_MAX/1e6:.0f}M ${PRICE_LO}-${PRICE_HI}\n"
            f"*Sizing*: quarter size until cushion "
            f"(${DAILY_TARGET*CUSHION_PCT:.0f}), then full\n"
            f"*Daily goal*: ${DAILY_TARGET:.0f} | "
            f"*Max loss*: ${abs(MAX_LOSS):.0f}\n"
            f"*Extended hours*: {'🌙 ON' if EXTENDED_HOURS else '⚪ OFF'}"
            + (f" | late {EH_LATE_START[0]}:{EH_LATE_START[1]:02d}–"
               f"{EH_LATE_END[0]}:{EH_LATE_END[1]:02d} ET, "
               f"{EH_SIZE_MULT:.0%} size, max {EH_MAX_TRADES}"
               if EXTENDED_HOURS else ""))

    elif cmd == "/orders":
        orders = get_orders()
        if not orders:
            tg_send("📋 No open orders")
        else:
            lines_out = []
            for o in orders:
                legs = o.get("legs", [])
                leg_summary = ""
                if legs:
                    for lg in legs:
                        lt = lg.get("type", "?")
                        lp = lg.get("limit_price") or lg.get("stop_price", "?")
                        ls = lg.get("status", "?")
                        leg_summary += f"  └ {lt} @ ${lp} [{ls}]\n"
                lines_out.append(
                    f"*{o.get('symbol','?')}* {o.get('qty','?')}sh "
                    f"@ ${o.get('limit_price','mkt')} "
                    f"[{o.get('status','?')}]\n"
                    + leg_summary)
            tg_send("📋 *Open Orders*\n" + "\n".join(lines_out))

    elif cmd == "/report":
        try:
            with open(STATUS_FILE) as f:
                d = json.load(f)
        except Exception:
            d = {}
        trades  = S.trades_today or []
        wl      = d.get("watchlist", [])
        pnl     = d.get("pnl", 0.0)
        eq      = d.get("equity", 0.0)
        outcome = "Green" if pnl > 0 else ("Red" if pnl < 0 else "Flat")
        # Trade lines
        if trades:
            tl = []
            for tr in trades:
                tl.append("  " + tr["symbol"]
                          + " " + str(tr["qty"]) + "sh"
                          + " @ $" + str(tr["entry"])
                          + " TP $" + str(tr["target"])
                          + " SL $" + str(tr["stop"])
                          + " RR " + str(tr["rr"])
                          + " " + tr.get("target_type", "?"))
            tlines = "\n".join(tl)
        else:
            tlines = "  No trades today"
        # Watchlist lines
        if wl:
            wl_list = []
            for w in wl:
                wl_list.append("  " + w["symbol"]
                               + " $" + str(w["price"])
                               + " gap " + str(w["gap"]) + "%"
                               + " rvol " + str(w["rvol"]) + "x"
                               + " float " + w.get("float_str", "?"))
            wlines = "\n".join(wl_list)
        else:
            wlines = "  No candidates"
        msg = ("*Daily Report — " + now_et().strftime("%a %b %d") + "*\n"
               + "Result: " + outcome
               + " | P&L: $" + f"{pnl:+.2f}" + "\n"
               + "Equity: $" + f"{eq:,.2f}" + "\n"
               + "Trades: " + str(len(trades)) + "/" + str(MAX_TRADES) + "\n"
               + "Cushion: " + ("built" if d.get("cushion_built") else "not yet") + "\n"
               + "\nWatchlist (" + str(len(wl)) + "):\n" + wlines + "\n"
               + "\nTrades:\n" + tlines + "\n"
               + "\n_/logs for full audit trail_")
        tg_send(msg)

    else:
        log("DEBUG", f"Unknown command: {cmd}")

# ── Main trading cycle ────────────────────────────────────────────────────────
def startup():
    log("INFO", "=" * 60)
    log("INFO", "GreenClaw v3 starting")
    log("INFO", f"  Python:        {sys.version.split()[0]}")
    log("INFO", f"  PID:           {os.getpid()}")
    log("INFO", f"  Polygon:       {'✅' if POLYGON_KEY else '❌ MISSING'}")
    log("INFO", f"  Alpaca:        {'✅' if ALPACA_KEY  else '❌ MISSING'}")
    log("INFO", f"  Telegram:      {'✅' if TG_TOKEN    else '❌ MISSING'}")
    log("INFO", f"  DRY RUN:       {'🔵 ON — no real orders' if DRY_RUN else '🟢 LIVE trading'}")
    S.equity = get_equity()
    log("INFO", f"  Equity:        ${S.equity:,.2f}")
    log("INFO", f"  Risk/trade:    {RISK_PCT*100}% = "
                f"${S.equity * RISK_PCT:.0f} (quarter: "
                f"${S.equity * RISK_PCT * 0.25:.0f})")
    log("INFO", f"  Daily goal:    ${DAILY_TARGET:.0f}")
    log("INFO", f"  Daily max loss:${abs(MAX_LOSS):.0f}")
    log("INFO", f"  Float max:     {FLOAT_MAX/1e6:.0f}M shares")
    log("INFO", f"  Gap min:       {GAP_MIN}%")
    log("INFO", f"  RVOL min:      {RVOL_MIN}x (time-of-day adjusted)")
    log("INFO", f"  Time:          {now_et().strftime('%Y-%m-%d %H:%M:%S ET')}")
    log("INFO", "=" * 60)

    try:
        with open(PID_FILE, "w") as f:
            f.write(str(os.getpid()))
    except Exception:
        pass

    tg_send(
        f"🟢 *GreenClaw v3 Started*\n"
        f"Equity: ${S.equity:,.2f}\n"
        f"Risk/trade (quarter): ${S.equity * RISK_PCT * 0.25:.0f}\n"
        f"Risk/trade (full):    ${S.equity * RISK_PCT:.0f}\n"
        f"Daily goal / max loss: ${DAILY_TARGET:.0f}\n"
        f"Float filter: ≤{FLOAT_MAX/1e6:.0f}M shares\n"
        f"Time: {now_et().strftime('%Y-%m-%d %H:%M:%S ET')}\n"
        f"Send /help for commands\n"
        + (f"⚠️ *DRY-RUN MODE* — no orders will be placed\n" if DRY_RUN else "")
        + (f"🌙 *EXTENDED HOURS ON* — late session "
           f"{EH_LATE_START[0]}:{EH_LATE_START[1]:02d}–"
           f"{EH_LATE_END[0]}:{EH_LATE_END[1]:02d} ET, "
           f"{EH_SIZE_MULT:.0%} size, software stops\n"
           if EXTENDED_HOURS else ""))
    S.save()


def cycle():
    t      = now_et()
    hh, mm = t.hour, t.minute
    today  = t.strftime("%Y-%m-%d")
    is_wd  = (t.weekday() < 5)

    # ── Day rollover ──────────────────────────────────────────────────────────
    if S.date != today:
        S.new_day(today)

    # ── Heartbeat (every 30 min, outside market hours) ────────────────────────
    now_ts = time.time()
    if (hh < 9 or hh >= 16) and (now_ts - S.last_heartbeat > 1800):
        log("INFO", f"Heartbeat | {t.strftime('%H:%M ET')} | "
                    f"equity ${S.equity:,.2f}")
        S.last_heartbeat = now_ts

    # ── Core scan at 9:15 ET (or forced) ────────────────────────────────────
    # Merges new candidates into existing watchlist (premarket scan may have
    # already built one). Never overwrites — only adds new symbols.
    scan_time = is_wd and hh == 9 and mm >= 15 and mm < 20
    if (scan_time and not S.scanned) or S.force_scan:
        is_forced = S.force_scan   # remember if this was a manual /scan
        fresh = scan_premarket(b_mode=S.b_mode)

        # Merge instead of overwrite — premarket watchlist is preserved
        if not S.watchlist:
            S.watchlist = fresh
            for w in S.watchlist:
                pmh = get_premarket_high(w["symbol"])
                if pmh:
                    S.premarket_highs[w["symbol"]] = pmh
        else:
            merge_scan_results(fresh, label="Core 9:15")

        S.scanned    = True
        S.force_scan = False
        S.equity     = get_equity()
        sheets_push({
            "type":       "scan",
            "date":       now_et().strftime("%Y-%m-%d"),
            "candidates": len(S.watchlist),
            "watchlist":  S.watchlist,
            "b_mode":     S.b_mode,
            "equity":     S.equity,
        })

        # ── Key fix: if a manual /scan finds candidates, un-halt the bot ──
        # This is what should have happened today with ELAB/ASTC/EEIQ/QNTM/KZR
        if S.watchlist and is_forced:
            if S.stopped or S.halted or S.core_cold_halted:
                S.stopped = False
                S.halted  = False
                S.core_cold_halted = False
                log("INFO", f"Manual scan found {len(S.watchlist)} candidate(s) "
                            f"— resuming from halt/stop")
                tg_send(f"▶ *Resumed* — manual scan found "
                        f"{len(S.watchlist)} candidate(s)")
            # Reset cold-market timer so bot gets a fresh 30-min window
            S.last_trade_time = now_et()
            log("INFO", "Cold-market timer reset after manual scan")

        if S.watchlist:
            # Fetch pre-market highs for all candidates
            log("INFO", "Fetching pre-market highs...")
            for w in S.watchlist:
                pmh = get_premarket_high(w["symbol"])
                if pmh:
                    S.premarket_highs[w["symbol"]] = pmh
                    log("INFO", f"  {w['symbol']} PMH ${pmh:.2f}")

            lines = []
            for w in S.watchlist:
                pmh = S.premarket_highs.get(w["symbol"])
                lines.append(
                    f"  *{w['symbol']}* ${w['price']:.2f} | "
                    f"gap {w['gap']}% | rvol {w['rvol']}x | "
                    f"float {w.get('float_str','?')}"
                    + (f" | PMH ${pmh:.2f}" if pmh else "") + "\n"
                    f"    {'📰' if w.get('has_news') else '⚠️'} "
                    f"{w.get('catalyst','')[:60]}")

            tg_send(
                f"🔍 *PRE-MARKET SCAN"
                f"{' (B-MODE)' if S.b_mode else ''}*\n"
                + "\n".join(lines)
                + f"\n\nMonitoring from 9:35 ET\n"
                f"Equity: ${S.equity:,.2f} | "
                f"Quarter size: ${S.equity*RISK_PCT*0.25:.0f}/trade")
        else:
            tg_send(
                f"🔍 *SCAN — No candidates*\n"
                f"Criteria: gap≥{GAP_MIN if not S.b_mode else B_GAP_MIN}% "
                f"rvol≥{RVOL_MIN if not S.b_mode else B_RVOL_MIN}x "
                f"float≤{(FLOAT_MAX if not S.b_mode else B_FLOAT_MAX)/1e6:.0f}M\n"
                f"Send /bmode for looser B-mode criteria\n"
                f"Send /scan at 9:15 to re-scan pre-market")
        S.save()

    # ── B-mode suggestion at 10:00 if no A-quality ───────────────────────────
    if (is_wd and hh == 10 and mm == 0
            and S.scanned and not S.watchlist and not S.b_mode):
        tg_send("⚠️ No A-quality candidates by 10:00 ET.\n"
                "Send /bmode to try B-mode (gap≥2% rvol≥4x float≤15M)\n"
                "Ross rule: max 1 B-mode trade, still need 2:1 RR.")

    # ── Intraday re-scan every INTRADAY_SCAN_MINS during trading window ───────
    # Catches stocks that emerge mid-session (e.g. ELAB/ASTC found at 10:40 ET
    # today despite zero candidates at 9:15 ET pre-market scan)
    in_trading_window = (is_wd and
                         ((hh == 9 and mm >= 35) or hh == 10
                          or (hh == 11 and mm == 0)))
    if (in_trading_window
            and S.scanned
            and not S.stopped
            and not S.halted
            and S.trade_count < MAX_TRADES
            and (now_ts - S.last_intraday_scan) >= INTRADAY_SCAN_MINS * 60):

        S.last_intraday_scan = now_ts
        log("INFO", f"Intraday re-scan at {t.strftime('%H:%M ET')}...")
        fresh = scan_premarket(b_mode=S.b_mode)

        # Merge new symbols into watchlist (don't drop existing ones)
        existing_syms = {w["symbol"] for w in S.watchlist}
        new_found = [w for w in fresh if w["symbol"] not in existing_syms
                     and w["symbol"] not in S.traded_today]

        if new_found:
            S.watchlist.extend(new_found)
            log("INFO", f"  Intraday scan: {len(new_found)} new candidate(s) added: "
                        f"{[w['symbol'] for w in new_found]}")

            # Fetch pre-market highs for new candidates
            for w in new_found:
                pmh = get_premarket_high(w["symbol"])
                if pmh:
                    S.premarket_highs[w["symbol"]] = pmh

            # Notify via Telegram
            lines_out = []
            for w in new_found:
                pmh = S.premarket_highs.get(w["symbol"])
                lines_out.append(
                    f"  *{w['symbol']}* ${w['price']:.2f} | "
                    f"gap {w['gap']}% | rvol {w['rvol']}x | "
                    f"float {w.get('float_str','?')}"
                    + (f" | PMH ${pmh:.2f}" if pmh else "") + "\n"
                    f"    {'📰' if w.get('has_news') else '⚠️'} "
                    f"{w.get('catalyst','')[:60]}")
            plural = "s" if len(new_found) > 1 else ""
            tg_send(
                f"📡 *INTRADAY SCAN — {len(new_found)} new candidate{plural}*\n"
                + "\n".join(lines_out)
                + f"\nTotal watchlist: {len(S.watchlist)}")

            # If bot was halted by cold-market logic, resume it
            if S.stopped or S.core_cold_halted:
                S.stopped = False
                S.core_cold_halted = False
                log("INFO", "Intraday scan found candidates — resuming from cold-market halt")
                tg_send("▶ *Resumed* — intraday scan found new candidates")

            # Reset cold-market timer
            S.last_trade_time = now_et()

            # Push to Sheets
            sheets_push({
                "type":       "scan",
                "date":       now_et().strftime("%Y-%m-%d"),
                "candidates": len(fresh),
                "watchlist":  fresh,
                "b_mode":     S.b_mode,
                "equity":     S.equity,
            })
            S.save()
        else:
            log("DEBUG", f"Intraday re-scan: no new candidates "
                         f"(total scanned: {len(fresh)})")

    # ── Cold market auto-stop (CORE WINDOW ONLY) ────────────────────────────
    # Ross: "if I haven't picked up a trade in 30 minutes I just give up"
    # Note: we use last_trade_time as the reset anchor — intraday scans that
    # find new candidates reset this timer, giving a fresh 30-min window.
    # IMPORTANT: this only sets S.core_cold_halted, NOT S.stopped.
    # Extended hours sessions are not affected by the cold market rule —
    # the whole point of EH mode is to find setups on cold days.
    if (is_wd and hh >= 9 and hh < 11
            and S.scanned
            and S.trade_count == 0
            and not S.core_cold_halted and not S.stopped and not S.halted):
        # Anchor: either last reset time or 9:35 ET open
        first_monitor = t.replace(hour=9, minute=35, second=0, microsecond=0)
        anchor = S.last_trade_time if S.last_trade_time else (
            first_monitor if t > first_monitor else None)
        if anchor and t > first_monitor:
            elapsed = (t - anchor).total_seconds() / 60
            if elapsed >= NO_TRADE_HALT_MINS:
                S.core_cold_halted = True
                log("INFO", "Cold market: no setup in 30 min — core window stopping")
                tg_send(f"🥶 *Cold market — core window stopped*\n"
                        f"No valid setup found in {NO_TRADE_HALT_MINS} min.\n"
                        + (f"Extended hours will continue scanning.\n"
                           if EXTENDED_HOURS else "")
                        + f"Send /resume to override.")
                S.save()

    # ── Active trading: 9:35–11:00 ET ────────────────────────────────────────
    in_window = (is_wd and
                 ((hh == 9 and mm >= 35) or hh == 10
                  or (hh == 11 and mm == 0)))

    if in_window and S.watchlist and not S.halted and not S.stopped and not S.core_cold_halted:

        # ── Refresh live P&L from Alpaca each cycle ──────────────────────
        # Without this, S.pnl stays 0.0 all session and cushion never
        # builds / loss limit never fires (diagnosed bug #7).
        live_pnl, live_eq = get_live_pnl()
        if live_pnl is not None:
            S.pnl    = live_pnl
            S.equity = live_eq

        # Daily loss limit check
        if S.pnl <= MAX_LOSS:
            S.halted = True
            tg_send(f"🛑 *DAILY LOSS LIMIT HIT*\n"
                    f"P&L: ${S.pnl:+.2f} | Limit: ${MAX_LOSS:.0f}\n"
                    f"Trading halted. Send /resume to override.")
            log("WARN", f"Loss limit hit: ${S.pnl:.2f}")
            S.save()
            return

        # Max trades per day
        if S.trade_count >= MAX_TRADES:
            return

        # B-mode: max 1 trade
        if S.b_mode and S.trade_count >= 1:
            return

        # Daily target hit — half size to protect green day
        # (Ross: "once I've hit my target I reduce size")
        protecting_gains = (S.pnl >= DAILY_TARGET)
        if protecting_gains and mm == 0:
            log("INFO", f"Daily target ${DAILY_TARGET:.0f} hit — "
                        f"half size for remainder of day")

        # Check if cushion is built (25% of daily target)
        cushion_threshold = DAILY_TARGET * CUSHION_PCT
        if not S.cushion_built and S.pnl >= cushion_threshold:
            S.cushion_built = True
            tg_send(f"💪 *Cushion built!* P&L ${S.pnl:+.2f} ≥ "
                    f"${cushion_threshold:.0f}\nScaling to *full size* now.")
            log("INFO", f"Cushion built at ${S.pnl:.2f} — going full size")

        # Open positions — skip symbols already held
        positions  = get_positions()
        held_syms  = {p.get("symbol", "") for p in (positions or [])}

        for w in S.watchlist:
            sym = w["symbol"]
            if sym in S.traded_today:
                continue
            if sym in held_syms:
                continue

            pmh = S.premarket_highs.get(sym)
            sig = detect_flag(sym, premarket_high=pmh)
            if not sig:
                continue

            # ── A-quality catalyst gate (enforced at trade time, not scan time) ─
            # Ross: "my best trades are when the catalyst is obvious"
            # Ross: "there must be a headline that justifies why the stock is moving"
            if not S.b_mode and not w.get("has_news"):
                log("INFO", f"  [{sym}] SKIP: no catalyst (A-quality requires news)")
                continue

            # Position size (quarter until cushion, full after)
            effective_equity = S.equity
            risk_dollars     = effective_equity * RISK_PCT
            if not S.cushion_built:
                risk_dollars *= 0.25  # quarter size
                size_label    = "quarter (building cushion)"
            elif protecting_gains:
                risk_dollars *= 0.50  # half size to protect green day
                size_label    = "half (protecting gains)"
            else:
                size_label    = "full"

            qty = int(risk_dollars / sig["risk"]) if sig["risk"] > 0 else 0
            max_qty = int(effective_equity * 0.25 / sig["entry"])
            qty = min(qty, max_qty)
            qty = max(qty, 1)

            # HOD / target type label
            target_type = "HOD retest" if sig.get("target_is_hod") else "measured move"

            # ── Alert before order ────────────────────────────────────────────
            pmh_line = (f"\nPMH: ${pmh:.2f}" if pmh else "")
            float_str = w.get("float_str", "unknown")
            mode_label = "B-MODE" if S.b_mode else "A-QUALITY"
            tg_send(
                f"🚩 *BULL FLAG [{mode_label}]: {sym}*\n"
                f"Entry:  ${sig['entry']:.2f}\n"
                f"Stop:   ${sig['stop']:.2f}  (risk ${sig['risk']:.2f}/sh)\n"
                f"Target: ${sig['target']:.2f}  ({target_type})\n"
                f"BE stop: ${sig['breakeven_stop']:.2f}  ← move stop here after fill\n"
                f"R:R:    {sig['rr']}:1\n"
                f"Shares: {qty}  | Size: {size_label}\n"
                f"Total risk: ${qty * sig['risk']:.0f}\n"
                f"─────────────────\n"
                f"Pattern: {sig['total_candles']} candles "
                f"(pole {sig['pole_bars']} + flag {sig['flag_bars']})\n"
                f"Pullback: {sig['retrace_pct']}% | "
                f"Flag vol: {sig['flag_vol_ratio']:.0%} of pole\n"
                f"VWAP: ${sig['vwap']:.2f} | HOD: ${sig['hod']:.2f} | "
                f"Float: {float_str}"
                + pmh_line)

            r = place_bracket(sym, qty, sig["entry"], sig["stop"], sig["target"])

            if r and r.get("id"):
                S.traded_today.add(sym)
                S.trade_count += 1
                S.last_trade_time = now_et()

                S.trades_today.append({
                    "symbol":         sym,
                    "qty":            qty,
                    "entry":          sig["entry"],
                    "stop":           sig["stop"],
                    "breakeven_stop": sig["breakeven_stop"],
                    "target":         sig["target"],
                    "target_type":    target_type,
                    "rr":             sig["rr"],
                    "risk":           sig["risk"],
                    "order_id":       r["id"],
                    "size_label":     size_label,
                    "session":        "core",
                    "time":           now_et().strftime("%H:%M ET"),
                    "vwap":           sig["vwap"],
                    "hod":            sig["hod"],
                    "pole_height":    sig["pole_height"],
                    "float":          w.get("float_str"),
                    "catalyst":       w.get("catalyst"),
                    "b_mode":         S.b_mode,
                    "dry_run":        r.get("dry_run", False),
                })
                # Push to Google Sheets
                sheets_push({
                    "type":       "trade",
                    "date":       now_et().strftime("%Y-%m-%d"),
                    "session":    "core",
                    "symbol":     sym,
                    "qty":        qty,
                    "entry":      sig["entry"],
                    "stop":       sig["stop"],
                    "target":     sig["target"],
                    "target_type":target_type,
                    "rr":         sig["rr"],
                    "risk":       sig["risk"],
                    "total_risk": round(qty * sig["risk"], 2),
                    "size_label": size_label,
                    "vwap":       sig["vwap"],
                    "hod":        sig["hod"],
                    "pole_height":sig["pole_height"],
                    "float":      w.get("float_str"),
                    "catalyst":   w.get("catalyst"),
                    "b_mode":     S.b_mode,
                    "equity":     S.equity,
                    "trade_num":  S.trade_count,
                    "order_id":   r["id"],
                })
                S.save()
                log("INFO", f"  [{sym}] Trade #{S.trade_count} recorded "
                            f"| size={size_label}")

    # ── Breakeven stop management ─────────────────────────────────────────────
    # Runs every cycle during trading hours if we have trades.
    # Checks if parent buy orders are filled and moves stop to breakeven.
    # Ross: "Once I'm in, I move my stop to breakeven as fast as possible."
    if (in_window or (is_wd and hh >= 9 and hh < 16)) and S.trades_today:
        newly_moved = manage_breakeven_stops(S.trades_today, S.be_moved)
        if newly_moved:
            S.be_moved.update(newly_moved)
            S.save()

    # ── Premarket continuous scan (7:00 AM+ every 15 min) ───────────────────
    # ALWAYS runs (not gated on EXTENDED_HOURS) — earlier watchlist is better
    # for everyone. Merges new candidates into watchlist (never overwrites).
    # Fetches PMH for each new candidate automatically.
    pm_scan_window = (is_wd
                      and ((hh == PM_SCAN_START[0] and mm >= PM_SCAN_START[1])
                           or (hh > PM_SCAN_START[0] and hh < 9)
                           or (hh == 9 and mm < 15)))  # stop at 9:15 when core scan takes over

    if (pm_scan_window
            and (now_ts - S.pm_last_scan) >= PM_SCAN_INTERVAL * 60):
        S.pm_last_scan = now_ts
        scan_label = f"PM {t.strftime('%H:%M ET')}"
        log("INFO", f"Premarket scan at {t.strftime('%H:%M ET')}...")
        fresh = scan_premarket(b_mode=S.b_mode)

        if not S.watchlist:
            # First scan of the day — set watchlist directly
            S.watchlist = fresh
            for w in S.watchlist:
                pmh = get_premarket_high(w["symbol"])
                if pmh:
                    S.premarket_highs[w["symbol"]] = pmh
            new_found = fresh
        else:
            # Subsequent scans — merge new candidates
            new_found = merge_scan_results(fresh, label=scan_label)

        S.equity = get_equity()

        if new_found:
            lines_out = []
            for w in new_found:
                pmh = S.premarket_highs.get(w["symbol"])
                lines_out.append(
                    f"  *{w['symbol']}* ${w['price']:.2f} | "
                    f"gap {w['gap']}% | rvol {w['rvol']}x | "
                    f"float {w.get('float_str','?')}"
                    + (f" | PMH ${pmh:.2f}" if pmh else "") + "\n"
                    f"    {'📰' if w.get('has_news') else '⚠️'} "
                    f"{w.get('catalyst','')[:60]}")
            is_first = (len(S.watchlist) == len(new_found))
            tg_send(
                f"🌅 *PREMARKET SCAN ({t.strftime('%H:%M ET')})*\n"
                + "\n".join(lines_out)
                + (f"\nTotal watchlist: {len(S.watchlist)}" if not is_first else "")
                + f"\nEquity: ${S.equity:,.2f}")
            S.pm_empty_notified = False  # reset so we notify if it goes empty again
        elif not S.watchlist and not S.pm_empty_notified:
            # First empty scan — notify ONCE, then stay silent until candidates found
            tg_send(f"🌅 *PREMARKET SCAN — No candidates yet*\n"
                    f"Re-scanning every {PM_SCAN_INTERVAL}min until 9:15 ET\n"
                    f"(Notifications silenced until candidates found)")
            S.pm_empty_notified = True
        else:
            # Subsequent empty scans — log only, no Telegram spam
            log("DEBUG", f"Premarket scan: no new candidates (silent)")

        sheets_push({
            "type": "scan", "session": "premarket",
            "date": now_et().strftime("%Y-%m-%d"),
            "time": t.strftime("%H:%M ET"),
            "candidates": len(fresh),
            "new_found": len(new_found) if new_found else 0,
            "watchlist_total": len(S.watchlist),
            "b_mode": S.b_mode, "equity": S.equity,
        })
        S.save()

    # ── Extended Hours: Early session trading (8:00–9:14 ET) ─────────────────
    # Uses premarket bars from IEX/Alpaca for bull flag detection.
    # Same criteria, half size, software stops, max 1 EH trade/day.
    eh_early_window = (EXTENDED_HOURS and is_wd
                       and ((hh == EH_EARLY_START[0] and mm >= EH_EARLY_START[1])
                            or (hh > EH_EARLY_START[0] and hh < EH_EARLY_END[0])
                            or (hh == EH_EARLY_END[0] and mm <= EH_EARLY_END[1])))

    if (eh_early_window
            and S.watchlist
            and not S.halted and not S.stopped
            and S.eh_trade_count < EH_MAX_TRADES
            and S.trade_count < MAX_TRADES):

        # Refresh live P&L
        live_pnl, live_eq = get_live_pnl()
        if live_pnl is not None:
            S.pnl    = live_pnl
            S.equity = live_eq

        # Daily loss limit (shared)
        if S.pnl <= MAX_LOSS:
            S.halted = True
            tg_send(f"🛑 *DAILY LOSS LIMIT HIT (during EH early)*\n"
                    f"P&L: ${S.pnl:+.2f} | Limit: ${MAX_LOSS:.0f}\n"
                    f"All trading halted.")
            S.save()
        else:
            positions = get_positions()
            held_syms = {p.get("symbol", "") for p in (positions or [])}
            all_traded = S.traded_today | S.eh_traded_today

            for w in S.watchlist:
                sym = w["symbol"]
                if sym in all_traded or sym in held_syms:
                    continue
                if S.eh_trade_count >= EH_MAX_TRADES:
                    break
                if S.trade_count >= MAX_TRADES:
                    break

                pmh = S.premarket_highs.get(sym)
                sig = detect_flag(sym, premarket_high=pmh, session="early")
                if not sig:
                    continue

                # A-quality catalyst gate at trade time
                if not S.b_mode and not w.get("has_news"):
                    log("INFO", f"  [{sym}] EH SKIP: no catalyst (A-quality requires news)")
                    continue

                # Half position sizing for EH trades
                effective_equity = S.equity
                risk_dollars = effective_equity * RISK_PCT * EH_SIZE_MULT
                if not S.cushion_built:
                    risk_dollars *= 0.25
                    size_label = f"EH quarter (building cushion, {EH_SIZE_MULT:.0%}x)"
                elif S.pnl >= DAILY_TARGET:
                    risk_dollars *= 0.50
                    size_label = f"EH half (protecting gains, {EH_SIZE_MULT:.0%}x)"
                else:
                    size_label = f"EH half ({EH_SIZE_MULT:.0%}x base)"

                qty = int(risk_dollars / sig["risk"]) if sig["risk"] > 0 else 0
                max_qty = int(effective_equity * 0.25 / sig["entry"])
                qty = min(qty, max_qty)
                qty = max(qty, 1)

                target_type = "HOD retest" if sig.get("target_is_hod") else "measured move"

                tg_send(
                    f"🌅 *EH BULL FLAG [{'B-MODE' if S.b_mode else 'A-QUALITY'}]: {sym}*\n"
                    f"Session: EARLY ({t.strftime('%H:%M ET')})\n"
                    f"Entry:  ${sig['entry']:.2f}\n"
                    f"Stop:   ${sig['stop']:.2f}  (⚠️ SOFTWARE stop)\n"
                    f"Target: ${sig['target']:.2f}  ({target_type})\n"
                    f"R:R:    {sig['rr']}:1\n"
                    f"Shares: {qty}  | Size: {size_label}\n"
                    f"Total risk: ${qty * sig['risk']:.0f}\n"
                    f"─────────────────\n"
                    f"Pattern: {sig['total_candles']} candles\n"
                    f"⚠️ Premarket — no broker-side stop")

                r = place_eh_order(sym, qty, sig["entry"], sig["stop"], sig["target"])

                if r and r.get("id"):
                    S.eh_traded_today.add(sym)
                    S.eh_trade_count += 1
                    S.trade_count += 1
                    S.last_trade_time = now_et()

                    trade_record = {
                        "symbol": sym, "qty": qty,
                        "entry": sig["entry"], "stop": sig["stop"],
                        "breakeven_stop": sig["breakeven_stop"],
                        "target": sig["target"], "target_type": target_type,
                        "rr": sig["rr"], "risk": sig["risk"],
                        "order_id": r["id"], "size_label": size_label,
                        "session": "early",
                        "time": now_et().strftime("%H:%M ET"),
                        "vwap": sig["vwap"], "hod": sig["hod"],
                        "pole_height": sig["pole_height"],
                        "float": w.get("float_str"),
                        "catalyst": w.get("catalyst"),
                        "b_mode": S.b_mode,
                        "dry_run": r.get("dry_run", False),
                        "eh_order": True,
                    }
                    S.eh_trades_today.append(trade_record)
                    S.trades_today.append(trade_record)

                    sheets_push({
                        "type": "trade", "session": "early",
                        "date": now_et().strftime("%Y-%m-%d"),
                        "symbol": sym, "qty": qty,
                        "entry": sig["entry"], "stop": sig["stop"],
                        "target": sig["target"], "target_type": target_type,
                        "rr": sig["rr"], "risk": sig["risk"],
                        "total_risk": round(qty * sig["risk"], 2),
                        "size_label": size_label,
                        "vwap": sig["vwap"], "hod": sig["hod"],
                        "float": w.get("float_str"),
                        "catalyst": w.get("catalyst"),
                        "b_mode": S.b_mode, "equity": S.equity,
                        "trade_num": S.trade_count,
                        "order_id": r["id"], "eh_order": True,
                    })
                    S.save()
                    log("INFO", f"  [{sym}] EH Early Trade #{S.eh_trade_count} "
                                f"| size={size_label}")
                    break  # max 1 per cycle

    # ── Extended Hours: Late session trading (11:01–15:30 ET) ─────────────────
    # Same bull flag criteria, but with expanded bar window and EH order flow.
    # Half position size. Max 1 EH trade per day. Software-managed stops.
    eh_late_window = (EXTENDED_HOURS and is_wd
                      and ((hh == EH_LATE_START[0] and mm >= EH_LATE_START[1])
                           or (hh > EH_LATE_START[0] and hh < EH_LATE_END[0])
                           or (hh == EH_LATE_END[0] and mm <= EH_LATE_END[1])))

    if (eh_late_window
            and S.watchlist
            and not S.halted and not S.stopped
            and S.eh_trade_count < EH_MAX_TRADES
            and S.trade_count < MAX_TRADES):  # shared limit

        # Refresh live P&L (shared with core)
        live_pnl, live_eq = get_live_pnl()
        if live_pnl is not None:
            S.pnl    = live_pnl
            S.equity = live_eq

        # Daily loss limit check (shared)
        if S.pnl <= MAX_LOSS:
            S.halted = True
            tg_send(f"🛑 *DAILY LOSS LIMIT HIT (during EH)*\n"
                    f"P&L: ${S.pnl:+.2f} | Limit: ${MAX_LOSS:.0f}\n"
                    f"All trading halted.")
            log("WARN", f"EH: Loss limit hit: ${S.pnl:.2f}")
            S.save()
        else:
            # Intraday re-scan in late session every 15 min
            if (now_ts - S.eh_last_late_scan) >= INTRADAY_SCAN_MINS * 60:
                S.eh_last_late_scan = now_ts
                log("INFO", f"EH: Late session re-scan at {t.strftime('%H:%M ET')}...")
                fresh = scan_premarket(b_mode=S.b_mode)
                new_found = merge_scan_results(fresh, label=f"EH Late {t.strftime('%H:%M')}")
                if new_found:
                    lines_out = []
                    for w in new_found:
                        pmh = S.premarket_highs.get(w["symbol"])
                        lines_out.append(
                            f"  *{w['symbol']}* ${w['price']:.2f} | "
                            f"gap {w['gap']}% | rvol {w['rvol']}x | "
                            f"float {w.get('float_str','?')}"
                            + (f" | PMH ${pmh:.2f}" if pmh else ""))
                    tg_send(f"📡 *EH LATE SCAN — {len(new_found)} new*\n"
                            + "\n".join(lines_out))
                    sheets_push({
                        "type": "scan", "session": "late",
                        "date": now_et().strftime("%Y-%m-%d"),
                        "candidates": len(fresh),
                        "watchlist": fresh,
                        "b_mode": S.b_mode, "equity": S.equity,
                    })

            # Check for bull flags with expanded time window
            positions = get_positions()
            held_syms = {p.get("symbol", "") for p in (positions or [])}
            all_traded = S.traded_today | S.eh_traded_today

            for w in S.watchlist:
                sym = w["symbol"]
                if sym in all_traded or sym in held_syms:
                    continue
                if S.eh_trade_count >= EH_MAX_TRADES:
                    break
                if S.trade_count >= MAX_TRADES:
                    break

                pmh = S.premarket_highs.get(sym)
                sig = detect_flag(sym, premarket_high=pmh, session="late")
                if not sig:
                    continue

                # A-quality catalyst gate at trade time
                if not S.b_mode and not w.get("has_news"):
                    log("INFO", f"  [{sym}] EH SKIP: no catalyst (A-quality requires news)")
                    continue

                # Half position sizing for EH trades
                effective_equity = S.equity
                risk_dollars = effective_equity * RISK_PCT
                # Apply EH half-size multiplier
                risk_dollars *= EH_SIZE_MULT
                # Further reduce if no cushion
                if not S.cushion_built:
                    risk_dollars *= 0.25
                    size_label = f"EH quarter (building cushion, {EH_SIZE_MULT:.0%}×)"
                elif S.pnl >= DAILY_TARGET:
                    risk_dollars *= 0.50
                    size_label = f"EH half (protecting gains, {EH_SIZE_MULT:.0%}×)"
                else:
                    size_label = f"EH half ({EH_SIZE_MULT:.0%}× base)"

                qty = int(risk_dollars / sig["risk"]) if sig["risk"] > 0 else 0
                max_qty = int(effective_equity * 0.25 / sig["entry"])
                qty = min(qty, max_qty)
                qty = max(qty, 1)

                target_type = "HOD retest" if sig.get("target_is_hod") else "measured move"

                tg_send(
                    f"🌙 *EH BULL FLAG [{'B-MODE' if S.b_mode else 'A-QUALITY'}]: {sym}*\n"
                    f"Session: LATE ({t.strftime('%H:%M ET')})\n"
                    f"Entry:  ${sig['entry']:.2f}\n"
                    f"Stop:   ${sig['stop']:.2f}  (risk ${sig['risk']:.2f}/sh)\n"
                    f"Target: ${sig['target']:.2f}  ({target_type})\n"
                    f"BE stop: ${sig['breakeven_stop']:.2f}  ← move stop here after fill\n"
                    f"R:R:    {sig['rr']}:1\n"
                    f"Shares: {qty}  | Size: {size_label}\n"
                    f"Total risk: ${qty * sig['risk']:.0f}\n"
                    f"─────────────────\n"
                    f"Pattern: {sig['total_candles']} candles\n"
                    f"✅ Regular hours — bracket order with broker-side stop")

                # Late session is during regular market hours (11:01-15:30)
                # so we use standard bracket orders — NOT place_eh_order.
                # Bracket orders provide broker-side stop-loss protection.
                r = place_bracket(sym, qty, sig["entry"], sig["stop"], sig["target"])

                if r and r.get("id"):
                    S.eh_traded_today.add(sym)
                    S.eh_trade_count += 1
                    S.trade_count += 1  # shared counter
                    S.last_trade_time = now_et()

                    trade_record = {
                        "symbol":         sym,
                        "qty":            qty,
                        "entry":          sig["entry"],
                        "stop":           sig["stop"],
                        "breakeven_stop": sig["breakeven_stop"],
                        "target":         sig["target"],
                        "target_type":    target_type,
                        "rr":             sig["rr"],
                        "risk":           sig["risk"],
                        "order_id":       r["id"],
                        "size_label":     size_label,
                        "session":        "late",
                        "time":           now_et().strftime("%H:%M ET"),
                        "vwap":           sig["vwap"],
                        "hod":            sig["hod"],
                        "pole_height":    sig["pole_height"],
                        "float":          w.get("float_str"),
                        "catalyst":       w.get("catalyst"),
                        "b_mode":         S.b_mode,
                        "dry_run":        r.get("dry_run", False),
                    }
                    S.eh_trades_today.append(trade_record)
                    S.trades_today.append(trade_record)  # also in combined list

                    sheets_push({
                        "type":       "trade",
                        "session":    "late",
                        "date":       now_et().strftime("%Y-%m-%d"),
                        "symbol":     sym,
                        "qty":        qty,
                        "entry":      sig["entry"],
                        "stop":       sig["stop"],
                        "target":     sig["target"],
                        "target_type":target_type,
                        "rr":         sig["rr"],
                        "risk":       sig["risk"],
                        "total_risk": round(qty * sig["risk"], 2),
                        "size_label": size_label,
                        "vwap":       sig["vwap"],
                        "hod":        sig["hod"],
                        "float":      w.get("float_str"),
                        "catalyst":   w.get("catalyst"),
                        "b_mode":     S.b_mode,
                        "equity":     S.equity,
                        "trade_num":  S.trade_count,
                        "order_id":   r["id"],
                    })
                    S.save()
                    log("INFO", f"  [{sym}] EH Trade #{S.eh_trade_count} recorded "
                                f"| size={size_label}")
                    break  # max 1 EH trade per cycle to avoid rapid-fire

    # ── Extended Hours: Software stop monitoring ──────────────────────────────
    # Runs every cycle when we have active EH positions.
    # Polls price and sells via limit order if stop is breached.
    # NOTE: runs even if EXTENDED_HOURS was toggled off — must manage
    # any already-open positions until they're closed.
    if S.eh_active_stops:
        monitor_eh_stops()

    # ── Extended Hours: EOD forced liquidation at 15:55 ET ────────────────────
    # Safety net: if any EH positions are still open at 3:55 PM, force-close
    # them before market close. Prevents unmanaged overnight positions.
    # The TP limit order (time_in_force=day) would be cancelled by Alpaca at
    # 4:00 PM anyway, leaving a naked position with no stop and no target.
    # NOTE: runs even if EXTENDED_HOURS was toggled off — must close
    # any already-open positions.
    if (is_wd and hh == 15 and mm >= 55 and mm < 59
            and S.eh_active_stops):
        log("WARN", "EH EOD LIQUIDATION: forcing close of open EH positions at 15:55 ET")
        for order_id in list(S.eh_active_stops.keys()):
            info = S.eh_active_stops[order_id]
            sym  = info["symbol"]

            if not info.get("filled"):
                # Buy never filled — just cancel the pending buy order
                if not info.get("dry_run"):
                    alp_del(f"/v2/orders/{order_id}")
                log("INFO", f"  [{sym}] EH EOD: cancelled unfilled buy order")
                tg_send(f"🕐 *EH EOD: {sym}* — cancelled unfilled buy order")
                del S.eh_active_stops[order_id]
                continue

            # Position is open — cancel TP and sell at market via aggressive limit
            if info.get("dry_run"):
                log("INFO", f"  [{sym}] EH EOD DRY RUN: simulated forced close")
                tg_send(f"🕐 *EH EOD (DRY RUN): {sym}* — would force close\n"
                        f"Entry: ${info['fill_price']:.2f}")
                del S.eh_active_stops[order_id]
                continue

            # Cancel existing TP order
            if info.get("tp_order_id"):
                alp_del(f"/v2/orders/{info['tp_order_id']}")
                log("INFO", f"  [{sym}] EH EOD: cancelled TP order")

            # Get current price for aggressive limit sell
            bars = get_1min_bars(sym, limit=2)
            if bars:
                current_price = float(bars[-1]["c"])
            else:
                current_price = info.get("fill_price", info["entry"])

            # Sell at current price - 10¢ to ensure fill before close
            sell_price = round(current_price - 0.10, 2)
            sell_r = alp_post("/v2/orders", {
                "symbol": sym, "qty": str(info["qty"]), "side": "sell",
                "type": "limit", "time_in_force": "day",
                "limit_price": str(sell_price),
            })

            pnl_per_sh = current_price - info["fill_price"]
            if sell_r and sell_r.get("id"):
                log("INFO", f"  [{sym}] EH EOD: forced sell @ ~${sell_price:.2f} "
                            f"| entry ${info['fill_price']:.2f} "
                            f"| est P&L ${pnl_per_sh:+.2f}/sh")
                tg_send(f"🕐 *EH EOD LIQUIDATION: {sym}*\n"
                        f"Forcing close @ ~${sell_price:.2f}\n"
                        f"Entry: ${info['fill_price']:.2f} | "
                        f"Est P&L: ${pnl_per_sh:+.2f}/sh\n"
                        f"Reason: preventing overnight hold")
            else:
                log("ERROR", f"  [{sym}] EH EOD: forced sell FAILED: {sell_r}")
                tg_send(f"❌ *EH EOD: {sym}* — forced sell FAILED\n"
                        f"⚠️ Position may carry overnight! Check Alpaca dashboard")

            del S.eh_active_stops[order_id]

        S.save()

    # ── EOD scorecard 16:00–16:05 ET ─────────────────────────────────────────
    if is_wd and hh == 16 and mm < 5 and S.scanned:
        acc      = get_account()
        S.equity = float(acc.get("equity", S.equity))
        last_eq  = float(acc.get("last_equity", S.equity))
        S.pnl    = round(S.equity - last_eq, 2)

        outcome = ("🟢 Green day!" if S.pnl > 0
                   else ("🔴 Red day" if S.pnl < 0
                   else "⚪ Flat day"))

        trade_lines = ""
        if S.trades_today:
            trade_lines = "\n\n*Trades:*\n" + "\n".join(
                f"  {'🌙' if tr.get('session') == 'late' else '☀️'} "
                f"{tr['symbol']} {tr['qty']}sh @ ${tr['entry']:.2f} "
                f"({tr.get('size_label','?')}) "
                f"SL ${tr['stop']:.2f} TP ${tr['target']:.2f} "
                f"({tr.get('target_type','?')}) "
                f"[{tr.get('session','core')}]"
                for tr in S.trades_today)

        eh_line = ""
        if EXTENDED_HOURS:
            eh_line = (f"\nEH trades: {S.eh_trade_count}/{EH_MAX_TRADES}"
                       f" | active stops: {len(S.eh_active_stops)}")

        tg_send(
            f"📊 *EOD — {t.strftime('%a %b %d')}*\n"
            f"{outcome}\n"
            f"Trades: {S.trade_count} | P&L: ${S.pnl:+.2f}\n"
            f"Equity: ${S.equity:,.2f}\n"
            f"Candidates today: {len(S.watchlist)}"
            + eh_line
            + trade_lines)

        log("INFO", f"EOD | trades={S.trade_count} pnl=${S.pnl:+.2f} "
                    f"equity=${S.equity:,.2f}")
        sheets_push({
            "type":          "eod",
            "date":          t.strftime("%Y-%m-%d"),
            "day_name":      t.strftime("%A"),
            "trades":        S.trade_count,
            "pnl":           S.pnl,
            "equity":        S.equity,
            "last_equity":   last_eq,
            "candidates":    len(S.watchlist),
            "outcome":       outcome,
            "b_mode":        S.b_mode,
            "extended_hours": EXTENDED_HOURS,
            "eh_trades":     S.eh_trade_count,
            "trades_detail": S.trades_today,
        })
        S.scanned = False   # prevent re-send
        S.save()

# ── Dashboard HTTP server ─────────────────────────────────────────────────────
# Runs in a background thread on port 8080.
# Serves /api/dashboard — a JSON blob with account, positions, orders,
# recent fills, trades today, and bot status — all fetched server-side
# so no CORS issue for the browser dashboard.
# Zeabur will expose this port automatically if you set the service port to 8080.
DASHBOARD_PORT = int(os.environ.get("PORT") or os.environ.get("DASHBOARD_PORT", "8080"))  # Zeabur injects $PORT at runtime

class DashboardHandler(BaseHTTPRequestHandler):

    def log_message(self, fmt, *args):
        pass  # silence default HTTP logging

    def _cors(self):
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Headers", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, OPTIONS")

    def do_OPTIONS(self):
        self.send_response(200)
        self._cors()
        self.end_headers()

    def do_GET(self):
        path = self.path.split("?")[0]

        if path == "/" or path == "":
            self._json({"status": "ok"})
            return

        if path == "/health":
            self._json({"status": "ok", "time": now_et().isoformat()})
            return

        # Token protection for sensitive endpoints
        if path in ("/api/dashboard", "/api/log"):
            provided = self.path.split("token=")[-1].split("&")[0] if "token=" in self.path else ""
            if DASH_TOKEN and provided != DASH_TOKEN:
                self._json({"error": "unauthorized"}, status=401)
                return

        if path == "/api/dashboard":
            self._serve_dashboard()
            return

        if path == "/api/log":
            self._serve_log()
            return

        self.send_response(404)
        self._cors()
        self.end_headers()

    def _json(self, data, status=200):
        body = json.dumps(data, default=str).encode()
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", len(body))
        self._cors()
        self.end_headers()
        self.wfile.write(body)

    def _serve_log(self):
        try:
            with open(LOG_FILE) as f:
                lines = f.readlines()[-50:]
            self._json({"lines": lines})
        except Exception as e:
            self._json({"lines": [], "error": str(e)})

    def _serve_dashboard(self):
        try:
            # Fetch live data from Alpaca server-side (no CORS problem here)
            acct      = alp_get("/v2/account") or {}
            positions = alp_get("/v2/positions") or []
            orders    = alp_get("/v2/orders?status=open&limit=50") or []
            fills     = alp_get(
                "/v2/account/activities?activity_types=FILL&page_size=20") or []
            portfolio = alp_get(
                "/v2/account/portfolio/history"
                "?period=1D&timeframe=5Min&extended_hours=true") or {}

            equity   = float(acct.get("equity", 0))
            last_eq  = float(acct.get("last_equity", equity))
            day_pnl  = round(equity - last_eq, 2)

            # Load bot state
            bot_state = {}
            try:
                with open(STATUS_FILE) as f:
                    bot_state = json.load(f)
            except Exception:
                pass

            trades_today = []
            try:
                with open(TRADES_FILE) as f:
                    trades_today = json.load(f)
            except Exception:
                pass

            self._json({
                "ok": True,
                "fetched_at": now_et().isoformat(),
                "account": {
                    "equity":        equity,
                    "last_equity":   last_eq,
                    "day_pnl":       day_pnl,
                    "buying_power":  float(acct.get("buying_power", 0)),
                    "cash":          float(acct.get("cash", 0)),
                    "status":        acct.get("status", ""),
                },
                "positions":    positions,
                "orders":       orders,
                "fills":        fills,
                "portfolio":    portfolio,
                "bot": {
                    "trade_count":   bot_state.get("trade_count", 0),
                    "pnl":           bot_state.get("pnl", 0),
                    "cushion_built": bot_state.get("cushion_built", False),
                    "scanned":       bot_state.get("scanned", False),
                    "halted":        bot_state.get("halted", False),
                    "stopped":       bot_state.get("stopped", False),
                    "b_mode":        bot_state.get("b_mode", False),
                    "watchlist":     bot_state.get("watchlist", []),
                    "started":       bot_state.get("started", ""),
                    "extended_hours": EXTENDED_HOURS,
                    "eh_trade_count": S.eh_trade_count,
                    "eh_active_stops": len(S.eh_active_stops),
                },
                "trades_today": trades_today,
                "config": {
                    "daily_target":  DAILY_TARGET,
                    "max_loss":      MAX_LOSS,
                    "max_trades":    MAX_TRADES,
                    "risk_pct":      RISK_PCT,
                    "gap_min":       GAP_MIN,
                    "rvol_min":      RVOL_MIN,
                    "float_max":     FLOAT_MAX,
                    "extended_hours": EXTENDED_HOURS,
                    "eh_max_trades": EH_MAX_TRADES,
                    "eh_size_mult":  EH_SIZE_MULT,
                },
            })

        except Exception as e:
            log("ERROR", f"Dashboard API error: {e}")
            self._json({"ok": False, "error": str(e)}, status=500)


def start_dashboard_server():
    """
    Bind dashboard/health check port. Uses SO_REUSEADDR to avoid
    'address already in use' on container restart (Zeabur sends SIGTERM
    then immediately restarts, and the old socket may still be in TIME_WAIT).
    """
    try:
        class ReusableTCPServer(HTTPServer):
            allow_reuse_address = True
        server = ReusableTCPServer(("0.0.0.0", DASHBOARD_PORT), DashboardHandler)
        log("INFO", f"Dashboard API listening on port {DASHBOARD_PORT}")
        log("INFO", f"  Endpoints: /health  /api/dashboard  /api/log")
        server.serve_forever()
    except Exception as e:
        log("ERROR", f"Dashboard server failed to start: {e}")


# ── Shutdown ──────────────────────────────────────────────────────────────────
def _shutdown(sig, _):
    log("INFO", f"Shutdown signal {sig}")
    tg_send("🔴 GreenClaw stopped")
    sys.exit(0)

# ── Entry point ───────────────────────────────────────────────────────────────
def main():
    signal.signal(signal.SIGTERM, _shutdown)
    signal.signal(signal.SIGINT,  _shutdown)

    # Start dashboard API server in background thread
    t = threading.Thread(target=start_dashboard_server, daemon=True)
    t.start()
    time.sleep(0.5)  # give OS a moment to confirm port is listening

    startup()
    log("INFO", "Main loop active")

    while True:
        try:
            updates = tg_poll(S.offset, 25)
            for u in updates:
                msg = u.get("message", {})
                txt = msg.get("text", "")
                cid = str(msg.get("chat", {}).get("id", ""))
                if txt:
                    handle_cmd(txt, cid)
                S.offset = u["update_id"] + 1

            cycle()
            S.save()

        except KeyboardInterrupt:
            log("INFO", "Keyboard interrupt")
            tg_send("🔴 GreenClaw stopped")
            break
        except Exception as e:
            log("ERROR", f"Loop error: {e}")
            time.sleep(10)

if __name__ == "__main__":
    main()
