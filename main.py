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
  - Max loss = daily goal (Ross's exact symmetry rule)
  - Intraday HOD tracked live from 1-min bars
  - Breakeven stop move logged and noted after entry
  - All five criteria verified and logged for every scan candidate
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
NO_TRADE_HALT_MINS = 30  # stop trying if no valid setup for this many minutes

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

# ── Alpaca ────────────────────────────────────────────────────────────────────
def alp_h():
    return {"APCA-API-KEY-ID": ALPACA_KEY, "APCA-API-SECRET-KEY": ALPACA_SEC}

def alp_get(p):    return GET(f"{ALPACA_URL}{p}", h=alp_h())
def alp_post(p,d): return POST(f"{ALPACA_URL}{p}", d, h=alp_h())
def alp_del(p):    return DELETE(f"{ALPACA_URL}{p}", h=alp_h())

def get_account():   return alp_get("/v2/account") or {}
def get_equity():    return float(get_account().get("equity", 0))
def get_positions(): return alp_get("/v2/positions") or []
def get_orders():    return alp_get("/v2/orders?status=open&limit=50") or []

def get_1min_bars(sym, limit=60):
    """Fetch 1-min bars from Alpaca IEX (Ross's primary chart timeframe)."""
    url = (f"https://data.alpaca.markets/v2/stocks/{sym}/bars"
           f"?timeframe=1Min&limit={limit}&feed=iex&adjustment=raw")
    resp = GET(url, h=alp_h())
    if not resp or "bars" not in resp:
        return []
    return resp["bars"]  # [{t, o, h, l, c, v, vw, n}, ...]

def place_bracket(sym, qty, entry, stop, target):
    """Submit bracket order. Returns order dict or None."""
    order = {
        "symbol": sym, "qty": str(qty), "side": "buy",
        "type": "limit", "time_in_force": "day",
        "limit_price": str(round(entry, 2)),
        "order_class": "bracket",
        "take_profit": {"limit_price": str(round(target, 2))},
        "stop_loss":   {"stop_price":  str(round(stop,  2))}
    }
    log("INFO", f"ORDER: {sym} BUY {qty} @ ${entry:.2f} "
                f"SL ${stop:.2f} TP ${target:.2f}")
    r = alp_post("/v2/orders", order)
    if r and r.get("id"):
        log("INFO", f"  ✅ Accepted | id={r['id']}")
        return r
    log("ERROR", f"  ❌ FAILED: {r}")
    tg_send(f"❌ ORDER FAILED {sym}\n{str(r)[:200]}")
    return None

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
    wsо = result.get("weighted_shares_outstanding")
    if wsо:
        return int(wsо)
    return None

def check_catalyst(sym):
    """
    Check Polygon news for recent catalyst.
    Ross: news event is what "brings in the volume."
    Returns (bool, headline).
    """
    try:
        yesterday = (date.today() - timedelta(days=2)).isoformat()
        url = (f"https://api.polygon.io/v2/reference/news"
               f"?ticker={sym}&published_utc.gte={yesterday}"
               f"&limit=3&apiKey={POLYGON_KEY}")
        resp = GET(url)
        if resp and resp.get("results"):
            headline = resp["results"][0].get("title", "News found")
            return True, headline
        return False, "No recent news"
    except Exception:
        return False, "Catalyst check unavailable"

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
        today = date.today().isoformat()
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
def detect_flag(sym, premarket_high=None):
    """
    Ross Cameron Bull Flag on 1-minute chart.

    Ross's exact pattern (from transcript):
    - "Usually constructed of 5 to 7 individual candles"
    - "First one is a green candle" (the flagpole surge)
    - Volume ramps up on the pole, decreases on the flag ("lighter volume on selling")
    - "First candle to make a new high — that's the moment you're buying"
    - "My stop is the low of the pullback"
    - "Profit target: retest of the high of day"

    Returns signal dict or None. Logs reason for every rejection.
    """
    bars = get_1min_bars(sym, limit=60)
    if not bars:
        log("INFO", f"  [{sym}] SKIP: no 1-min bar data")
        return None

    # Filter to today's bars only
    today_str = date.today().isoformat()
    bars = [b for b in bars if b["t"][:10] == today_str]

    # Only use bars from 9:35 ET onward (skip opening 5-min chaos)
    # but still compute VWAP from 9:30 if available
    all_today = []
    market_bars = []
    for b in bars:
        ts_et = datetime.fromisoformat(b["t"].replace("Z", "+00:00")).astimezone(ET)
        if ts_et.hour >= 9 and ts_et.minute >= 30:
            all_today.append(b)
        if ts_et.hour > 9 or (ts_et.hour == 9 and ts_et.minute >= 35):
            if ts_et.hour < 11 or (ts_et.hour == 11 and ts_et.minute == 0):
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

    # Estimate how many minutes into the trading session we are
    now   = now_et()
    open_time = now.replace(hour=9, minute=30, second=0, microsecond=0)
    mins_traded = max(1, int((now - open_time).total_seconds() / 60))
    # Pre-market scan happens before open — use 1 minute as minimum
    if now.hour < 9 or (now.hour == 9 and now.minute < 30):
        mins_traded = 1   # pre-market: use minimal value

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
            tod_rvol = calc_tod_rvol(vol, prev_vol, mins_traded)
            # Also compute raw RVOL for display
            raw_rvol = vol / max(prev_vol, 1)

            # ── Apply all 5 criteria with explicit pass/fail logging ──────────
            fails = []
            if price < PRICE_LO:     fails.append(f"price ${price:.2f}<${PRICE_LO}")
            if price > PRICE_HI:     fails.append(f"price ${price:.2f}>${PRICE_HI}")
            if gap < gap_thr:        fails.append(f"gap {gap:.1f}%<{gap_thr}%")
            if tod_rvol < rvol_thr:  fails.append(f"rvol {tod_rvol:.1f}x<{rvol_thr}x")

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
            has_news, headline = check_catalyst(sym)
            if not has_news:
                log("INFO", f"  WARN {sym}: no catalyst found "
                            f"— watchlisting anyway (verify manually)")
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
        self.b_mode           = False
        self.cushion_built    = False  # True once 25% of daily target earned
        self.last_trade_time  = None   # datetime of last trade attempt
        self.date             = ""
        self.equity           = 0.0
        self.offset           = 0
        self.force_scan       = False
        self.start_time       = now_et().isoformat()
        self.last_heartbeat   = 0.0

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
        self.cushion_built   = False
        self.last_trade_time = None
        self.date            = d
        self.force_scan      = False

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

# ── Position sizing (Ross's micro/macro system) ───────────────────────────────
def calc_qty(entry, stop, equity, trade_num, cushion_built, daily_target):
    """
    Ross's sizing rules from the video:
    - Start at QUARTER size (25% of normal) for trade 1 and 2
    - Scale to FULL size only after cushion is built (≥25% of daily target earned)
    - If daily target already hit: half size to protect gains
    - Never more than 25% of equity in one position

    Quarter-start prevents the revenge-trading spiral on bad days while
    still allowing full participation on good days once validated.
    """
    risk_dollars = equity * RISK_PCT

    # Size multiplier based on day state
    if not cushion_built:
        # Quarter size until first cushion earned
        multiplier = 0.25
        size_label = "quarter (no cushion yet)"
    elif daily_target > 0 and (equity * 0.01) > 0:
        # Full size once cushion built
        multiplier = 1.0
        size_label = "full"

    # Extra caution: reduce to half if daily target already fully hit
    # (protect the green day)
    # This is tracked externally and passed in as equity >= daily_target
    if daily_target > 0 and equity > 0:
        pass  # handled by caller checking S.pnl

    qty = int(risk_dollars * multiplier / max(stop - entry, 0.01)) \
        if stop < entry else \
        int(risk_dollars * multiplier / max(entry - stop, 0.01))

    # Hard cap: 25% of equity in any single position
    max_qty = int(equity * 0.25 / entry) if entry > 0 else 0
    qty = min(qty, max_qty)

    return max(1, qty), size_label

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
            f"Stopped: {d.get('stopped',False)}"
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
            "/bmode     — toggle B-mode (looser criteria)\n"
            "/help      — this message\n\n"
            f"*A-quality*: gap≥{GAP_MIN}% rvol≥{RVOL_MIN}x "
            f"float≤{FLOAT_MAX/1e6:.0f}M ${PRICE_LO}-${PRICE_HI}\n"
            f"*Sizing*: quarter size until cushion "
            f"(${DAILY_TARGET*CUSHION_PCT:.0f}), then full\n"
            f"*Daily goal*: ${DAILY_TARGET:.0f} | "
            f"*Max loss*: ${abs(MAX_LOSS):.0f}")

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
        f"Send /help for commands")
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

    # ── Pre-market scan at 9:00–9:05 ET (or forced) ──────────────────────────
    scan_time = is_wd and hh == 9 and mm < 5
    if (scan_time and not S.scanned) or S.force_scan:
        S.watchlist  = scan_premarket(b_mode=S.b_mode)
        S.scanned    = True
        S.force_scan = False
        S.equity     = get_equity()

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

    # ── Cold market auto-stop ─────────────────────────────────────────────────
    # Ross: "if I haven't picked up a trade in 30 minutes I just give up"
    if (is_wd and hh >= 9 and hh < 11
            and S.scanned and S.watchlist
            and S.trade_count == 0
            and not S.stopped and not S.halted):
        if S.last_trade_time is None:
            # Start the clock from 9:35 (first monitoring time)
            first_monitor = t.replace(hour=9, minute=35, second=0, microsecond=0)
            if t > first_monitor:
                elapsed = (t - first_monitor).total_seconds() / 60
                if elapsed >= NO_TRADE_HALT_MINS:
                    S.stopped = True
                    log("INFO", "Cold market: no trade in 30 min — stopping")
                    tg_send(f"🥶 *Cold market — stopping for today*\n"
                            f"No valid setup found in {NO_TRADE_HALT_MINS} min.\n"
                            f"Send /resume to override if you see something.")
                    S.save()

    # ── Active trading: 9:35–11:00 ET ────────────────────────────────────────
    in_window = (is_wd and
                 ((hh == 9 and mm >= 35) or hh == 10
                  or (hh == 11 and mm == 0)))

    if in_window and S.watchlist and not S.halted and not S.stopped:

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
            tg_send(
                f"🚩 *BULL FLAG: {sym}*\n"
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
                    "time":           now_et().strftime("%H:%M ET"),
                    "vwap":           sig["vwap"],
                    "hod":            sig["hod"],
                    "pole_height":    sig["pole_height"],
                    "float":          w.get("float_str"),
                    "catalyst":       w.get("catalyst"),
                    "b_mode":         S.b_mode,
                })
                S.save()
                log("INFO", f"  [{sym}] Trade #{S.trade_count} recorded "
                            f"| size={size_label}")

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
                f"  {tr['symbol']} {tr['qty']}sh @ ${tr['entry']:.2f} "
                f"({tr.get('size_label','?')}) "
                f"SL ${tr['stop']:.2f} TP ${tr['target']:.2f} "
                f"({tr.get('target_type','?')})"
                for tr in S.trades_today)

        tg_send(
            f"📊 *EOD — {t.strftime('%a %b %d')}*\n"
            f"{outcome}\n"
            f"Trades: {S.trade_count} | P&L: ${S.pnl:+.2f}\n"
            f"Equity: ${S.equity:,.2f}\n"
            f"Candidates today: {len(S.watchlist)}"
            + trade_lines)

        log("INFO", f"EOD | trades={S.trade_count} pnl=${S.pnl:+.2f} "
                    f"equity=${S.equity:,.2f}")
        S.scanned = False   # prevent re-send
        S.save()

# ── Dashboard HTTP server ─────────────────────────────────────────────────────
# Runs in a background thread on port 8080.
# Serves /api/dashboard — a JSON blob with account, positions, orders,
# recent fills, trades today, and bot status — all fetched server-side
# so no CORS issue for the browser dashboard.
# Zeabur will expose this port automatically if you set the service port to 8080.
DASHBOARD_PORT = int(os.environ.get("DASHBOARD_PORT", "8080"))

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

        if path == "/health":
            self._json({"status": "ok", "time": now_et().isoformat()})
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
                },
            })

        except Exception as e:
            log("ERROR", f"Dashboard API error: {e}")
            self._json({"ok": False, "error": str(e)}, status=500)


def start_dashboard_server():
    try:
        server = HTTPServer(("0.0.0.0", DASHBOARD_PORT), DashboardHandler)
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
