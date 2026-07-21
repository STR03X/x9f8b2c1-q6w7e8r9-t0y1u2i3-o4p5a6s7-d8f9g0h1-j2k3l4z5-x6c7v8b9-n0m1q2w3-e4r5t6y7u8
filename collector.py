import asyncio
import json
import time
import os
import csv
import logging
import sys
from datetime import datetime, timezone
from collections import deque
from typing import Any
import zendriver as uc
import zendriver.cdp.input_ as cdp_input
import zendriver.cdp.network as cdp_network

crash_handler = logging.FileHandler("crash.log", encoding="utf-8", delay=True)
crash_handler.setLevel(logging.WARNING)
crash_handler.setFormatter(logging.Formatter("%(asctime)s [%(levelname)s] %(message)s"))

stdout_handler = logging.StreamHandler(sys.stdout)
stdout_handler.setLevel(logging.INFO)
stdout_handler.setFormatter(logging.Formatter("%(asctime)s [%(levelname)s] %(message)s"))

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[crash_handler, stdout_handler]
)
logger = logging.getLogger("Collector")

BINOMO_URL = "https://binomo.com/trading"
CANDLE_SECONDS = 5
WINDOW_SIZE = 60
MIN_TICKS = 5
YATAY_TOLERANCE_PCT = 0.0 

ticks = []
candles = deque(maxlen=300)
candles_5m = deque(maxlen=150)
ticks_for_5m = []
current_5m_bucket = None
current_sentiment = {"call": 50, "put": 50}
sentiment_history = deque(maxlen=60)
smart_money_history = deque(maxlen=3)
current_std = 0.0
current_radius = 0.0
current_range_coeff = 1.0
current_minute = None
latest_server_timestamp = 0.0

current_smart_money = {
    "trend": None,
    "bet_amount": 0,
    "rate": None,
    "timestamp": None
}
session_start_time = None
restart_browser = False
session_range_coefficient = 1.0

pending_rows = []
_cf_bypass_running = False
_last_cf_solve_time = 0.0
CSV_PATH = "dataset.csv"

CSV_HEADERS = [
    "timestamp", "close", "rsi", "macd_line", "macd_hist", "stoch_k", "stoch_d",
    "ema9", "ema21", "ema_signal", "bollinger_width", "bollinger_position",
    "bollinger_squeeze", "sar", "sar_dev", "atr", "vol_score", "obv_trend",
    "sentiment_call", "sentiment_put", "sentiment_momentum",
    "pattern", "support_dist_pct", "resistance_dist_pct", "htf_5m_trend",
    "market_regime", "fibonacci_distance", "fibonacci_warning",
    "smart_money_trend", "smart_money_bet", "smart_money_strength",
    "bid_ask_imbalance",
    "hour_of_day", "day_of_week",
    "price_diff_t1", "price_diff_t2",
    "rsi_diff_t1", "rsi_diff_t2",
    "macd_hist_slope", "stoch_diff",
    "bollinger_pct_b",
    "ema9_dev", "ema21_dev",
    "volatility_ratio",
    "tick_count", "tick_ratio",
    "sentiment_change_t1",
    "target_seconds", "target_price", "price_change", "pnl_result"
]

def init_csv():
    if not os.path.exists(CSV_PATH) or os.path.getsize(CSV_PATH) == 0:
        with open(CSV_PATH, "w", newline="", encoding="utf-8") as f:
            writer = csv.writer(f)
            writer.writerow(CSV_HEADERS)
        logger.info(f"[CSV] {CSV_PATH} basariyla olusturuldu.")

init_csv()

def calc_adx(candles_list, period=14):
    if len(candles_list) < period * 2 + 1:
        return None
    trs = []
    plus_dms = []
    minus_dms = []

    for i in range(1, len(candles_list)):
        c = candles_list[i]
        p = candles_list[i - 1]
        tr = max(
            c["high"] - c["low"],
            abs(c["high"] - p["close"]),
            abs(c["low"] - p["close"])
        )
        trs.append(tr)
        up_move = c["high"] - p["high"]
        down_move = p["low"] - c["low"]
        if up_move > down_move and up_move > 0:
            plus_dms.append(up_move)
        else:
            plus_dms.append(0.0)
        if down_move > up_move and down_move > 0:
            minus_dms.append(down_move)
        else:
            minus_dms.append(0.0)

    str_val = sum(trs[:period])
    splus_dm = sum(plus_dms[:period])
    sminus_dm = sum(minus_dms[:period])
    dx_series = []
    if str_val > 0:
        plus_di = 100 * (splus_dm / str_val)
        minus_di = 100 * (sminus_dm / str_val)
    else:
        plus_di = 0.0
        minus_di = 0.0
    di_sum = plus_di + minus_di
    dx = 100 * (abs(plus_di - minus_di) / di_sum) if di_sum > 0 else 0.0
    dx_series.append(dx)
    for i in range(period, len(trs)):
        str_val = str_val - (str_val / period) + trs[i]
        splus_dm = splus_dm - (splus_dm / period) + plus_dms[i]
        sminus_dm = sminus_dm - (sminus_dm / period) + minus_dms[i]
        if str_val > 0:
            plus_di = 100 * (splus_dm / str_val)
            minus_di = 100 * (sminus_dm / str_val)
        else:
            plus_di = 0.0
            minus_di = 0.0
        di_sum = plus_di + minus_di
        dx = 100 * (abs(plus_di - minus_di) / di_sum) if di_sum > 0 else 0.0
        dx_series.append(dx)
    if len(dx_series) < period:
        return None
    adx = sum(dx_series[:period]) / period
    for i in range(period, len(dx_series)):
        adx = (adx * (period - 1) + dx_series[i]) / period
    return adx

def calc_bollinger_width(prices, period=20):
    if len(prices) < period:
        return None
    res = calc_bollinger(prices, period)
    if not res or res[0] is None:
        return None
    sma, upper, lower = res
    if sma == 0:
        return 0.0
    return (upper - lower) / sma

def detect_bollinger_squeeze(prices, period=20, window_len=40):
    if len(prices) < period + window_len:
        return False
    widths = []
    for i in range(len(prices) - window_len + 1, len(prices) + 1):
        w = calc_bollinger_width(prices[:i], period)
        if w is not None:
            widths.append(w)
    if not widths:
        return False
    current_width = widths[-1]
    sorted_widths = sorted(widths)
    percentile_20_index = max(0, int(len(sorted_widths) * 0.20))
    threshold = sorted_widths[percentile_20_index]
    return current_width <= threshold

def detect_market_regime(candles_list, range_coeff) -> str:
    if len(candles_list) < 30:
        return "RANGING"
    adx = calc_adx(list(candles_list), 14)
    closes = [c["close"] for c in candles_list]
    bb_width = calc_bollinger_width(closes, 20)
    score = 0

    if adx is not None:
        if adx > 25:
            score += 2
        elif adx < 20:
            score -= 1

    if bb_width is not None:
        n = len(closes)
        recent_widths = [
            calc_bollinger_width(closes[:i], 20)
            for i in range(max(20, n - 30), n + 1)
        ]
        recent_widths = [w for w in recent_widths if w is not None]
        if len(recent_widths) >= 5:
            sorted_w = sorted(recent_widths)
            p80 = sorted_w[int(len(sorted_w) * 0.8)]
            p20 = sorted_w[max(0, int(len(sorted_w) * 0.2))]
            if bb_width >= p80:
                score += 2
            elif bb_width <= p20:
                score -= 1

    if score >= 2:
        return "STRONG_TREND"
    return "RANGING"

def calc_fibonacci_status(candles_list, current_price) -> dict:
    clist = list(candles_list)
    if len(clist) < 15:
        return {"closest_level_name": "YOK", "closest_level_val": None, "distance_pct": 999.0, "warning": "Yetersiz veri"}
    highs = [c["high"] for c in clist]
    lows = [c["low"] for c in clist]
    highest_high = max(highs)
    lowest_low = min(lows)
    diff = highest_high - lowest_low
    if diff == 0:
        return {"closest_level_name": "YOK", "closest_level_val": None, "distance_pct": 999.0, "warning": "Yatay bant"}
    fib_levels = {
        "0.000": lowest_low,
        "0.236": lowest_low + 0.236 * diff,
        "0.382": lowest_low + 0.382 * diff,
        "0.500": lowest_low + 0.5 * diff,
        "0.618": lowest_low + 0.618 * diff,
        "0.786": lowest_low + 0.786 * diff,
        "1.000": highest_high
    }
    closest_level_name = None
    closest_level_val = None
    min_distance_pct = 999.0
    for name, val in fib_levels.items():
        if val == 0:
            continue
        dist_pct = (abs(current_price - val) / val) * 100
        if dist_pct < min_distance_pct:
            min_distance_pct = dist_pct
            closest_level_name = name
            closest_level_val = val
    range_pct = (diff / lowest_low) * 100
    threshold = range_pct * 0.05
    warning = "Normal"
    if min_distance_pct < threshold:
        warning = "Yakın"
    return {
        "closest_level_name": closest_level_name,
        "closest_level_val": round(closest_level_val, 14) if closest_level_val else None,
        "distance_pct": round(min_distance_pct, 12),
        "warning": warning
    }

def calc_ema(prices, period):
    if len(prices) < period:
        return None
    k = 2 / (period + 1)
    ema = sum(prices[:period]) / period
    for p in prices[period:]:
        ema = p * k + ema * (1 - k)
    return ema

def calc_rsi(prices, period=14):
    if len(prices) < period + 1:
        return None
    gains, losses = [], []
    for i in range(1, len(prices)):
        diff = prices[i] - prices[i - 1]
        gains.append(max(diff, 0.0))
        losses.append(max(-diff, 0.0))
    avg_gain = sum(gains[:period]) / period
    avg_loss = sum(losses[:period]) / period
    for i in range(period, len(gains)):
        avg_gain = (avg_gain * (period - 1) + gains[i]) / period
        avg_loss = (avg_loss * (period - 1) + losses[i]) / period
    if avg_loss == 0:
        return 100.0
    rs = avg_gain / avg_loss
    return 100 - (100 / (1 + rs))

def calc_stoch_rsi(prices, period=14, smooth_k=3, smooth_d=3):
    min_required = period * 2 + smooth_k + smooth_d
    if len(prices) < min_required:
        return None, None
    rsi_vals = []
    for i in range(period + 1, len(prices) + 1):
        r = calc_rsi(prices[:i], period)
        if r is not None:
            rsi_vals.append(r)
    if len(rsi_vals) < period:
        return None, None
    stoch_rsi_vals = []
    for i in range(period, len(rsi_vals) + 1):
        window = rsi_vals[i - period:i]
        min_rsi = min(window)
        max_rsi = max(window)
        if max_rsi == min_rsi:
            stoch_rsi_vals.append(0.0)
        else:
            stoch = (window[-1] - min_rsi) / (max_rsi - min_rsi) * 100
            stoch_rsi_vals.append(stoch)
    if len(stoch_rsi_vals) < smooth_k:
        return None, None
    k_vals = []
    for i in range(smooth_k, len(stoch_rsi_vals) + 1):
        k_vals.append(sum(stoch_rsi_vals[i - smooth_k:i]) / smooth_k)
    if len(k_vals) < smooth_d:
        return None, None
    d_val = sum(k_vals[-smooth_d:]) / smooth_d
    return k_vals[-1], d_val

def calc_macd(prices):
    if len(prices) < 26:
        return None, None
    macd_series = []
    for i in range(26, len(prices) + 1):
        e12 = calc_ema(prices[:i], 12)
        e26 = calc_ema(prices[:i], 26)
        if e12 is not None and e26 is not None:
            macd_series.append(e12 - e26)
    if len(macd_series) < 9:
        return None, None
    macd_line = macd_series[-1]
    signal = calc_ema(macd_series, 9)
    histogram = (macd_line - signal) if signal is not None else None
    return macd_line, histogram

def calc_bollinger(prices, period=20):
    if len(prices) < period:
        return None, None, None
    subset = prices[-period:]
    sma = sum(subset) / period
    std = (sum((x - sma) ** 2 for x in subset) / period) ** 0.5
    return sma, sma + 2 * std, sma - 2 * std

def calc_momentum(prices, period=10):
    if len(prices) < period + 1:
        return None
    return prices[-1] - prices[-period]

def calc_parabolic_sar(highs, lows, af_start=0.02, af_max=0.2, af_step=0.02):
    if len(highs) < 3:
        return None
    sar = [lows[0]]
    bull = True
    af = af_start
    ep = highs[0]
    for i in range(1, len(highs)):
        prev_sar = sar[-1]
        if bull:
            current_sar = prev_sar + af * (ep - prev_sar)
            if i >= 2:
                current_sar = min(current_sar, lows[i - 1], lows[i - 2])
            elif i == 1:
                current_sar = min(current_sar, lows[i - 1])
            if lows[i] < current_sar:
                bull = False
                current_sar = ep
                ep = lows[i]
                af = af_start
            else:
                if highs[i] > ep:
                    ep = highs[i]
                    af = min(af_max, af + af_step)
        else:
            current_sar = prev_sar + af * (ep - prev_sar)
            if i >= 2:
                current_sar = max(current_sar, highs[i - 1], highs[i - 2])
            elif i == 1:
                current_sar = max(current_sar, highs[i - 1])
            if highs[i] > current_sar:
                bull = True
                current_sar = ep
                ep = highs[i]
                af = af_start
            else:
                if lows[i] < ep:
                    ep = lows[i]
                    af = min(af_max, af + af_step)
        sar.append(current_sar)
    return sar[-1]

def calc_atr(candles_list, period=14):
    if len(candles_list) < 2:
        return None
    trs = []
    for i in range(1, len(candles_list)):
        c = candles_list[i]
        prev_close = candles_list[i - 1]["close"]
        try:
            h = c.get("high", c["close"])
            l = c.get("low", c["close"])
            tr = max(
                h - l,
                abs(h - prev_close),
                abs(l - prev_close),
                abs(c["close"] - prev_close),
            )
            trs.append(tr)
        except Exception:
            continue
    if not trs:
        return None
    actual_period = min(period, len(trs))
    atr = sum(trs[:actual_period]) / actual_period
    for tr in trs[actual_period:]:
        atr = (atr * (actual_period - 1) + tr) / actual_period
    return atr

def detect_patterns(candles_list):
    if len(candles_list) < 3:
        return "Yeterli mum yok"
    curr = candles_list[-1]
    prev = candles_list[-2]
    curr_body = abs(curr["open"] - curr["close"])
    curr_upper_wick = curr["high"] - max(curr["open"], curr["close"])
    curr_lower_wick = min(curr["open"], curr["close"]) - curr["low"]
    patterns = []
    if curr_body <= (curr["high"] - curr["low"]) * 0.1:
        patterns.append("Doji")
    if (prev["close"] < prev["open"] and curr["close"] > curr["open"]
            and curr["close"] > prev["open"] and curr["open"] < prev["close"]):
        patterns.append("Bullish_Engulfing")
    if (prev["close"] > prev["open"] and curr["close"] < curr["open"]
            and curr["close"] < prev["open"] and curr["open"] > prev["close"]):
        patterns.append("Bearish_Engulfing")
    if curr_lower_wick > curr_body * 2 and curr_upper_wick < curr_body * 0.5:
        patterns.append("Hammer")
    if curr_upper_wick > curr_body * 2 and curr_lower_wick < curr_body * 0.5:
        patterns.append("Shooting_Star")
    return patterns[0] if patterns else "Neutral"

def cluster_levels(levels, current_price, tolerance_pct=0.0005):
    if not levels:
        return []
    sorted_levels = sorted(levels)
    clusters = []
    current_cluster = [sorted_levels[0]]
    threshold = current_price * tolerance_pct
    for val in sorted_levels[1:]:
        if val - current_cluster[-1] <= threshold:
            current_cluster.append(val)
        else:
            clusters.append(sum(current_cluster) / len(current_cluster))
            current_cluster = [val]
    clusters.append(sum(current_cluster) / len(current_cluster))
    return clusters

def get_support_resistance(candles_list, period=50, tolerance=0.0005):
    if len(candles_list) < 5:
        return None, None
    subset = candles_list[-period:] if len(candles_list) >= period else candles_list
    swing_highs = []
    swing_lows = []
    for i in range(1, len(subset) - 1):
        if subset[i]["high"] > subset[i - 1]["high"] and subset[i]["high"] > subset[i + 1]["high"]:
            swing_highs.append(subset[i]["high"])
        if subset[i]["low"] < subset[i - 1]["low"] and subset[i]["low"] < subset[i + 1]["low"]:
            swing_lows.append(subset[i]["low"])
    if not swing_highs:
        swing_highs = [c["high"] for c in subset]
    if not swing_lows:
        swing_lows = [c["low"] for c in subset]
    current_price = candles_list[-1]["close"]
    clustered_highs = cluster_levels(swing_highs, current_price, tolerance)
    clustered_lows = cluster_levels(swing_lows, current_price, tolerance)
    resistances_above = [h for h in clustered_highs if h > current_price]
    resistance = min(resistances_above) if resistances_above else max(clustered_highs) if clustered_highs else current_price
    supports_below = [l for l in clustered_lows if l < current_price]
    support = max(supports_below) if supports_below else min(clustered_lows) if clustered_lows else current_price
    return support, resistance

def get_higher_timeframe_trend(candles_list, tf_multiplier=5):
    if len(candles_list) < tf_multiplier * 3:
        return "RANGING"
    htf_closes = []
    for i in range(0, len(candles_list), tf_multiplier):
        chunk = candles_list[i:i + tf_multiplier]
        if len(chunk) == tf_multiplier:
            htf_closes.append(chunk[-1]["close"])
    if len(htf_closes) < 3:
        return "RANGING"
    ema_fast = calc_ema(htf_closes, min(3, len(htf_closes)))
    ema_slow = calc_ema(htf_closes, min(5, len(htf_closes))) if len(htf_closes) >= 5 else None
    if ema_slow is not None:
        if ema_fast > ema_slow:
            return "BULLISH"
        elif ema_fast < ema_slow:
            return "BEARISH"
        return "RANGING"
    if htf_closes[-1] > htf_closes[-2] and htf_closes[-2] > htf_closes[-3]:
        return "BULLISH"
    elif htf_closes[-1] < htf_closes[-2] and htf_closes[-2] < htf_closes[-3]:
        return "BEARISH"
    return "RANGING"

def calculate_sentiment_momentum():
    if len(sentiment_history) < 2:
        return "Neutral"
    now = time.time()
    cutoff = now - 60
    recent = [s for s in sentiment_history if s["time"] >= cutoff]
    if len(recent) < 2:
        recent = list(sentiment_history)
    old_put = recent[0]["put"]
    new_put = recent[-1]["put"]
    diff = new_put - old_put
    if diff > 10:
        return "DOWN"
    elif diff < -10:
        return "UP"
    return "Neutral"

def calculate_smart_money_strength() -> int:
    if not current_smart_money.get("trend"):
        return 0
    sm_time = current_smart_money.get("timestamp")
    if sm_time and (time.time() - sm_time) > 180:
        return 0
    bet_amount = current_smart_money.get("bet_amount", 0)
    if bet_amount > 1000:
        return 4
    elif bet_amount > 500:
        return 3
    elif bet_amount > 100:
        return 2
    return 1

def analyze_timeframe(candle_list) -> dict | None:
    clist = list(candle_list)
    clist = [c for c in clist if isinstance(c, dict) and all(k in c for k in ("open", "high", "low", "close"))]
    closes = [c["close"] for c in clist]
    n = len(closes)
    if n < 2:
        return {"color": "Neutral", "ema_signal": "YATAY", "rsi": 50.0}
    ema9 = calc_ema(closes, 9)
    ema21 = calc_ema(closes, 21)
    rsi = calc_rsi(closes, 14)
    ema_signal = "YATAY"
    if ema9 is not None and ema21 is not None:
        ema_signal = "UP" if ema9 > ema21 else "DOWN"
    last_candle = clist[-1]
    color = "GREEN" if last_candle["close"] >= last_candle["open"] else "RED"
    return {"color": color, "ema_signal": ema_signal, "rsi": round(rsi, 2) if rsi else 50.0}


def analyze_candles() -> dict | None:
    clist = list(candles)
    clist = [c for c in clist if isinstance(c, dict) and all(k in c for k in ("open", "high", "low", "close"))]
    closes = [c["close"] for c in clist]
    highs = [c["high"] for c in clist]
    lows = [c["low"] for c in clist]
    n = len(closes)
    if n < 30:
        return None

    ema9 = calc_ema(closes, 9)
    ema21 = calc_ema(closes, 21)
    rsi = calc_rsi(closes)
    stoch_k, stoch_d = calc_stoch_rsi(closes)
    macd_v, macd_h = calc_macd(closes)
    bb_mid, bb_up, bb_lo = calc_bollinger(closes)
    momentum = calc_momentum(closes)
    atr = calc_atr(clist)
    sar = calc_parabolic_sar(highs, lows)
    price = closes[-1]

    pattern = detect_patterns(clist)
    atr_val = atr if (atr is not None and atr > 0) else 0.0000001
    sup, res = get_support_resistance(clist, tolerance=(atr_val / price))
    htf_trend = get_higher_timeframe_trend(clist, 5)
    sent_mom = calculate_sentiment_momentum()

    spreads = [c["spread_avg"] for c in clist[-5:] if c.get("spread_avg")]
    avg_spread = sum(spreads) / len(spreads) if spreads else 0.0

    ema_signal = "YATAY"
    if ema9 is not None and ema21 is not None:
        ema_signal = "UP" if ema9 > ema21 else "DOWN"

    bb_pos = "LOWER_HALF"
    if bb_up and bb_lo:
        if price > bb_up:
            bb_pos = "ABOVE_UPPER"
        elif price < bb_lo:
            bb_pos = "BELOW_LOWER"
        elif price > bb_mid:
            bb_pos = "UPPER_HALF"

    sup_dist = round(((price - sup) / sup) * 100, 8) if sup else 0.0
    res_dist = round(((res - price) / res) * 100, 8) if res else 0.0
    vol_score = round((atr / price) * 1_000_000_000, 2) if atr is not None and price else 0.0

    obv_proxy = 0.0
    for c in clist:
        if c["close"] >= c["open"]:
            obv_proxy += c.get("tick_count", 0)
        else:
            obv_proxy -= c.get("tick_count", 0)
    obv_prev = 0.0
    for c in clist[:-3]:
        if c["close"] >= c["open"]:
            obv_prev += c.get("tick_count", 0)
        else:
            obv_prev -= c.get("tick_count", 0)
    last_3_obv = obv_proxy - obv_prev
    if last_3_obv > 0:
        obv_trend = "UP"
    elif last_3_obv < 0:
        obv_trend = "DOWN"
    else:
        obv_trend = "FLAT"

    market_regime = detect_market_regime(candles, current_range_coeff)
    fib = calc_fibonacci_status(candles, price)

    try:
        ts_val = int(clist[-1]["time"])
        dt_val = datetime.fromtimestamp(ts_val, tz=timezone.utc)
        hour_of_day = dt_val.hour
        day_of_week = dt_val.weekday()
    except Exception:
        hour_of_day = datetime.now(timezone.utc).hour
        day_of_week = datetime.now(timezone.utc).weekday()

    price_diff_t1 = 0.0
    price_diff_t2 = 0.0
    if len(closes) > 1 and closes[-2] != 0:
        price_diff_t1 = round(((closes[-1] - closes[-2]) / closes[-2]) * 100, 12)
    if len(closes) > 2 and closes[-3] != 0:
        price_diff_t2 = round(((closes[-1] - closes[-3]) / closes[-3]) * 100, 12)

    rsi_diff_t1 = 0.0
    rsi_diff_t2 = 0.0
    if len(closes) > 1:
        prev_rsi = calc_rsi(closes[:-1])
        if rsi is not None and prev_rsi is not None:
            rsi_diff_t1 = round(rsi - prev_rsi, 4)
    if len(closes) > 2:
        prev_2_rsi = calc_rsi(closes[:-2])
        if rsi is not None and prev_2_rsi is not None:
            rsi_diff_t2 = round(rsi - prev_2_rsi, 4)

    macd_hist_slope = 0.0
    if len(closes) > 1:
        _, prev_macd_h = calc_macd(closes[:-1])
        if macd_h is not None and prev_macd_h is not None:
            macd_hist_slope = round(macd_h - prev_macd_h, 12)

    stoch_diff = round(stoch_k - stoch_d, 4) if (stoch_k is not None and stoch_d is not None) else 0.0

    bollinger_pct_b = 0.5
    if bb_up is not None and bb_lo is not None:
        denom = bb_up - bb_lo
        if denom != 0:
            bollinger_pct_b = round((price - bb_lo) / denom, 6)

    ema9_dev = 0.0
    ema21_dev = 0.0
    if ema9 is not None and ema9 != 0:
        ema9_dev = round(((price - ema9) / ema9) * 100, 12)
    if ema21 is not None and ema21 != 0:
        ema21_dev = round(((price - ema21) / ema21) * 100, 12)

    volatility_ratio = 1.0
    atr_50 = calc_atr(clist, 50)
    if atr is not None and atr_50 is not None and atr_50 != 0:
        volatility_ratio = round(atr / atr_50, 6)

    tick_count = clist[-1].get("tick_count", 0)
    last_10_ticks = [c.get("tick_count", 0) for c in clist[-10:]]
    avg_ticks = sum(last_10_ticks) / len(last_10_ticks) if last_10_ticks else 0
    tick_ratio = round(tick_count / avg_ticks, 4) if avg_ticks != 0 else 1.0

    sentiment_change_t1 = 0.0
    if len(sentiment_history) > 1:
        sentiment_change_t1 = float(sentiment_history[-1]["call"] - sentiment_history[-2]["call"])

    res_dict = {
        "timestamp": clist[-1]["time"],
        "close": price,
        "rsi": round(rsi, 2) if rsi is not None else 50.0,
        "macd_line": round(macd_v, 12) if macd_v is not None else 0.0,
        "macd_hist": round(macd_h, 12) if macd_h is not None else 0.0,
        "stoch_k": round(stoch_k, 2) if stoch_k is not None else 50.0,
        "stoch_d": round(stoch_d, 2) if stoch_d is not None else 50.0,
        "ema9": round(ema9, 12) if ema9 is not None else price,
        "ema21": round(ema21, 12) if ema21 is not None else price,
        "ema_signal": ema_signal,
        "bollinger_width": round((calc_bollinger_width(closes, 20) or 0.0) * 1e12, 6),
        "bollinger_position": bb_pos,
        "bollinger_squeeze": 1 if detect_bollinger_squeeze(closes, 20, 40) else 0,
        "sar": round(sar, 12) if sar is not None else price,
        "sar_dev": round(((price - sar) / price) * 100, 12) if price != 0 and sar is not None else 0.0,
        "atr": round(atr, 12) if atr else 0.0,
        "vol_score": vol_score,
        "obv_trend": obv_trend,
        "sentiment_call": current_sentiment["call"],
        "sentiment_put": current_sentiment["put"],
        "sentiment_momentum": sent_mom,
        "pattern": pattern,
        "support_dist_pct": sup_dist,
        "resistance_dist_pct": res_dist,
        "htf_5m_trend": htf_trend,
        "market_regime": market_regime,
        "fibonacci_distance": fib["distance_pct"],
        "fibonacci_warning": 1 if fib["warning"] == "Yakın" else 0,
        "smart_money_trend": current_smart_money.get("trend") or "neutral",
        "smart_money_bet": current_smart_money.get("bet_amount", 0),
        "smart_money_strength": calculate_smart_money_strength(),
        "bid_ask_imbalance": round((avg_spread / price) * 1_000_000_000 if price else 0.0, 4),
        "hour_of_day": hour_of_day,
        "day_of_week": day_of_week,
        "price_diff_t1": price_diff_t1,
        "price_diff_t2": price_diff_t2,
        "rsi_diff_t1": rsi_diff_t1,
        "rsi_diff_t2": rsi_diff_t2,
        "macd_hist_slope": macd_hist_slope,
        "stoch_diff": stoch_diff,
        "bollinger_pct_b": bollinger_pct_b,
        "ema9_dev": ema9_dev,
        "ema21_dev": ema21_dev,
        "volatility_ratio": volatility_ratio,
        "tick_count": tick_count,
        "tick_ratio": tick_ratio,
        "sentiment_change_t1": sentiment_change_t1
    }

    return res_dict

total_saved_count = 0
if os.path.exists(CSV_PATH):
    try:
        with open(CSV_PATH, "r", encoding="utf-8") as f:
            total_saved_count = sum(1 for _ in f) - 1
    except Exception:
        total_saved_count = 0

WARMUP_CANDLE_COUNT = 120
candle_count = 0

last_tick_price = 0.0
last_tick_time = time.time()
active_page = None
is_running = True

def update_cli_stats(last_price=0.0):
    global last_tick_price
    last_tick_price = last_price

def save_row_to_csv(data_row, target_time, future_price, price_change, pnl_result):
    global total_saved_count
    row_data = []
    for col in CSV_HEADERS:
        if col == "target_seconds":
            row_data.append(target_time)
        elif col == "target_price":
            row_data.append(future_price)
        elif col == "price_change":
            row_data.append(round(price_change, 14))
        elif col == "pnl_result":
            row_data.append(pnl_result)
        else:
            val = data_row.get(col)
            if val is None:
                if "pattern" in col:
                    val = "Neutral"
                elif "trend" in col or "signal" in col or "position" in col or "momentum" in col or "regime" in col:
                    val = "Neutral"
                else:
                    val = 0.0
            row_data.append(val)

    with open(CSV_PATH, "a", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(row_data)
    total_saved_count += 1
    update_cli_stats(data_row["close"])

def check_and_save_pending(current_price):
    now = latest_server_timestamp if latest_server_timestamp > 0.0 else time.time()
    for row in list(pending_rows):
        if now >= row["target_timestamp"]:
            if now - row["target_timestamp"] > 10:
                logger.warning(f"[STALE] Vade gecikmesi toleransi asildi! Vade: {datetime.fromtimestamp(row['target_timestamp']).strftime('%H:%M:%S')} | Gecikme: {now - row['target_timestamp']:.1f}s | Kaydedilmeden temizleniyor.")
                pending_rows.remove(row)
                continue

            price_change = current_price - row["close"]
            if price_change > 0:
                pnl_result = 1
            elif price_change < 0:
                pnl_result = 0
            else:
                logger.warning(
                    f"[BERABERLIK] Entry={row['close']:.11f} == Exit={current_price:.11f}"
                )
                pending_rows.remove(row)
                continue
            save_row_to_csv(row, int(row["target_timestamp"]), current_price, price_change, pnl_result)
            pending_rows.remove(row)
            update_cli_stats(current_price)
            logger.info(f"[KAYDETME] Toplam: {total_saved_count} | Vade: {datetime.fromtimestamp(row['target_timestamp']).strftime('%H:%M:%S')} | Entry: {row['close']:.8f} -> Exit: {current_price:.8f} | Sonuc: {pnl_result}")

def add_to_pending(analysis_data):
    try:
        ts = int(analysis_data["timestamp"])
    except Exception:
        ts = int(time.time())
    second_of_minute = ts % 60
    if second_of_minute < 30:
        target_seconds_in_future = 60 - second_of_minute
    else:
        target_seconds_in_future = 120 - second_of_minute
    target_timestamp = ts + target_seconds_in_future
    analysis_data["target_timestamp"] = target_timestamp
    pending_rows.append(analysis_data)
    update_cli_stats(analysis_data["close"])
    logger.info(f"[TAKIP] Mum: {datetime.fromtimestamp(ts).strftime('%H:%M:%S')} -> Vade: {datetime.fromtimestamp(target_timestamp).strftime('%H:%M:%S')} ({target_seconds_in_future}s)")


def close_candle():
    global ticks, current_minute
    global current_5m_bucket, ticks_for_5m, candles_5m
    if len(ticks) < MIN_TICKS:
        ticks = []
        return

    rates = [t["rate"] for t in ticks]
    spreads = [t["ask"] - t["bid"] for t in ticks]

    candle = {
        "time": int(current_minute),
        "open": rates[0],
        "high": max(rates),
        "low": min(rates),
        "close": rates[-1],
        "tick_count": len(ticks),
        "spread_avg": sum(spreads) / len(spreads),
        "std": current_std,
        "radius": current_radius,
    }
    candles.append(candle)
    ticks = []

    try:
        ts = int(candle["time"])
        b5m = (ts // 300) * 300

        if current_5m_bucket is None:
            current_5m_bucket = b5m

        if b5m != current_5m_bucket:
            if ticks_for_5m:
                c5m = {
                    "time": str(current_5m_bucket),
                    "open": ticks_for_5m[0]["open"],
                    "high": max(x["high"] for x in ticks_for_5m),
                    "low": min(x["low"] for x in ticks_for_5m),
                    "close": ticks_for_5m[-1]["close"],
                    "tick_count": sum(x["tick_count"] for x in ticks_for_5m),
                    "spread_avg": sum(x.get("spread_avg", 0.0) for x in ticks_for_5m) / len(ticks_for_5m)
                }
                candles_5m.append(c5m)
                ticks_for_5m = []
            current_5m_bucket = b5m
        ticks_for_5m.append(candle)
    except Exception as e:
        logger.error(f"[TIMEFRAME AGGREGATION HATA] {e}", exc_info=True)

    global candle_count
    candle_count += 1
    if candle_count <= WARMUP_CANDLE_COUNT:
        logger.info(f"[ISINMA] {candle_count}/{WARMUP_CANDLE_COUNT} mum - indikatörler olgunlaşıyor, CSV'ye yazılmıyor.")
        return

    result = analyze_candles()
    if result:
        add_to_pending(result)

def get_candle_key(dt):
    ts = int(dt.timestamp())
    bucket = (ts // CANDLE_SECONDS) * CANDLE_SECONDS
    return str(bucket)

def handle_as_message(payload):
    global current_minute, ticks
    try:
        if isinstance(payload, bytes):
            payload = payload.decode("utf-8")
        data = json.loads(payload) if isinstance(payload, str) else payload
    except Exception as e:
        logger.error(f"[AS WS PARSE HATA] {e}")
        return
    if isinstance(data, dict) and data.get("success"):
        for item in data.get("data", []):
            if item.get("action") == "assets":
                for asset in item.get("assets", []):
                    rate = asset.get("rate")
                    ask = asset.get("ask")
                    bid = asset.get("bid")
                    ts = asset.get("created_at_with_millis") or asset.get("created_at", "")
                    if not rate:
                        continue
                    try:
                        dt = datetime.fromisoformat(ts.replace("Z", "+00:00"))
                        minute = get_candle_key(dt)
                        global latest_server_timestamp
                        latest_server_timestamp = dt.timestamp()
                    except Exception:
                        now_ts = int(time.time())
                        minute = str((now_ts // CANDLE_SECONDS) * CANDLE_SECONDS)

                    if current_minute is None:
                        current_minute = minute
                    if minute != current_minute:
                        close_candle()
                        current_minute = minute

                    ticks.append({"rate": rate, "ask": ask or rate, "bid": bid or rate, "ts": ts})
                    update_cli_stats(rate)
                    check_and_save_pending(rate)
                    global last_tick_time
                    last_tick_time = time.time()

def trigger_ui_update():
    pass

def handle_ws_message(payload):
    global current_sentiment, current_std, current_radius, current_range_coeff
    global current_smart_money, session_start_time, session_range_coefficient
    try:
        if isinstance(payload, bytes):
            payload = payload.decode("utf-8")
        data = json.loads(payload) if isinstance(payload, str) else payload
    except Exception as e:
        logger.error(f"[GENEL WS PARSE HATA] {e}")
        return
    if not isinstance(data, dict):
        return
    event = data.get("event")
    if event == "majority_opinion":
        p = data.get("payload", {})
        current_sentiment["call"] = p.get("call", 50)
        current_sentiment["put"] = p.get("put", 50)
        sentiment_history.append({
            "time": time.time(),
            "call": p.get("call", 50),
            "put": p.get("put", 50)
        })
        trigger_ui_update()
    elif event == "quotes_range":
        p = data.get("payload", {})
        try:
            current_std = float(p.get("std", 0))
            current_radius = float(p.get("radius", 0))
            current_range_coeff = float(p.get("range_coefficient", 1.0))
            session_range_coefficient = current_range_coeff
            session_start_time = p.get("started_at")
            trigger_ui_update()
        except Exception:
            pass
    elif event == "social_trading_deal":
        p = data.get("payload", {})
        try:
            bet_in_currencies = p.get("bet_in_currencies", {})
            usd_bet = bet_in_currencies.get("USD", {}).get("bet", 0)
            normalized_bet = usd_bet / 100.0 if usd_bet else p.get("bet", 0)
            deal = {
                "trend": p.get("trend"),
                "bet_amount": normalized_bet,
                "rate": p.get("entrie_rate"),
                "timestamp": time.time()
            }
            smart_money_history.append(deal)
            current_smart_money = dict(deal)
            if smart_money_history:
                call_bet = sum(d["bet_amount"] for d in smart_money_history if d["trend"] == "call")
                put_bet = sum(d["bet_amount"] for d in smart_money_history if d["trend"] == "put")
                total_bet = call_bet + put_bet
                dominant = "call" if call_bet >= put_bet else "put"
                current_smart_money["trend"] = dominant
                current_smart_money["bet_amount"] = total_bet / len(smart_money_history)
            trigger_ui_update()
        except Exception as e:
            logger.debug(f"[SOCIAL TRADING PARSE] {e}")

async def status_reporter():
    while is_running:
        await asyncio.sleep(10)
        sentiment_str = f"CALL {current_sentiment['call']}% | PUT {current_sentiment['put']}%"
        logger.info(f"[DURUM] Kaydedilecek Mumlar: {total_saved_count} | Fiyat: {last_tick_price:.8f} | Bekleyen: {len(pending_rows)} | Egilim: {sentiment_str}")

async def watchdog_task():
    global last_tick_time, active_page, restart_browser
    last_tick_time = time.time()
    while is_running:
        await asyncio.sleep(15)
        if time.time() - last_tick_time > 60:
            logger.warning("[WATCHDOG] 60 saniyedir yeni tick gelmedi! Tarayici donmus veya baglanti kopmus olabilir. Sayfa yenileniyor...")
            last_tick_time = time.time()
            if active_page:
                try:
                    await active_page.reload()
                    logger.info("[WATCHDOG] Sayfa basariyla yenilendi.")
                    await guvenlik_kontrolu(active_page, wait_seconds=10)
                except Exception as e:
                    logger.error(f"[WATCHDOG HATA] Sayfa yenilenirken hata olustu (tarayici tamamen cokmus olabilir): {e}")
                    logger.warning("[WATCHDOG] Tarayici yeniden baslatma sinyali gonderiliyor...")
                    restart_browser = True

async def _cloudflare_id_bul(page) -> str:
    try:
        cf_id = await page.evaluate("""
            (function() {
                let iframe = document.querySelector('iframe[src*="challenges.cloudflare.com"]');
                if (iframe) {
                    let parent = iframe.parentElement;
                    while (parent && parent !== document.body) {
                        if (parent.tagName === 'DIV') {
                            if (!parent.id) {
                                parent.id = 'cf-turnstile-auto-' + Math.floor(Math.random() * 1000000);
                            }
                            return parent.id;
                        }
                        parent = parent.parentElement;
                    }
                    if (!iframe.id) {
                        iframe.id = 'cf-iframe-auto-' + Math.floor(Math.random() * 1000000);
                    }
                    return iframe.id;
                }
                let input = document.querySelector('input[name="cf-turnstile-response"]');
                if (input) {
                    let parent = input.parentElement;
                    while (parent && parent !== document.body) {
                        if (parent.tagName === 'DIV') {
                            if (!parent.id) {
                                parent.id = 'cf-turnstile-auto-' + Math.floor(Math.random() * 1000000);
                            }
                            return parent.id;
                        }
                        parent = parent.parentElement;
                    }
                }
                let turnstileEl = document.querySelector('.cf-turnstile, #cf-turnstile, [class*="turnstile"]');
                if (turnstileEl) {
                    if (!turnstileEl.id) {
                        turnstileEl.id = 'cf-turnstile-auto-' + Math.floor(Math.random() * 1000000);
                    }
                    return turnstileEl.id;
                }
                return null;
            })()
        """)
        if cf_id:
            logger.info(f"Dinamik Cloudflare ID tespit edildi: {cf_id}")
        return cf_id
    except Exception as e:
        logger.error(f"Cloudflare ID bulma hatası: {e}")
        return None

async def guvenlik_kontrolu(page, wait_seconds=12) -> bool:
    global _cf_bypass_running, _last_cf_solve_time
    if _cf_bypass_running:
        return False

    import time
    if time.time() - _last_cf_solve_time < 10:
        return False

    _cf_bypass_running = True
    try:
        logger.info(f"[CLOUDFLARE] Cloudflare Turnstile kontrol ediliyor (azami {wait_seconds}s bekleniyor)...")
        start_wait = time.time()
        cf_id = None
        while time.time() - start_wait < wait_seconds:
            cf_id = await _cloudflare_id_bul(page)
            if cf_id:
                break
            await asyncio.sleep(1.0)

        if not cf_id:
            logger.info("[CLOUDFLARE] Cloudflare Turnstile elementi bulunamadı (Sayfa temiz).")
            return False

        logger.info(f"[CLOUDFLARE] Cloudflare Turnstile tespit edildi (ID: {cf_id}), bypass mekanizması başlatılıyor.")

        await page.evaluate("""
            () => {
                let input = document.querySelector('input[name="cf-turnstile-response"]');
                if (input) input.value = "";
            }
        """)

        max_deneme = 3
        deneme = 0
        while deneme < max_deneme:
            deneme += 1
            logger.info(f"Cloudflare bypass denemesi: {deneme}/{max_deneme}")

            rect = await page.evaluate(f"""
                (function() {{
                    let iframe = document.querySelector('iframe[src*="challenges.cloudflare.com"]');
                    let target = iframe || document.getElementById('{cf_id}');
                    if (!target) return null;
                    let r = target.getBoundingClientRect();
                    return [r.x, r.y, r.width, r.height];
                }})()
            """)

            if not rect or not isinstance(rect, list) or len(rect) < 4 or rect[2] == 0 or rect[3] == 0:
                logger.warning(f"Cloudflare Turnstile koordinatları alınamadı (Deneme {deneme}).")
                await asyncio.sleep(2)
                continue

            def get_val(item):
                if isinstance(item, dict) and 'value' in item:
                    return item['value']
                return item

            x_coord = get_val(rect[0])
            y_coord = get_val(rect[1])
            h_coord = get_val(rect[3])

            x = int(x_coord + 35)
            y = int(y_coord + h_coord / 2)

            await page.send(cdp_input.dispatch_mouse_event(
                type_='mouseMoved', x=x, y=y, button=cdp_input.MouseButton.NONE
            ))
            await asyncio.sleep(0.3)
            await page.send(cdp_input.dispatch_mouse_event(
                type_='mousePressed', x=x, y=y, button=cdp_input.MouseButton.LEFT, click_count=1
            ))
            await asyncio.sleep(0.1)
            await page.send(cdp_input.dispatch_mouse_event(
                type_='mouseReleased', x=x, y=y, button=cdp_input.MouseButton.LEFT, click_count=1
            ))
            logger.info(f"Cloudflare checkbox'ına tıklandı (CDP mouse: x={x}, y={y}).")

            start_time = time.time()
            timeout = 15
            while time.time() - start_time < timeout:
                await asyncio.sleep(2)

                turnstile_response_dolu = await page.evaluate("""
                    () => {
                        let input = document.querySelector('input[name="cf-turnstile-response"]');
                        return !!(input && input.value && input.value.length > 0);
                    }
                """)

                cf_element_kayboldu_mu = await page.evaluate(f"""
                    () => {{
                        let el = document.getElementById('{cf_id}');
                        if (!el) return true;
                        let style = window.getComputedStyle(el);
                        return el.offsetWidth === 0 || el.offsetHeight === 0 || style.display === 'none' || style.visibility === 'hidden';
                    }}
                """)

                url_changed = await page.evaluate("""
                    () => !window.location.href.includes('__cf_chl_rt_tk')
                """)

                if turnstile_response_dolu or cf_element_kayboldu_mu or url_changed:
                    logger.info("Cloudflare Turnstile başarıyla geçildi ve doğrulandı.")
                    _last_cf_solve_time = time.time()
                    await asyncio.sleep(3)
                    return True

            logger.warning(f"Cloudflare doğrulama {timeout} saniye içinde tamamlanamadı.")

        logger.error(f"Cloudflare Turnstile {max_deneme} denemede de geçilemedi.")
        return False
    finally:
        _cf_bypass_running = False

ws_connection_urls = {}

def on_ws_created(event: cdp_network.WebSocketCreated):
    ws_connection_urls[event.request_id] = event.url
    logger.info(f"[WS TESPIT EDILDI] RequestID: {event.request_id} | URL: {event.url}")
    if "as.binomo.com" in event.url:
        logger.info("[WS] Fiyat akisi (as.binomo.com) baglandi!")
    elif "binomo.com" in event.url or "bn." in event.url:
        logger.info(f"[WS] Genel Binomo WS baglandi: {event.url}")

def on_ws_frame_received(event: cdp_network.WebSocketFrameReceived):
    payload = event.response.payload_data
    url = ws_connection_urls.get(event.request_id, "")
    if "as.binomo.com" in url:
        handle_as_message(payload)
    else:
        handle_ws_message(payload)

async def _launch_browser_session(storage_state):
    global active_page

    user_data_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "browser_data")
    chrome_path = "/usr/bin/google-chrome" if os.path.exists("/usr/bin/google-chrome") else None
    start_kwargs = {
        "headless": False,
        "sandbox": False,
        "browser_args": [
            "--window-size=1280,800",
            "--no-sandbox",
            "--disable-setuid-sandbox",
            "--disable-dev-shm-usage",
            f"--user-data-dir={user_data_dir}"
        ]
    }
    if chrome_path:
        start_kwargs["browser_executable_path"] = chrome_path

    browser = await uc.start(**start_kwargs)

    page = browser.main_tab
    active_page = page

    page.add_handler(cdp_network.WebSocketCreated, on_ws_created)
    page.add_handler(cdp_network.WebSocketFrameReceived, on_ws_frame_received)

    if storage_state:
        try:
            with open(storage_state, "r", encoding="utf-8") as f:
                state = json.load(f)
            cookies = state.get("cookies", [])
            if cookies:
                for c in cookies:
                    try:
                        name = c.get("name")
                        value = c.get("value")
                        domain = c.get("domain")
                        if name and value:
                            await page.send(cdp_network.set_cookie(name=name, value=value, domain=domain))
                    except Exception:
                        pass
                logger.info(f"[AUTH] {len(cookies)} adet cerez basariyla enjekte edildi.")
        except Exception as e:
            logger.error(f"[AUTH HATA] Cerezler enjekte edilirken hata: {e}")

    logger.info(">>> Binomo platformu arka planda yukleniyor...")
    try:
        page = await browser.get(BINOMO_URL)
        active_page = page
    except Exception as e:
        logger.error(f"[GOTO HATA] {e}")

    bypass_result = await guvenlik_kontrolu(page, wait_seconds=12)
    if bypass_result:
        logger.info("[CLOUDFLARE] Cloudflare Turnstile gecildi. Platformun WebSocket akisini baslatmasi icin sayfa yenileniyor...")
        try:
            await page.reload()
            await asyncio.sleep(3)
        except Exception as e:
            logger.error(f"[RELOAD HATA] {e}")

    current_url = getattr(page, 'url', BINOMO_URL)
    logger.info(f"[SAYFA URL] Yuklenen sayfa: {current_url}")

    if "sign-in" in str(current_url) or "login" in str(current_url) or "auth" in str(current_url):
        logger.warning("[LOGIN] UYARI: Sayfa login sayfasina yonlendirdi! auth.json veya profil gecersiz olmis olabilir.")
    elif "trade" in str(current_url):
        logger.info("[LOGIN] Sayfa trading platformunda gorünüyor. [OK]")
    else:
        logger.info(f"[LOGIN] Sayfa durumu belirsiz (oturum acilmamis olabilir): {current_url}")

    return browser, page

async def run_collector():
    global restart_browser, last_tick_time, is_running
    is_ci = os.environ.get("CI") or os.environ.get("GITHUB_ACTIONS")
    if is_ci:
        logger.info("[CI/CD] GitHub Actions ortami tespit edildi.")

    auth_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "auth.json")
    storage_state = auth_path if os.path.exists(auth_path) else None
    if storage_state:
        logger.info("[AUTH] auth.json dosyasi bulundu, oturum verileri enjekte edilecek.")

    start_time = time.time()
    max_run_time = int(os.environ.get("MAX_RUN_TIME_SECONDS", 20400))
    logger.info(f"[BASLANGIC] Maksimum calisme suresi: {max_run_time} saniye ({(max_run_time / 3600):.2f} saat) olarak belirlendi.")

    browser, page = await _launch_browser_session(storage_state)
    logger.info(">>> WebSocket akisi dinleniyor. Veri toplama aktif! [OK]")

    asyncio.create_task(status_reporter())
    asyncio.create_task(watchdog_task())

    while is_running:
        try:
            if time.time() - start_time >= max_run_time:
                logger.info(f"[TIMEOUT] Maksimum calisme suresi doldu ({max_run_time} saniye). Uygulama guvenli sekilde kapatiliyor...")
                is_running = False
                break

            if restart_browser:
                restart_browser = False
                logger.warning("[RESTART] Tarayici oturumu kapatiliyor, 5 saniye bekleniyor...")
                try:
                    await browser.stop()
                except Exception:
                    pass

                await asyncio.sleep(5)
                logger.info("[RESTART] Yeni tarayici oturumu baslatiliyor...")
                try:
                    browser, page = await _launch_browser_session(storage_state)
                    last_tick_time = time.time() 
                    logger.info("[RESTART] Tarayici basariyla yeniden baslatildi. [OK]")
                except Exception as e:
                    logger.error(f"[RESTART HATA] Yeniden baslatilamadi: {e}. 30 saniye sonra tekrar denenecek.")
                    restart_browser = True  
                    await asyncio.sleep(30)

            await asyncio.sleep(1)

        except Exception as e:
            logger.error(f"[COLLECTOR HATA] Ana dongu hatasi: {e}")
            await asyncio.sleep(5)

    try:
        await browser.stop()
    except Exception:
        pass

def main():
    global is_running
    logger.info("Veri toplayici basliyor. Durdurmak icin Ctrl+C kullanin.")
    try:
        asyncio.run(run_collector())
    except KeyboardInterrupt:
        pass
    except Exception as e:
        logger.error(f"Kritik Hata: {e}")
    finally:
        is_running = False
        print("Uygulama kapatildi.")
        sys.exit(0)

if __name__ == "__main__":
    main()
