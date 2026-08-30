#!/usr/bin/env python3
"""
monbus_halfbeat_model.py — measure half-beat (32-bit slot) packing vs the
current 64-bit-slot compressor, on either a synthetic workload or a real
captured monbus trace.

Why this exists
---------------
The current compressor (bin/TBClasses/monbus/monbus_compressor.py) emits one
64-bit beat per tier-1 record and 3 beats per raw escape, so its reduction is
structurally capped at 66.7% (1 - 1/3) and only reaches that ceiling when
*every* record is a tier-1 hit. Half-beat packing puts two 32-bit records in
one beat (0.5 beat/record), raising the ceiling to 83.3% (1 - 0.5/3).

But the realized ratio is dominated by the tier-1 hit rate h, not the slot
size:   reduction = h * (1 - b_t/3)
        current  (b_t=1.0): h * 0.667
        halfbeat (b_t=0.5): h * 0.833
So 80% needs h ~= 0.96. This tool reports h and the realized ratio for both
codecs so we can see whether half-beat is worth the RTL on the ACTUAL traffic.

The CAM / per-template-delta_ts classification here is a faithful re-use of
the committed Encoder logic, so a record is counted "tier-1" iff the real
compressor would have compressed it.

Run:
    source env_python
    python3 host/monbus_halfbeat_model.py            # synthetic envelope
    python3 host/monbus_halfbeat_model.py trace.json  # real captured trace
"""
from __future__ import annotations

import sys
from dataclasses import dataclass
from typing import List, Tuple

from TBClasses.monbus.monbus_compressor import (
    Cam, TemplateKey, _key_from_packet, _field, _make_packet,
    TS_STORE, DELTA_TS_A, DELTA_TS_B, DELTA_TS_C,
    EVENT_DATA_A, EVENT_DATA_B, EVENT_DATA_C_DELTA,
    _EVENT_DATA_HI, _EVENT_DATA_LO,
    MONBUS_PKT_WIDTH, MONBUS_TS_WIDTH, DEFAULT_CAM_SIZE,
)

# ---------------------------------------------------------------------------
# Half-beat slot budgets.  A half-pair beat is {tag[63:60]=0x4, slotA[59:30],
# slotB[29:0]} -> two 30-bit slots.  Each slot = sub(2) + idx(5) + payload(23).
# Two variants cover the two compressible shapes; a record is "half" iff it
# fits either.  These are the field widths the RTL/golden lock.
# ---------------------------------------------------------------------------
HALF_TAG_BITS = 2            # per-slot sub-format tag
HALF_IDX_BITS = 5            # 32-entry CAM index
HALF_PAYLOAD  = 23           # 30-bit slot - 2 sub - 5 idx
# HALF-A: absolute small event_data + small delta_ts
HALF_A_DELTA = 10            # delta_ts < 1024
HALF_A_ED    = HALF_PAYLOAD - HALF_A_DELTA   # event_data < 2^13
# HALF-C: signed event_data delta + small delta_ts (counters / addresses)
HALF_C_DELTA = 10            # delta_ts < 1024
HALF_C_EDD   = HALF_PAYLOAD - HALF_C_DELTA   # |ed_delta| < 2^12

assert HALF_TAG_BITS + HALF_IDX_BITS + HALF_A_DELTA + HALF_A_ED == 30
assert HALF_TAG_BITS + HALF_IDX_BITS + HALF_C_DELTA + HALF_C_EDD == 30

RAW = "raw"
FULL = "full"      # tier-1 but only fits a 64-bit slot
HALF = "half"      # fits a 32-bit slot


@dataclass
class Result:
    records: int = 0
    tier1: int = 0        # full + half (anything the current codec compresses)
    half: int = 0
    full: int = 0
    raw: int = 0
    beats_current: int = 0     # 64-bit beats, current codec (1 / tier1, 3 / raw)
    beats_halfbeat: int = 0    # 64-bit beats, half-beat codec

    @property
    def h(self) -> float:
        return self.tier1 / self.records if self.records else 0.0

    def _red(self, beats: int) -> float:
        raw_baseline = self.records * 3
        return 1.0 - beats / raw_baseline if raw_baseline else 0.0

    @property
    def red_current(self) -> float:
        return self._red(self.beats_current)

    @property
    def red_halfbeat(self) -> float:
        return self._red(self.beats_halfbeat)


def classify(records: List[Tuple[int, int]], cam_size: int = DEFAULT_CAM_SIZE) -> Result:
    """Replay the stream through a per-template CAM (same rules as the committed
    Encoder) and tally cost classes + packed beats for both codecs."""
    cam = Cam(cam_size)
    r = Result()
    half_pending = False   # a 32-bit slot waiting for its partner in the beat

    def flush_half():
        nonlocal half_pending
        if half_pending:
            r.beats_halfbeat += 1   # lone half rounds up to a full beat
            half_pending = False

    for packet, ts in records:
        r.records += 1
        packet &= (1 << MONBUS_PKT_WIDTH) - 1
        ts &= (1 << MONBUS_TS_WIDTH) - 1
        key = _key_from_packet(packet)
        event_data = _field(packet, _EVENT_DATA_HI, _EVENT_DATA_LO)
        ts_lo = ts & ((1 << TS_STORE) - 1)

        # peek without LRU touch (mirror Encoder._cam_peek)
        idx = next((i for i, e in enumerate(cam.entries) if e.key == key), None)
        klass = RAW
        if idx is not None:
            e = cam.entries[idx]
            delta_ts = (ts_lo - e.last_ts) & ((1 << TS_STORE) - 1)
            ed_delta = event_data - e.last_event_data
            # --- is it tier-1 at all (current 64-bit codec)? ---
            fits_a = delta_ts < (1 << DELTA_TS_A) and event_data < (1 << EVENT_DATA_A)
            fits_b = delta_ts < (1 << DELTA_TS_B) and event_data < (1 << EVENT_DATA_B)
            cd_lo, cd_hi = -(1 << (EVENT_DATA_C_DELTA - 1)), (1 << (EVENT_DATA_C_DELTA - 1))
            fits_c = delta_ts < (1 << DELTA_TS_C) and (cd_lo <= ed_delta < cd_hi)
            if fits_a or fits_b or fits_c:
                # --- does it also fit a 32-bit half-slot? ---
                half_a = delta_ts < (1 << HALF_A_DELTA) and event_data < (1 << HALF_A_ED)
                hc_lo, hc_hi = -(1 << (HALF_C_EDD - 1)), (1 << (HALF_C_EDD - 1))
                half_c = delta_ts < (1 << HALF_C_DELTA) and (hc_lo <= ed_delta < hc_hi)
                klass = HALF if (half_a or half_c) else FULL
            # tier-1 hit updates CAM (move-to-front + last_ed/last_ts)
            cam.entries.pop(idx)
            e.last_event_data = event_data
            e.last_ts = ts_lo
            cam.entries.insert(0, e)
        else:
            cam.install(key, event_data, ts_lo)

        # --- tally ---
        if klass == RAW:
            r.raw += 1
            r.beats_current += 3
            flush_half()
            r.beats_halfbeat += 3
        elif klass == FULL:
            r.tier1 += 1
            r.full += 1
            r.beats_current += 1
            flush_half()
            r.beats_halfbeat += 1
        else:  # HALF
            r.tier1 += 1
            r.half += 1
            r.beats_current += 1
            if half_pending:
                r.beats_halfbeat += 1   # completes the pair -> 1 beat for 2 slots
                half_pending = False
            else:
                half_pending = True
    flush_half()
    return r


# ---------------------------------------------------------------------------
# Synthetic workload — interleaved per-channel completions, monotonic ts.
# event_data model is parameterizable since it dominates half-slot fit.
# ---------------------------------------------------------------------------
def synth(num_channels: int, records_per_ch: int, ed_mode: str,
          gap: int = 40, seed: int = 1) -> List[Tuple[int, int]]:
    import random
    rng = random.Random(seed)
    out: List[Tuple[int, int]] = []
    ed_state = {c: rng.randrange(1 << 20) for c in range(num_channels)}
    ts = 0
    for n in range(records_per_ch):
        for c in range(num_channels):
            ts += gap + rng.randrange(gap)        # monotonic, jittered
            if ed_mode == "const":
                ed = 0x1000                        # unchanged per template
            elif ed_mode == "counter":
                ed_state[c] += rng.randrange(1, 8)  # small monotonic delta
                ed = ed_state[c]
            elif ed_mode == "latency":
                ed = 200 + rng.randrange(-30, 30)   # small absolute, jittery
            else:  # "random" — large 40-bit values
                ed = rng.randrange(1 << 40)
            pkt = _make_packet(packet_type=0x1, protocol=0x0, event_code=0x10,
                               channel_id=c, agent_id=0, unit_id=0, event_data=ed)
            out.append((pkt, ts))
    return out


def _print(title: str, r: Result):
    print(f"\n=== {title} ===")
    print(f"  records={r.records}  tier1_hit_rate h={r.h:.3f}  "
          f"(half={r.half} full={r.full} raw={r.raw})")
    print(f"  current  : {r.beats_current:6d} beats  -> {r.red_current*100:5.1f}% reduction")
    print(f"  half-beat: {r.beats_halfbeat:6d} beats  -> {r.red_halfbeat*100:5.1f}% reduction")


def load_trace(path: str) -> List[Tuple[int, int]]:
    """Load (packet, ts) pairs from a capture_raw_trace.py JSON dump."""
    import json
    doc = json.load(open(path))
    recs = doc["records"] if isinstance(doc, dict) else doc
    return [(int(p), int(t)) for p, t in recs]


def main(argv: List[str]):
    if len(argv) > 1:
        for path in argv[1:]:
            recs = load_trace(path)
            _print(f"REAL TRACE {path} ({len(recs)} records)", classify(recs))
        return
    print("SYNTHETIC ENVELOPE (ceiling: current 66.7%, half-beat 83.3%)")
    for nch in (1, 4):
        for mode in ("const", "counter", "latency", "random"):
            r = classify(synth(nch, 400, mode))
            _print(f"{nch}ch / event_data={mode}", r)


if __name__ == "__main__":
    main(sys.argv)
