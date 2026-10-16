#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
""" amber perf sweep - board-level performance analysis for the amber pair rig.

Analogous to the stream perf analysis: where stream's perf_profiler records
per-channel elapsed times and software post-processes them, this sweep
characterizes the amber MESI L1 pair on silicon from telemetry the board
already has:

  - MonBus tally bins (hit / miss / snoop / AXI read / AXI write) per run,
    taken as DIFFERENCES (tally_clear is tied off in amber_pair_harness, so
    counts accumulate across runs; per-run counts = after - before).
  - Injector acc/rsp counts + CRC-32s (integrity and determinism).
  - Tally first-event latch bank: exactly one shot per board reset (the
    bank has no clear), used to capture the first four MonBus events of one
    run with 90 MHz hardware timestamps and full 64-bit addresses.

The sweep matrix walks region size (working set vs the 32 KB cache
capacity), write mix, and sharing to expose the paths the fixed 4 KB smoke
never reaches: capacity/conflict misses, victim selection, dirty evictions
(AXI write monlite bin), and replacement under thrash.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time
from datetime import datetime, timezone

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "bin"))
import amber_env  # noqa: F401  (path setup before shared-layer imports)
sys.path.insert(0, os.path.join(amber_env.repo_root(), "bin"))

from amber_board import (AmberDriver, build_amber_bridge,
                         build_default_profile, harness_probe,
                         open_amber_link, TALLY_CFGR_BASE, TALLY_CFGW_BASE)

SEED0 = 0x1234_5678
SEED1 = 0xDEAD_BEEF

# cfgr-aperture offsets decoded in monbus_tally_axil but not present in the
# RDL regmap (read raw through the bridge).
CFGR_LATCH_STATUS = 0x10   # {latch_valid, latch_fill}
CFGR_LATCH_PKT0   = 0x18   # packet[31:0]
CFGR_LATCH_PKT1   = 0x20   # packet[63:32]
CFGR_LATCH_PKT2   = 0x28   # packet[95:64]
CFGR_LATCH_PKT3   = 0x30   # packet[127:96]
CFGR_LATCH_TS0    = 0x38   # timestamp[31:0]
CFGR_LATCH_TS1    = 0x40   # timestamp[63:32]

_PROTO_NAMES = {0: "AXI", 1: "AXIS", 2: "APB", 3: "ARB",
                4: "CORE", 5: "WB", 6: "CXS"}
_CORE_EVENTS = {0x00: "hit", 0x01: "miss", 0x02: "snoop"}


def _decode_packet(words, ts):
    pkt = (words[3] << 96) | (words[2] << 64) | (words[1] << 32) | words[0]
    return {
        "pkt_type":  (pkt >> 124) & 0xF,
        "protocol":  _PROTO_NAMES.get((pkt >> 105) & 0xF, "?"),
        "event":     _CORE_EVENTS.get((pkt >> 97) & 0xFF,
                                      f"0x{(pkt >> 97) & 0xFF:02x}"),
        "agent":     f"0x{(pkt >> 72) & 0xFFFF:04x}",
        "unit":      (pkt >> 64) & 0xFF,
        "addr":      f"0x{pkt & 0xFFFFFFFFFFFFFFFF:016x}",
        "ts_cycles": ts,
    }


def _read_bins(driver):
    tally = driver.bus["tally_cnt"]
    bins = [tally.read(f"COUNT{i}") for i in range(12)]
    return bins, tally.read("UNEXPECTED")


def _latch_capture(driver):
    """Read back the first-event latch bank (assumes WATCH armed + filled)."""
    cfgw = driver.bus["tally_cfgw"]
    status = driver.bridge.read(TALLY_CFGR_BASE + CFGR_LATCH_STATUS)
    fill = status & 0xFFFF
    events = []
    for i in range(4):
        cfgw.write("LATCH_SEL", SEL=i)
        words = [driver.bridge.read(TALLY_CFGR_BASE + off) for off in
                 (CFGR_LATCH_PKT0, CFGR_LATCH_PKT1,
                  CFGR_LATCH_PKT2, CFGR_LATCH_PKT3)]
        ts_lo = driver.bridge.read(TALLY_CFGR_BASE + CFGR_LATCH_TS0)
        ts_hi = driver.bridge.read(TALLY_CFGR_BASE + CFGR_LATCH_TS1)
        events.append(_decode_packet(words, (ts_hi << 32) | ts_lo))
    return {"fill": fill, "events": events}


CONFIGS = [
    # name,            mask,      base0,    base1,    we_mix, latch
    ("smoke4k_we64",   0x000FFF, 0x00000, 0x00000, 64, False),
    ("r4k_we0",        0x000FFF, 0x00000, 0x00000, 0, False),
    ("r4k_we255",      0x000FFF, 0x00000, 0x00000, 255, False),
    ("r1k_we64",       0x0003FF, 0x00000, 0x00000, 64, False),
    ("r64b_we64",      0x00003F, 0x00000, 0x00000, 64, False),
    ("r16k_we64",      0x003FFF, 0x00000, 0x00000, 64, False),
    ("r64k_we64",      0x00FFFF, 0x00000, 0x00000, 64, True),
    ("r64k_we255",     0x00FFFF, 0x00000, 0x00000, 255, False),
    ("r128k_we64",     0x01FFFF, 0x00000, 0x00000, 64, False),
    ("disjoint64k_we64", 0x00FFFF, 0x00000, 0x40000, 64, False),
    ("smoke4k_we64_repeat", 0x000FFF, 0x00000, 0x00000, 64, False),
]


def run_sweep(driver, *, count, configs=None, settle=0.25, say=print):
    names = set(configs) if configs else None
    driver.clear_and_load_profile(build_default_profile())
    results = []
    for name, mask, base0, base1, we_mix, do_latch in CONFIGS:
        if names and name not in names:
            continue
        say(f"[sweep] {name}: count={count} mask=0x{mask:06x} "
            f"bases=0x{base0:05x}/0x{base1:05x} we_mix={we_mix}")

        if do_latch:
            driver.bus["tally_cfgw"].write("WATCH_CTRL", ARM=1, MASK=0x0001)

        bins_before, unc_before = _read_bins(driver)
        driver.configure_ci("ci0", seed=SEED0, addr_base=base0,
                            addr_mask=mask, count=count, we_mix=we_mix)
        driver.configure_ci("ci1", seed=SEED1, addr_base=base1,
                            addr_mask=mask, count=count, we_mix=we_mix)
        t0 = time.monotonic()
        driver.start_all()
        ok = driver.wait_done(timeout=180.0)
        wall = time.monotonic() - t0
        time.sleep(settle)  # let the MonBus path drain before snapshotting

        bins_after, unc_after = _read_bins(driver)
        delta = [a - b for a, b in zip(bins_after, bins_before)]
        unc = unc_after - unc_before

        st0 = driver.ci_status("ci0")
        st1 = driver.ci_status("ci1")
        crc0 = driver.ci_crcs("ci0")
        crc1 = driver.ci_crcs("ci1")

        rec = {
            "config": name, "count": count, "mask": f"0x{mask:06x}",
            "base0": f"0x{base0:05x}", "base1": f"0x{base1:05x}",
            "we_mix": we_mix, "done": ok, "wall_s": round(wall, 3),
            "delta_bins": delta, "unexpected": unc,
            "ci0": {**st0, **crc0}, "ci1": {**st1, **crc1},
        }
        if do_latch:
            rec["latch"] = _latch_capture(driver)
        results.append(rec)

        hits, misses, snoops, evicts, drops = delta[0], delta[1], delta[2], \
            delta[3], delta[4]
        fill_end, drain_end = delta[7], delta[9]
        # Hit events fire once per SERVED access (post-miss replays re-hit),
        # so bin0 = total accesses; true miss rate = miss/accesses.
        say(f"  acc={hits} miss={misses} snoop={snoops} evict={evicts} "
            f"drop={drops} fill_end={fill_end} drain_end={drain_end} "
            f"unc={unc} "
            f"miss%={100.0 * misses / hits if hits else 0:.1f} "
            f"wall={wall:.2f}s err={st0['err_flag'] or st1['err_flag']}")
        if unc != 0 or st0["err_flag"] or st1["err_flag"] or not ok:
            say(f"[sweep] WARNING {name}: unexpected/err/timeout flag set")

    return results


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.strip().splitlines()[0])
    ap.add_argument("--port", default=None)
    ap.add_argument("--baud", type=int, default=115200)
    ap.add_argument("--board", default="genesys2")
    ap.add_argument("--count", type=int, default=20000)
    ap.add_argument("--configs", nargs="+", default=None,
                    help="run only these named configs")
    ap.add_argument("--out", default=None,
                    help="JSON results path (default: results/perf_sweep_*.json")
    args = ap.parse_args(argv)

    link = open_amber_link(args.port, board_name=args.board,
                           baudrate=args.baud)
    bridge = build_amber_bridge(link)
    driver = AmberDriver(bridge)
    try:
        results = run_sweep(driver, count=args.count,
                            configs=args.configs)
    finally:
        bridge.close()

    if args.out:
        out = args.out
    else:
        stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
        out = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "..", "results", f"perf_sweep_{stamp}.json")
    os.makedirs(os.path.dirname(out), exist_ok=True)
    with open(out, "w") as fh:
        json.dump({"count": args.count, "results": results}, fh, indent=2)
    print(f"[sweep] results written to {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
