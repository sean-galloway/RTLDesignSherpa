#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
""" amber perf sweep - board-level performance analysis for the amber pair rig.

Analogous to the stream perf analysis: where stream's perf_profiler records
per-channel elapsed times and software post-processes them, this sweep
characterizes the amber MESI L1 pair on silicon from telemetry the board
already has:

  - MonBus tally bins (hit / miss / snoop / AXI read / AXI write) per run.
    harness CSR CTRL drives monbus_tally_axil directly (CTRL[0]=clear W1P,
    CTRL[1]=freeze level), so each run is a clean window: settle, freeze,
    read, clear. No before/after subtraction.
  - Injector acc/rsp counts + CRC-32s (integrity and determinism).
  - Tally first-event latch bank: re-armed by every tally_clear (the clear
    walk resets latch_fill), so any config with latch=True captures its own
    first four MonBus events with 90 MHz hardware timestamps and full
    64-bit addresses.

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

# cfgr-aperture latch readback offsets used to be raw bridge reads; they are
# named registers in the regenerated tally_regs regmap (TASK-001 item 4).

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
    """Read back the first-event latch bank (assumes WATCH armed + filled).

    The latch readback words are named registers in the regenerated
    tally_regs regmap (formal/amber TASK-001 item 4); FILL says how many of
    the 16 slots hold events."""
    cfgw = driver.bus["tally_cfgw"]
    cfgr = driver.bus["tally_cfgr"]
    fill = cfgr.read("LATCH_STATUS") & 0xFFFF
    events = []
    for i in range(min(fill, 16)):
        cfgw.write("LATCH_SEL", SEL=i)
        words = [cfgr.read(n) for n in
                 ("LATCH_PKT0", "LATCH_PKT1", "LATCH_PKT2", "LATCH_PKT3")]
        ts = (cfgr.read("LATCH_TS_HI") << 32) | cfgr.read("LATCH_TS_LO")
        events.append(_decode_packet(words, ts))
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


def run_sweep(driver, *, count, configs=None, settle=0.25, say=print,
              outstanding=(1,), ci1_idle=False):
    """Walk CONFIGS at each injector depth in `outstanding` (TASK-002).

    The issued sequence is depth-invariant, so every config's CRCs must be
    identical across depths; run cycles, latency and the MLP counters are
    what change."""
    names = set(configs) if configs else None
    driver.clear_and_load_profile(build_default_profile())
    driver.tally_clear()  # start from zeroed bins; each run below re-clears
    results = []
    for depth in outstanding:
        for name, mask, base0, base1, we_mix, do_latch in CONFIGS:
            if names and name not in names:
                continue
            say(f"[sweep] {name}: count={count} mask=0x{mask:06x} "
                f"bases=0x{base0:05x}/0x{base1:05x} we_mix={we_mix} "
                f"outstanding={depth}")

            if do_latch:
                driver.bus["tally_cfgw"].write("WATCH_CTRL", ARM=1, MASK=0x0001)

            driver.configure_ci("ci0", seed=SEED0, addr_base=base0,
                                addr_mask=mask, count=count, we_mix=we_mix,
                                outstanding=depth)
            # --ci1-idle: the second injector runs zero transactions (done at
            # start), so the first cache sees no peer traffic -- the single-
            # core, like-for-like point against the reference rig (TASK-003)
            driver.configure_ci("ci1", seed=SEED1, addr_base=base1,
                                addr_mask=mask, count=0 if ci1_idle else count,
                                we_mix=we_mix, outstanding=depth)
            t0 = time.monotonic()
            driver.start_all()
            ok = driver.wait_done(timeout=180.0)
            wall = time.monotonic() - t0
            time.sleep(settle)  # let the MonBus path drain into the bins

            # Freeze for a coherent snapshot, read, then clear for the next run
            # (tally_clear is RMW: the freeze level survives the clear).
            driver.tally_freeze(True)
            bins, unc = _read_bins(driver)
            delta = bins
            unc_ = unc

            st0 = driver.ci_status("ci0")
            st1 = driver.ci_status("ci1")
            crc0 = driver.ci_crcs("ci0")
            crc1 = driver.ci_crcs("ci1")
            lat0 = driver.ci_latency("ci0")
            lat1 = driver.ci_latency("ci1")

            if do_latch:
                latch = _latch_capture(driver)

            driver.tally_clear()
            driver.tally_freeze(False)

            rec = {
                "config": name, "count": count, "mask": f"0x{mask:06x}",
                "base0": f"0x{base0:05x}", "base1": f"0x{base1:05x}",
                "we_mix": we_mix, "outstanding": depth, "ci1_idle": ci1_idle, "done": ok,
                "wall_s": round(wall, 3),
                "bins": bins, "unexpected": unc_,
                "ci0": {**st0, **crc0, **lat0}, "ci1": {**st1, **crc1, **lat1},
            }
            if do_latch:
                rec["latch"] = latch
            results.append(rec)

            hits, misses, snoops, evicts, drops = delta[0], delta[1], delta[2], \
                delta[3], delta[4]
            fill_end, drain_end = delta[7], delta[9]
            # Hit events fire once per SERVED access (post-miss replays re-hit),
            # so bin0 = total accesses; true miss rate = miss/accesses.
            lat_mean0 = lat0["lat_sum"] / count if count else 0
            lat_mean1 = lat1["lat_sum"] / count if count else 0
            cyc0, cyc1 = lat0["run_cycles"], lat1["run_cycles"]
            mlp0 = lat0["outst_sum"] / cyc0 if cyc0 else 0
            mlp1 = lat1["outst_sum"] / cyc1 if cyc1 else 0
            say(f"  acc={hits} miss={misses} snoop={snoops} evict={evicts} "
                f"drop={drops} fill_end={fill_end} drain_end={drain_end} "
                f"unc={unc_} "
                f"miss%={100.0 * misses / hits if hits else 0:.1f} "
                f"lat0={lat0['lat_min']}/{lat_mean0:.1f}/{lat0['lat_max']} "
                f"lat1={lat1['lat_min']}/{lat_mean1:.1f}/{lat1['lat_max']} "
                f"cyc0={cyc0} cyc1={cyc1} "
                f"cpt0={cyc0 / count if count else 0:.2f} "
                f"mlp0={mlp0:.2f}/{lat0['outst_max']} "
                f"mlp1={mlp1:.2f}/{lat1['outst_max']} "
                f"stall0={lat0['stall_cycles']} cstall0={lat0['credit_stall']} "
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
    ap.add_argument("--outstanding", nargs="+", type=int, default=[1],
                    help="injector depths to sweep (1..16); default 1")
    ap.add_argument("--ci1-idle", action="store_true",
                    help="run injector 1 with zero transactions: single-core numbers "
                         "for the reference comparison (TASK-003)")
    ap.add_argument("--out", default=None,
                    help="JSON results path (default: results/perf_sweep_*.json")
    args = ap.parse_args(argv)

    link = open_amber_link(args.port, board_name=args.board,
                           baudrate=args.baud)
    bridge = build_amber_bridge(link)
    driver = AmberDriver(bridge)
    try:
        results = run_sweep(driver, count=args.count,
                            configs=args.configs,
                            outstanding=tuple(args.outstanding),
                            ci1_idle=args.ci1_idle)
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
        json.dump({"count": args.count, "outstanding": args.outstanding,
                   "results": results}, fh, indent=2)
    print(f"[sweep] results written to {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
