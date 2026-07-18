#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""End-to-end DDR2 characterization smoke test.

Programs a simple linear WR + RD workload, kicks both engines, waits for
completion, and reports CRC / cycles / perf. Intended as the first thing
you run after flashing a fresh bitstream.

Usage:
    python3 run_smoke.py --port /dev/ttyUSB1 [--txn 1024] [--blen 8]

Expected pass condition:
    * BUILD_ID matches
    * both engines report done within the timeout
    * CRC_ACTUAL == CRC_EXPECTED and BEATS_MISMATCHED == 0
    * TIMER.pass is asserted
"""

from __future__ import annotations

import argparse
import sys

from ddr2_char import (
    DDR2CharDriver,
    autodetect_port,
    MEMTYPE_DDR2,
    ID_MODE_FIXED,
    AXI_SIZE_8,
    AXI_BURST_INCR,
    HIST_BUS_RD,
    HIST_BUS_WR,
    HIST_METRIC_0,
    HIST_METRIC_1,
)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.strip().splitlines()[0])
    ap.add_argument("--port",       default="auto")
    ap.add_argument("--baud",       type=int, default=115200)
    ap.add_argument("--base-addr",  type=lambda s: int(s, 0), default=0x0)
    ap.add_argument("--txn",        type=int, default=1024,
                    help="Number of bursts per engine")
    ap.add_argument("--blen",       type=int, default=8,
                    help="Beats per burst (AXI4 burst length)")
    ap.add_argument("--seed",       type=lambda s: int(s, 0), default=0xDEADBEEF)
    ap.add_argument("--timeout",    type=float, default=30.0)
    ap.add_argument("--phy-wrlat",  type=int, default=4)
    ap.add_argument("--phy-rdlat",  type=int, default=6)
    args = ap.parse_args()

    args.port = autodetect_port(args.baud, want=args.port)
    d = DDR2CharDriver(port=args.port, baudrate=args.baud)

    # 1. Identity ping. Bad BUILD_ID = wrong bitstream or dead UART.
    bid = d.build_id()
    if bid != d.BUILD_ID_MAGIC:
        print(f"FAIL: BUILD_ID=0x{bid:08X} (expected 0x{d.BUILD_ID_MAGIC:08X})",
              file=sys.stderr)
        return 2
    print(f"identity ok: BUILD_ID=0x{bid:08X}")

    # 2. Wait for controller init before touching cfg. If init_fail
    #    latched, the whole run is a bust.
    s = d.status()
    if not s.init_done:
        print(f"FAIL: controller init did not complete (init_done=0 "
              f"init_fail={s.init_fail})", file=sys.stderr)
        return 2
    print(f"init ok: init_done=1 init_fail={s.init_fail}")

    # 3. Runtime controller cfg. Values below are placeholders -- the real
    #    numbers come from the JEDEC datasheet for MT47H64M16HR-25E once
    #    a7ddrphy is wired up and calibration completes.
    d.set_controller_cfg(
        memtype     = MEMTYPE_DDR2,
        t_phy_wrlat = args.phy_wrlat,
        t_rddata_en = args.phy_rdlat,
        rd_in_order = False,
    )
    d.set_controller_cap(cap_lookahead_max=4, cap_synth_mask=0xF)

    # 4. Program both engines with a matching workload.
    #    - Linear stride: each burst covers blen*8 bytes (64b data bus).
    #    - Same LFSR seed on WR and RD so the RD engine's CRC accumulator
    #      knows what pattern to expect.
    stride = args.blen * 8   # bytes per burst

    engine_cfg = dict(
        start_addr = args.base_addr,
        burst_len  = args.blen,
        txn_count  = args.txn,
        stride_0   = stride,
        gap        = 0,
        axi_id     = 0,
        id_mode    = ID_MODE_FIXED,
        axi_size   = AXI_SIZE_8,
        axi_burst  = AXI_BURST_INCR,
        data_mode  = False,           # LFSR mode
        lfsr_seed  = args.seed,
    )
    d.program_wr_engine(**engine_cfg)
    d.program_rd_engine(**engine_cfg)
    print(f"engines programmed: txn={args.txn} blen={args.blen} "
          f"stride=0x{stride:X} seed=0x{args.seed:08X}")

    # 5. Clear stats + kick.
    d.clear_stats()
    d.timer_clear()
    d.freeze_trace(False)   # make sure perf isn't frozen

    d.start_both()
    print("kicked both engines")

    # 6. Wait for both engines done. Errors bubble up as exceptions.
    try:
        s = d.wait_done(timeout_s=args.timeout)
    except (TimeoutError, RuntimeError) as e:
        print(f"FAIL: {e}", file=sys.stderr)
        # Dump what state we can before we die.
        s = d.status()
        print(f"  status={s}", file=sys.stderr)
        return 3

    # 7. CRC check.
    exp, act, match, valid = d.crc()
    beats_mism = d.beats_mismatched()
    if not (match and valid) or beats_mism != 0:
        print(f"FAIL: data mismatch: exp=0x{exp:08X} act=0x{act:08X} "
              f"match={match} valid={valid} beats_mism={beats_mism}",
              file=sys.stderr)
        return 4
    print(f"CRC ok: exp=act=0x{exp:08X} beats_mism=0")

    # 8. Timer + perf.
    tm = d.timer()
    m  = d.perf_meters()

    beats_total = args.txn * args.blen
    print(f"cycles: total={tm.cycles} "
          f"WR window={tm.w_last - tm.w_first} "
          f"RD window={tm.r_last - tm.r_first}")
    print(f"WR meter: util={m['wr'].utilisation():.1%} "
          f"(prod={m['wr'].prod} bp={m['wr'].bp} "
          f"starv={m['wr'].starv} idle={m['wr'].idle})")
    print(f"RD meter: util={m['rd'].utilisation():.1%} "
          f"(prod={m['rd'].prod} bp={m['rd'].bp} "
          f"starv={m['rd'].starv} idle={m['rd'].idle})")

    # 9. Quick histogram peek: which bin holds the mode for AR->firstR
    #    and AW->B? (Just informational; a real characterization sweep
    #    would dump all 16 bins and CSV them.)
    for label, bus, metric in (("AR->firstR", HIST_BUS_RD, HIST_METRIC_0),
                               ("AR->RLAST",  HIST_BUS_RD, HIST_METRIC_1),
                               ("AW->B",      HIST_BUS_WR, HIST_METRIC_0)):
        counts, total = d.perf_hist_dump(bus, metric)
        if total:
            mode_bin = max(range(16), key=lambda b: counts[b])
            print(f"{label:12s}: total={total} mode=bin{mode_bin} "
                  f"[{1 << mode_bin}..{1 << (mode_bin + 1)}) cyc "
                  f"({counts[mode_bin]}/{total} = "
                  f"{counts[mode_bin] / total:.1%})")

    print(f"SMOKE PASS: cycles={tm.cycles} beats={beats_total} "
          f"pass={tm.passed}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
