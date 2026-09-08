#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
"""run_cdc_demo.py — Host CLI for the cdc_demo_top FPGA bitstream.

Thin front-end: builds a `CdcDemoDriver` (by-name registers over the UART/AXIL
bridge) and dispatches to the authored-once programs in `cdc_programs.py` — the
SAME programs the cocotb sim runs (dv/tests/test_cdc_demo_uart.py). No hardcoded
offsets live here; the register layout comes from the PeakRDL regmap.

Subcommands:
  smoke       BUILD_ID + SCRATCH round-trip + per-counter defaults.
  monitor     Real-time VALUE / PRESS_COUNT for all four counters.
  press       Inject N HOST_PRESS events and verify VALUE = INIT + N*INC.
  cfg-load    CFG_LOAD reloads VALUE to INIT, leaving PRESS_COUNT intact.
  cdc-mode    Round-trip every CDC_MODE code through the CSR.
  watch-fail  Headline demo: NO-CDC + AUTO_INC, sweep pickoff slow→fast.
  reset       Soft reset via CTRL.soft_reset.
  set / get   Raw register poke/peek (absolute bus address) for debug.

Bitstream: cdc_demo_top.  Default UART port: /dev/ttyUSB1.
Docs: ../docs/HARNESS.md
"""

import argparse
import sys
import time
from pathlib import Path

# host/ on sys.path so cdc_demo / cdc_programs import cleanly when run directly.
sys.path.insert(0, str(Path(__file__).resolve().parent))
import cdc_demo as cd            # noqa: E402
import cdc_programs as progs     # noqa: E402


def cmd_smoke(args, drv):
    print("\n== SMOKE TEST ==")
    r = progs.smoke(drv)
    print(f"  BUILD_ID = 0x{r.build_id:08X}  "
          f"{'OK' if r.build_id_ok else f'FAIL (expected 0x{cd.EXPECTED_BUILD_ID:08X})'}")
    for wrote, read, ok in r.scratch:
        print(f"  SCRATCH 0x{wrote:08X} -> 0x{read:08X}  {'OK' if ok else 'FAIL'}")
    print("\n  Per-counter defaults:")
    print(f"  {'idx':>3}  {'divisor':>9}  {'init':>6}  {'inc':>5}  {'value':>6}  "
          f"{'presses':>7}  {'mode':<20}  {'auto':>4}")
    for c in r.counters:
        print(f"  {c.idx:>3}  0x{c.divisor:>07X}  0x{c.init:>04X}  {c.increment:>5}  "
              f"0x{c.value:>04X}  {c.press_count:>7}  "
              f"{c.cdc_mode}={cd.CDC_MODE_NAMES.get(c.cdc_mode,'?'):<16}  {c.auto_inc:>4}")
    return 0 if r.ok else 1


def cmd_monitor(args, drv):
    print("\n== MONITOR (Ctrl-C to stop) ==")
    print(f"  {'time':>6}  " + "  ".join(f"ctr{i}.val ctr{i}.cnt"
                                         for i in range(cd.NUM_COUNTERS)))
    t0 = time.time()
    try:
        while True:
            row = f"{time.time()-t0:6.1f}  "
            for i in range(cd.NUM_COUNTERS):
                c = drv.counter(i)
                row += f"   0x{c.value():04X}  {c.press_count():>5}   "
            print(row)
            time.sleep(args.interval)
    except KeyboardInterrupt:
        print("\nstopped")
    return 0


def cmd_press(args, drv):
    r = progs.press(drv, args.counter, args.count)
    print(f"\n== PRESS counter {args.counter}: {args.count} injections "
          f"(INIT=0x{r.init:02X} INC={r.increment}) ==")
    print(f"  VALUE 0x{r.value_before:04X} -> 0x{r.value_after:04X}  "
          f"(expected 0x{r.value_expected:04X})")
    print(f"  PRESS_COUNT delta = {r.press_delta}")
    print("  OK" if r.ok else "  FAIL")
    return 0 if r.ok else 1


def cmd_cfg_load(args, drv):
    r = progs.cfg_load(drv, args.counter)
    print(f"\n== CFG-LOAD counter {args.counter} ==")
    print(f"  after 5 presses: VALUE=0x{r.value_mid:04X} PRESS_COUNT={r.press_mid}")
    print(f"  after reload:    VALUE=0x{r.value_reload:04X} "
          f"(target 0x{r.reload_target:04X}) PRESS_COUNT={r.press_reload}")
    print("  OK" if r.ok else "  FAIL")
    return 0 if r.ok else 1


def cmd_cdc_mode(args, drv):
    r = progs.cdc_mode_check(drv, args.counter)
    print(f"\n== CDC-MODE round-trip counter {args.counter} ==")
    for wrote, read in r.checks:
        print(f"  mode {wrote} -> {read}  {'OK' if wrote == read else 'FAIL'}")
    print("  OK" if r.ok else "  FAIL")
    return 0 if r.ok else 1


def cmd_watch_fail(args, drv):
    print(f"\n== WATCH-FAIL demo on counter {args.counter} "
          f"(NO-CDC + AUTO_INC, sweep pickoff) ==")
    sweep = args.pickoffs or [23, 19, 15, 13, 11, 9, 7, 5, 3, 1, 0]
    rows = progs.watch_fail(drv, args.counter, sweep)
    print(f"  {'pickoff':>7}  {'ctr_clk':>12}  {'samples':<40}  spread/unique")
    print("  " + "-" * 80)
    for row in rows:
        f = row.f_ctr_hz
        fs = (f"{f/1e6:.3f} MHz" if f >= 1e6 else
              f"{f/1e3:.2f} kHz" if f >= 1e3 else f"{f:.2f} Hz")
        samples = " ".join(f"{v:02X}" for v in row.samples)
        print(f"  {row.pickoff:>7}  {fs:>12}  {samples:<40}  "
              f"range=0x{row.spread:02X} unique={row.unique}")
    print("\n  Slow rows: 1-3 unique values (clean). Fast rows: many unique "
          "values across 0x00-0xFF (multi-bit skew). 7-seg flicker tracks this.")
    return 0


def cmd_reset(args, drv):
    print("Soft reset via CTRL.soft_reset...")
    drv.soft_reset()
    time.sleep(0.05)
    bid = drv.build_id()
    ok = bid == cd.EXPECTED_BUILD_ID
    print(f"  Post-reset BUILD_ID = 0x{bid:08X}  {'OK' if ok else 'FAIL'}")
    return 0 if ok else 1


def cmd_set(args, drv):
    addr, val = int(args.addr, 0), int(args.val, 0)
    drv.bridge.write(addr, val)
    print(f"  WRITE 0x{addr:08X} <= 0x{val:08X}")
    return 0


def cmd_get(args, drv):
    addr = int(args.addr, 0)
    val = drv.bridge.read(addr)
    print(f"  READ  0x{addr:08X} => 0x{val:08X}")
    return 0


def main():
    p = argparse.ArgumentParser(
        description="Host CLI for cdc_demo_top bitstream.",
        formatter_class=argparse.RawDescriptionHelpFormatter, epilog=__doc__)
    p.add_argument("--port", default="auto",
                   help="Serial device. Default 'auto' probes every /dev/ttyUSB* "
                        "for the harness (BUILD_ID round-trip); pass an explicit "
                        "path to force it.")
    p.add_argument("--baud", type=int, default=115200)
    sub = p.add_subparsers(dest="cmd", required=True)

    sub.add_parser("smoke")

    pm = sub.add_parser("monitor")
    pm.add_argument("--interval", type=float, default=0.2)

    pp = sub.add_parser("press")
    pp.add_argument("--counter", type=int, default=0)
    pp.add_argument("--count", type=int, default=100)

    pc = sub.add_parser("cfg-load")
    pc.add_argument("--counter", type=int, default=0)

    pcd = sub.add_parser("cdc-mode")
    pcd.add_argument("--counter", type=int, default=0)

    pw = sub.add_parser("watch-fail")
    pw.add_argument("--counter", type=int, default=2)
    pw.add_argument("--pickoffs", type=lambda s: [int(x) for x in s.split(",")],
                    default=None,
                    help="Comma list of pickoffs (default 23,19,15,13,11,9,7,5,3,1,0)")

    sub.add_parser("reset")

    ps = sub.add_parser("set")
    ps.add_argument("addr")
    ps.add_argument("val")

    pg = sub.add_parser("get")
    pg.add_argument("addr")

    args = p.parse_args()
    # 'set'/'get' are raw-poke debug commands the user aims at a known device; the
    # rest resolve the port by probing for the harness (BUILD_ID) since ttyUSB
    # numbering drifts.
    port = cd.autodetect_port(args.baud, want=args.port)
    drv = cd.CdcDemoDriver(port=port, baud=args.baud)
    try:
        cmds = {
            "smoke": cmd_smoke, "monitor": cmd_monitor, "press": cmd_press,
            "cfg-load": cmd_cfg_load, "cdc-mode": cmd_cdc_mode,
            "watch-fail": cmd_watch_fail, "reset": cmd_reset,
            "set": cmd_set, "get": cmd_get,
        }
        return cmds[args.cmd](args, drv)
    finally:
        drv.close()


if __name__ == "__main__":
    sys.exit(main())
