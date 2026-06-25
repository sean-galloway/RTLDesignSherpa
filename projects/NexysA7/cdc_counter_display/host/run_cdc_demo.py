#!/usr/bin/env python3
"""
run_cdc_demo.py — Host runner for the cdc_demo_top FPGA bitstream.

Subcommands:
  smoke       Verify the link works: read BUILD_ID, exercise SCRATCH,
              dump all four counters' defaults.
  monitor     Real-time view of all four counters' VALUE / PRESS_COUNT
              (updates every 200 ms — Ctrl-C to stop).
  press       Inject N host-press events to a counter and verify the
              expected VALUE = INIT + N * INCREMENT (mod 256).
  watch-fail  THE headline demo: put a chosen counter in NO-CDC mode
              with AUTO_INC=1, then sweep its PICKOFF from slow to
              fast. Reads VALUE before/after each step; computes
              variance to surface "garbage" reads at high speeds.
  reset       Soft reset everything via CTRL[0].
  set         Generic register write (debug).
  get         Generic register read (debug).

Bitstream: cdc_demo_top.  Default UART port: /dev/ttyUSB1.
Documentation: ../docs/HARNESS.md
"""

import argparse
import sys
import time
from pathlib import Path

# Reuse the existing UART AXI bridge from the converters project
HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent.parent.parent
sys.path.insert(0, str(REPO / "projects/components/converters/bin"))
try:
    from uart_axi_bridge import UARTAxiBridge
except ImportError:
    print("ERROR: cannot import uart_axi_bridge. Run from a checked-out repo.")
    sys.exit(2)


# -----------------------------------------------------------------------------
# CSR map — keep this aligned with ../docs/HARNESS.md and cdc_demo_harness.sv
# -----------------------------------------------------------------------------

OFF_BUILD_ID    = 0x000
OFF_STATUS      = 0x004
OFF_CTRL        = 0x008
OFF_DISP_SELECT = 0x00C
OFF_SCRATCH     = 0x010

NUM_COUNTERS    = 4

def ctr_base(i: int) -> int:
    if not 0 <= i < NUM_COUNTERS:
        raise ValueError(f"counter index out of range: {i}")
    return 0x40 + i * 0x40

OFF_DIVISOR    = 0x00
OFF_INIT       = 0x04
OFF_INCREMENT  = 0x08
OFF_CFG_LOAD   = 0x0C
OFF_HOST_PRESS = 0x10
OFF_VALUE      = 0x14
OFF_PRESS_CNT  = 0x18
OFF_CLK_TICKS  = 0x1C
OFF_CDC_MODE   = 0x20
OFF_AUTO_INC   = 0x24

EXPECTED_BUILD_ID = 0x4344_4331   # "CDC1"

CLK_HZ = 100_000_000  # sys_clk

CDC_MODE_NAMES = {0: "NO-CDC",
                  1: "STRETCH (cdc_open_loop, ~20 MHz cliff)",
                  2: "SYNC-FIFO (fifo_async)",
                  3: "TWO-PHASE (cdc_2_phase_handshake)",
                  4: "FOUR-PHASE (cdc_4_phase_handshake)"}


# -----------------------------------------------------------------------------
# Per-counter helpers
# -----------------------------------------------------------------------------

class Counter:
    def __init__(self, bridge, idx):
        self.b   = bridge
        self.i   = idx
        self.base = ctr_base(idx)

    def w(self, off, val): self.b.write(self.base + off, val & 0xFFFF_FFFF)
    def r(self, off):       return self.b.read (self.base + off)

    # Convenience accessors
    def set_pickoff(self, pickoff):  self.w(OFF_DIVISOR,   pickoff & 0xFF)
    def set_init(self, init):        self.w(OFF_INIT,      init    & 0xFF)
    def set_increment(self, inc):    self.w(OFF_INCREMENT, inc     & 0xFF)
    def load(self):                  self.w(OFF_CFG_LOAD,  1)
    def press(self):                 self.w(OFF_HOST_PRESS, 1)
    def set_cdc_mode(self, mode):    self.w(OFF_CDC_MODE,  mode & 0x7)
    def set_auto_inc(self, en):      self.w(OFF_AUTO_INC,  en   & 1)

    def value(self):       return self.r(OFF_VALUE)      & 0xFFFF
    def press_count(self): return self.r(OFF_PRESS_CNT)  & 0xFFFF
    def clk_ticks(self):   return self.r(OFF_CLK_TICKS)  & 0xFFFFFFFF
    def cdc_mode(self):    return self.r(OFF_CDC_MODE)   & 0x7
    def auto_inc(self):    return self.r(OFF_AUTO_INC)   & 1


# -----------------------------------------------------------------------------
# Subcommands
# -----------------------------------------------------------------------------

def cmd_smoke(args, bridge):
    print("\n== SMOKE TEST ==")
    bid = bridge.read(OFF_BUILD_ID)
    print(f"  BUILD_ID = 0x{bid:08X}", end="")
    if bid != EXPECTED_BUILD_ID:
        print(f"  FAIL (expected 0x{EXPECTED_BUILD_ID:08X})")
        return 1
    print("  OK")

    for v in (0xDEAD_BEEF, 0x1234_5678, 0xA5A5_5A5A):
        bridge.write(OFF_SCRATCH, v)
        rb = bridge.read(OFF_SCRATCH)
        ok = "OK" if rb == v else f"FAIL (got 0x{rb:08X})"
        print(f"  SCRATCH 0x{v:08X} -> 0x{rb:08X}  {ok}")
        if rb != v: return 1

    print("\n  Per-counter defaults:")
    print(f"  {'idx':>3}  {'pickoff':>8}  {'init':>6}  {'inc':>5}  {'value':>6}  "
          f"{'presses':>7}  {'mode':<18}  {'auto':>4}")
    for i in range(NUM_COUNTERS):
        c = Counter(bridge, i)
        mode = c.cdc_mode()
        print(f"  {i:>3}  {c.r(OFF_DIVISOR):>8}  0x{c.r(OFF_INIT):>04X}  "
              f"{c.r(OFF_INCREMENT):>5}  0x{c.value():>04X}  "
              f"{c.press_count():>7}  {mode}={CDC_MODE_NAMES.get(mode,'?'):<14}  "
              f"{c.auto_inc():>4}")
    return 0


def cmd_monitor(args, bridge):
    print("\n== MONITOR (Ctrl-C to stop) ==")
    print(f"  {'time':>6}  "
          + "  ".join(f"ctr{i}.val ctr{i}.cnt" for i in range(NUM_COUNTERS)))
    t0 = time.time()
    try:
        while True:
            cs = [Counter(bridge, i) for i in range(NUM_COUNTERS)]
            row = f"{time.time()-t0:6.1f}  "
            for c in cs:
                row += f"   0x{c.value():02X}    {c.press_count():>5}   "
            print(row)
            time.sleep(args.interval)
    except KeyboardInterrupt:
        print("\nstopped")
    return 0


def cmd_press(args, bridge):
    c = Counter(bridge, args.counter)
    init = c.r(OFF_INIT) & 0xFF
    inc  = c.r(OFF_INCREMENT) & 0xFF
    pc_before  = c.press_count()
    val_before = c.value()

    print(f"\n== PRESS counter {args.counter}: {args.count} injections "
          f"(INIT=0x{init:02X} INC={inc}) ==")
    print(f"  Before: VALUE=0x{val_before:02X}  PRESS_COUNT={pc_before}")
    t0 = time.time()
    for _ in range(args.count):
        c.press()
    elapsed = time.time() - t0

    # Give the CDC a moment to settle
    time.sleep(0.1)

    pc_after  = c.press_count()
    val_after = c.value()
    expected_val = (val_before + args.count * inc) & 0xFF

    print(f"  After:  VALUE=0x{val_after:02X}  PRESS_COUNT={pc_after}  "
          f"(elapsed {elapsed:.2f} s)")
    print(f"  Expected VALUE = (0x{val_before:02X} + {args.count} * {inc}) "
          f"& 0xFF = 0x{expected_val:02X}")
    print(f"  PRESS_COUNT delta = {pc_after - pc_before}")
    rv = 0
    if val_after != expected_val:
        print("  VALUE MISMATCH (CDC error?)")
        rv = 1
    if pc_after - pc_before != args.count:
        print("  PRESS_COUNT delta MISMATCH (lost host_press events?)")
        rv = 1
    if rv == 0:
        print("  OK")
    return rv


def cmd_watch_fail(args, bridge):
    """
    THE headline demo. Put one counter in NO-CDC + AUTO_INC, then sweep
    its PICKOFF from slow → fast. At each step, sample VALUE several
    times and compute the spread — proper CDC shows monotonic progress
    (or matches the auto-inc rate), broken CDC at fast clock shows wide
    variance and impossible jumps.

    Output is a table the user can correlate with the 7-seg flicker.
    """
    c = Counter(bridge, args.counter)

    print(f"\n== WATCH-FAIL demo on counter {args.counter} ==")
    print(f"  Setting CDC_MODE = 1 (NO CDC, raw cross), AUTO_INC = 1")
    print(f"  Display: set DISP_SELECT to {args.counter} via:")
    print(f"           python3 {sys.argv[0]} --port {args.port} set "
          f"0x{OFF_DISP_SELECT:03X} {args.counter}")

    bridge.write(OFF_DISP_SELECT, args.counter)
    c.set_cdc_mode(1)
    c.set_auto_inc(1)
    c.set_init(0)
    c.set_increment(1)
    c.load()
    time.sleep(0.2)

    # The sweep: pickoff in decreasing order = increasing clock freq.
    # f_ctr = 100 MHz / 2^(pickoff+1)
    sweep = args.pickoffs or [23, 19, 15, 13, 11, 9, 7, 5, 3, 1, 0]

    print()
    print(f"  {'pickoff':>7}  {'ctr_clk':>12}  "
          f"{'samples (VALUE @ ~50 ms intervals)':<60}  variance")
    print("  " + "-" * 100)
    for po in sweep:
        c.set_pickoff(po)
        time.sleep(0.1)  # let the new pickoff settle through the bin2gray sync

        # 10 samples spread over ~500 ms
        samples = []
        for _ in range(10):
            samples.append(c.value())
            time.sleep(0.05)

        # Compute spread (min/max/range) and the unique values seen
        lo, hi = min(samples), max(samples)
        spread = (hi - lo) & 0xFF
        unique = len(set(samples))

        # ctr_clk frequency at this pickoff:  f = 100 MHz / 2^(pickoff+1)
        f_ctr = CLK_HZ / (1 << (po + 1))
        f_str = (f"{f_ctr/1e6:.3f} MHz" if f_ctr >= 1e6 else
                 f"{f_ctr/1e3:.2f} kHz" if f_ctr >= 1e3 else
                 f"{f_ctr:.2f} Hz")
        samples_str = " ".join(f"{v:02X}" for v in samples)
        print(f"  {po:>7}  {f_str:>12}  {samples_str:<60}  "
              f"min=0x{lo:02X} max=0x{hi:02X} range=0x{spread:02X} unique={unique}")

    # Reset counter back to proper / off so the demo doesn't leave a flickering
    # display behind.
    c.set_cdc_mode(0)
    c.set_auto_inc(0)
    c.set_pickoff(23)

    print()
    print("  Slow rows should show 1–3 unique values (clean count progress).")
    print("  Fast rows should show 8+ unique values across the full 0x00–0xFF")
    print("  range (mid-transition garbage). The 7-seg flicker tracks this.")
    return 0


def cmd_reset(args, bridge):
    print("Soft reset via CTRL[0]...")
    bridge.write(OFF_CTRL, 1)
    time.sleep(0.05)
    bid = bridge.read(OFF_BUILD_ID)
    print(f"  Post-reset BUILD_ID = 0x{bid:08X}", end="")
    print("  OK" if bid == EXPECTED_BUILD_ID else "  FAIL")
    return 0 if bid == EXPECTED_BUILD_ID else 1


def cmd_set(args, bridge):
    addr = int(args.addr, 0)
    val  = int(args.val,  0)
    bridge.write(addr, val)
    print(f"  WRITE 0x{addr:08X} <= 0x{val:08X}")
    return 0


def cmd_get(args, bridge):
    addr = int(args.addr, 0)
    val  = bridge.read(addr)
    print(f"  READ  0x{addr:08X} => 0x{val:08X}")
    return 0


# -----------------------------------------------------------------------------
# CLI
# -----------------------------------------------------------------------------

def main():
    p = argparse.ArgumentParser(
        description="Host runner for cdc_demo_top bitstream.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__)
    p.add_argument("--port", default="/dev/ttyUSB1",
                   help="Serial device (default /dev/ttyUSB1)")
    p.add_argument("--baud", type=int, default=115200)
    sub = p.add_subparsers(dest="cmd", required=True)

    sub.add_parser("smoke")

    pm = sub.add_parser("monitor")
    pm.add_argument("--interval", type=float, default=0.2)

    pp = sub.add_parser("press")
    pp.add_argument("--counter", type=int, default=0)
    pp.add_argument("--count",   type=int, default=100)

    pw = sub.add_parser("watch-fail")
    pw.add_argument("--counter",  type=int, default=2,
                    help="Which counter to corrupt (default 2)")
    pw.add_argument("--pickoffs", type=lambda s: [int(x) for x in s.split(",")],
                    default=None,
                    help="Comma list of pickoff values to sweep "
                         "(default: 23,19,15,13,11,9,7,5,3,1,0)")

    sub.add_parser("reset")

    ps = sub.add_parser("set")
    ps.add_argument("addr")
    ps.add_argument("val")

    pg = sub.add_parser("get")
    pg.add_argument("addr")

    args = p.parse_args()

    bridge = UARTAxiBridge(port=args.port, baudrate=args.baud)
    try:
        cmds = {
            "smoke": cmd_smoke, "monitor": cmd_monitor, "press": cmd_press,
            "watch-fail": cmd_watch_fail, "reset": cmd_reset,
            "set": cmd_set, "get": cmd_get,
        }
        return cmds[args.cmd](args, bridge)
    finally:
        if hasattr(bridge, "ser"):
            bridge.ser.close()


if __name__ == "__main__":
    sys.exit(main())
