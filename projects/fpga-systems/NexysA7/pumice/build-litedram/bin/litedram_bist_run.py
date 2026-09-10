#!/usr/bin/env python3
"""LiteDRAM hardware-BIST bandwidth on the Nexys A7, for the pumice A/B.

NOTE ON WHAT THIS MEASURES: this is LiteDRAM's OWN BIST generator/checker
driving its OWN user port. It is NOT the pumice harness's AXI pattern
generators, so it is a reference point, not a like-for-like A/B. The
like-for-like number needs LiteDRAM dropped into the pumice harness
(build-litedram/, litedram_char_harness) so both controllers see identical
traffic and identical measurement.
"""
import sys, time
from litex import RemoteClient

SYS_CLK = 75e6
LEN = 16 * 1024 * 1024          # bytes per run
BASE = 0

def run(w, kind, bl, random):
    pre = f"sdram_{kind}_"
    r = w.regs
    getattr(r, pre + "reset").write(1)
    getattr(r, pre + "reset").write(0)
    getattr(r, pre + "base").write(BASE)
    getattr(r, pre + "end").write(BASE + LEN)
    getattr(r, pre + "length").write(bl)
    getattr(r, pre + "random").write(1 if random else 0)
    getattr(r, pre + "start").write(1)
    getattr(r, pre + "start").write(0)
    t0 = time.time()
    while getattr(r, pre + "done").read() == 0:
        if time.time() - t0 > 60:
            return None, None, None
        time.sleep(0.01)
    ticks = getattr(r, pre + "ticks").read()
    errs = getattr(r, pre + "errors").read() if kind == "checker" else 0
    mbps = (LEN / (ticks / SYS_CLK)) / 1e6 if ticks else 0.0
    return mbps, ticks, errs


def main():
    w = RemoteClient(csr_csv="/tmp/claude-1000/-mnt-data-github-RTLDesignSherpa/764caa7b-7b70-493f-a8f1-cf2931a9b6e8/scratchpad/litex_bist/csr.csv")
    w.open()
    print(f"{'dir':<6} {'bl':>4} {'rnd':>4} {'MB/s':>9} {'MiB/s':>9} {'ticks':>10} {'errors':>7}")
    print("-" * 56)
    rows = []
    for bl in (8, 16, 32):
        for random in (False, True):
            wr, wt, _ = run(w, "generator", bl, random)
            rd, rt, re = run(w, "checker", bl, random)
            if wr is None or rd is None:
                print(f"{'--':<6} {bl:>4} {int(random):>4}   TIMEOUT")
                continue
            print(f"{'write':<6} {bl:>4} {int(random):>4} {wr:>9.1f} {wr/1.048576:>9.1f} {wt:>10} {'-':>7}")
            print(f"{'read':<6} {bl:>4} {int(random):>4} {rd:>9.1f} {rd/1.048576:>9.1f} {rt:>10} {re:>7}")
            rows.append((bl, random, wr, rd, re))
    w.close()
    with open(sys.argv[1] if len(sys.argv) > 1 else "/dev/null", "w") as fh:
        fh.write("bl,random,write_MBps,read_MBps,read_errors\n")
        for bl, rnd, wr, rd, re in rows:
            fh.write(f"{bl},{int(rnd)},{wr:.1f},{rd:.1f},{re}\n")


if __name__ == "__main__":
    main()
