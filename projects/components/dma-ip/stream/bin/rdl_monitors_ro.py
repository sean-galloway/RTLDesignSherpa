#!/usr/bin/env python3
"""
rdl_monitors_ro.py - make the STREAM monitor registers read-only.

For a monitors-off STREAM build (USE_AXI_MONITORS=0) the monitor config/status
registers are dead -- they drive disabled logic -- yet they still cost area in
the PeakRDL register block + cmd/rsp adapter (write storage, write decode, and a
read-mux entry each). This script rewrites the monitor registers' software
access from `sw = rw` to `sw = r`, which:

  * removes the write storage flop and write-decode logic (the field collapses
    to a constant at its reset value -> a read-as-zero "hole"),
  * KEEPS the address map byte-identical (the register still lives at its
    address; the host just reads 0 and writes are ignored),
  * KEEPS the generated hwif_out.<field> wire (now a constant), so the RTL that
    consumes it still elaborates unchanged.

It does NOT touch the core datapath/config registers (global ctrl, scheduler,
descriptor engine, channel enable/reset/state, AXI xfer config). Monitor
registers are matched by name prefix.

Usage:
  rdl_monitors_ro.py IN.rdl -o OUT.rdl          # transform only
  rdl_monitors_ro.py IN.rdl -o OUT.rdl --regen DIR   # + run peakrdl_generate.py

Default IN is rtl/macro/stream_regs.rdl relative to the stream component.
"""
import argparse
import os
import re
import subprocess
import sys

# Register-name prefixes considered "monitor" (dead when USE_AXI_MONITORS=0).
MON_PREFIXES = ("MON_", "DAXMON_", "RDMON_", "WRMON_", "PERF_")

# Matches a register-block closing line:  "} NAME @ 0x180;"  or  "} NAME[8] @ 0x150 += 0x4;"
REG_CLOSE = re.compile(r"^\s*\}\s*([A-Za-z_]\w*)(?:\[\d+\])?\s*@")
SW_RW = re.compile(r"(\bsw\s*=\s*)(rw|w)(\s*;)")


def is_monitor(name: str) -> bool:
    return any(name.startswith(p) for p in MON_PREFIXES)


def _find_peakrdl_generate(start: str):
    """Locate bin/peakrdl_generate.py via REPO_ROOT or by walking up."""
    cand = os.environ.get("REPO_ROOT")
    if cand:
        p = os.path.join(cand, "bin", "peakrdl_generate.py")
        if os.path.isfile(p):
            return p
    d = start
    while d != os.path.dirname(d):
        p = os.path.join(d, "bin", "peakrdl_generate.py")
        if os.path.isfile(p):
            return p
        d = os.path.dirname(d)
    return None


def transform(text: str):
    """Return (new_text, converted_register_names)."""
    out = []
    block = []          # lines buffered since the last register close
    converted = []
    for line in text.splitlines(keepends=True):
        block.append(line)
        m = REG_CLOSE.match(line)
        if m:
            name = m.group(1)
            if is_monitor(name):
                # Demote sw=rw / sw=w -> sw=r within this register's block.
                new_block, n = [], 0
                for bl in block:
                    bl2 = SW_RW.sub(r"\1r\3", bl)
                    n += (bl2 != bl)
                    new_block.append(bl2)
                if n:
                    converted.append((name, n))
                out.extend(new_block)
            else:
                out.extend(block)
            block = []
    out.extend(block)   # trailing (addrmap close, etc.)
    return "".join(out), converted


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    default_in = os.path.normpath(os.path.join(here, "..", "rtl", "macro", "stream_regs.rdl"))
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("rdl", nargs="?", default=default_in, help="input .rdl (default: stream_regs.rdl)")
    ap.add_argument("-o", "--out", help="output .rdl (default: <in>_nomon.rdl)")
    ap.add_argument("--regen", metavar="COPY_RTL_DIR",
                    help="after transform, run bin/peakrdl_generate.py and copy RTL here")
    args = ap.parse_args()

    if not os.path.isfile(args.rdl):
        sys.exit(f"error: RDL not found: {args.rdl}")
    out_path = args.out or re.sub(r"\.rdl$", "_nomon.rdl", args.rdl)

    with open(args.rdl) as f:
        text = f.read()
    new_text, converted = transform(text)
    with open(out_path, "w") as f:
        f.write(new_text)

    total = sum(n for _, n in converted)
    print(f"[rdl_monitors_ro] {len(converted)} monitor register(s) -> RO "
          f"({total} sw=rw/sw=w fields demoted to sw=r)")
    for name, n in converted:
        print(f"    {name}: {n} field(s)")
    print(f"[rdl_monitors_ro] wrote {out_path}")

    if args.regen:
        gen = _find_peakrdl_generate(here)
        if not gen:
            sys.exit("error: could not locate bin/peakrdl_generate.py (set REPO_ROOT)")
        cmd = [sys.executable, gen, out_path, "--copy-rtl", args.regen]
        print(f"[rdl_monitors_ro] regenerating: {' '.join(cmd)}")
        subprocess.run(cmd, check=True)


if __name__ == "__main__":
    main()
