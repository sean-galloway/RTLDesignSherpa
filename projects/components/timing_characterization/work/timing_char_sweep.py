#!/usr/bin/env python3
"""Characterize timing_char asic_only primitives against ASAP7 RVT.

For each (primitive, corner):
  - synthesize at two chain depths (short & long)
  - get total flop->flop delay D and ABC level count `lev`
  - derive Tflop (Tcq+Tsu) and per-level gate delay via linear extrapolation:
        D = Tflop + lev * per_level_delay

Then for each (primitive, corner, freq):
  - budget = period_ps - Tflop
  - max_levels = floor(budget / per_level_delay)

Output: /tmp/charwork/asap7/timing_char_data.csv
"""
from __future__ import annotations
import csv
import math
import re
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path

ASIC_ONLY = Path("/mnt/data/github/RTLDesignSherpa/projects/components/timing_characterization/rtl/asic_only/fub")
LIB_DIR = Path.home() / "eda/asap7_merged"
LIB = {c: LIB_DIR / f"asap7sc7p5t_RVT_{c}_nldm.lib" for c in ("TT", "FF", "SS")}

WORK = Path("/tmp/charwork/asap7/char_sweep")
WORK.mkdir(parents=True, exist_ok=True)
CSV_OUT = Path("/tmp/charwork/asap7/timing_char_data.csv")

FREQS_MHZ = [500, 750, 1000]
CORNERS   = ["TT", "FF", "SS"]

# ---------------------------------------------------------------------------- #
# Primitives: each row in the characterization sheet
#
# For chain primitives: short_n and long_n bracket the chain depth.
# We use synth at both to derive per-level gate delay and Tflop separately.
# ---------------------------------------------------------------------------- #
@dataclass
class Prim:
    name:      str   # primitive name (matches SV module name)
    label:     str   # row label in characterization sheet
    param:     str   # parameter that sets chain depth/levels
    short_val: int
    long_val:  int
    rtl:       Path

PRIMS = [
    Prim("inverter_chain", "INV",  "NUM_INVERTERS",  4, 16,
         ASIC_ONLY / "inverter_chain.sv"),
    Prim("nand_chain",     "NAND", "LEVELS",         3, 6,    # 2**6=64 leaves
         ASIC_ONLY / "nand_chain.sv"),
    Prim("xor_tree",       "XOR",  "LEVELS",         3, 6,
         ASIC_ONLY / "xor_tree.sv"),
    Prim("mux_tree",       "MUX",  "LEVELS",         3, 6,
         ASIC_ONLY / "mux_tree.sv"),
]

# ---------------------------------------------------------------------------- #
# Yosys script
# ---------------------------------------------------------------------------- #
def build_ys(prim: Prim, value: int, corner: str, period_ps: int, work: Path) -> Path:
    lib = LIB[corner]
    gparams = f"-G {prim.param}={value}"
    netlist = work / "netlist.v"
    stat    = work / "stat.txt"
    ys_path = work / "synth.ys"
    abc_script = work / "abc.script"
    abc_script.write_text(
        "strash\n"
        "map -p -B 0.2 -A 0.9\n"
        "buffer -c -N 6\n"
        "topo\n"
        "upsize -c\n"
        "dnsize -c\n"
        "stime -c\n"
        "print_stats -m\n"
    )
    ys = f"""\
plugin -i slang
read_slang -DUSE_ASYNC_RESET \\
    --top {prim.name} {gparams} \\
        {prim.rtl}
async2sync
read_liberty -lib {lib}
synth -top {prim.name} -flatten
dfflibmap -liberty {lib} \\
    -dont_use DFFASRHQN* -dont_use DFFHQN* -dont_use DFFLQN* \\
    -dont_use SDFL* -dont_use DFFLQ*
abc -liberty {lib} -script {abc_script}
opt_clean -purge
tee -o {stat} stat -liberty {lib}
write_verilog -noattr {netlist}
"""
    ys_path.write_text(ys)
    return ys_path

# ---------------------------------------------------------------------------- #
# Parsers
# ---------------------------------------------------------------------------- #
NUM = r"(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?"
ABC_DELAY_RE = re.compile(rf"Delay\s*=\s*({NUM})\s*ps")
ABC_LEV_RE   = re.compile(r"\blev\s*=\s*(\d+)")

def parse_abc(log_text: str):
    delay, lev = None, None
    for line in log_text.splitlines():
        m = ABC_DELAY_RE.search(line)
        if m: delay = float(m.group(1))
        m = ABC_LEV_RE.search(line)
        if m: lev = int(m.group(1))
    return delay, lev

# ---------------------------------------------------------------------------- #
# Driver
# ---------------------------------------------------------------------------- #
def synth_once(prim: Prim, value: int, corner: str, period_ps: int) -> dict:
    tag = f"{prim.name}__{prim.param}{value}__{corner}"
    work = WORK / tag
    work.mkdir(parents=True, exist_ok=True)
    ys = build_ys(prim, value, corner, period_ps, work)
    log = work / "yosys.log"
    cmd = ["yosys", "-ql", str(log), str(ys)]
    t0 = time.time()
    r = subprocess.run(cmd, capture_output=True, text=True, cwd=work, timeout=300)
    dt = time.time() - t0
    if r.returncode != 0:
        return {"status": "FAIL", "elapsed_s": round(dt, 1),
                "error": (r.stderr[:200] or log.read_text()[-200:])}
    delay, lev = parse_abc(log.read_text())
    return {"status": "OK", "delay_ps": delay, "lev": lev,
            "elapsed_s": round(dt, 1)}

def main():
    # period for synth target — use 1 ns for all probes (ABC tries to meet it
    # but we read the achieved delay, not the slack).
    PROBE_PERIOD = 1000

    rows = []
    print(f"[char_sweep] {len(PRIMS)} primitives x 2 depths x {len(CORNERS)} corners "
          f"= {len(PRIMS)*2*len(CORNERS)} runs", file=sys.stderr)
    i = 0
    total = len(PRIMS) * 2 * len(CORNERS)
    for prim in PRIMS:
        for value in (prim.short_val, prim.long_val):
            for corner in CORNERS:
                i += 1
                print(f"[{i:2d}/{total}] {prim.label} {prim.param}={value} {corner} ... ",
                      end="", file=sys.stderr, flush=True)
                res = synth_once(prim, value, corner, PROBE_PERIOD)
                if res["status"] == "OK":
                    print(f"D={res['delay_ps']:.1f}ps lev={res['lev']} ({res['elapsed_s']}s)",
                          file=sys.stderr)
                else:
                    print(f"FAIL  {res.get('error','')[:100]}", file=sys.stderr)
                row = {"primitive": prim.label, "param": prim.param, "value": value,
                       "corner": corner, **res}
                rows.append(row)

    with CSV_OUT.open("w", newline="") as f:
        cols = ["primitive", "param", "value", "corner", "status",
                "delay_ps", "lev", "elapsed_s", "error"]
        w = csv.DictWriter(f, fieldnames=cols, extrasaction="ignore")
        w.writeheader()
        for r in rows:
            w.writerow(r)
    print(f"[char_sweep] -> {CSV_OUT}", file=sys.stderr)

if __name__ == "__main__":
    main()
