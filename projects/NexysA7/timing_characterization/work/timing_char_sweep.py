#!/usr/bin/env python3
"""Characterize timing_char asic_only primitives against ASAP7 RVT.

For each (primitive, corner):
  - synthesize at two probe sizes (short & long)
  - get total flop->flop delay D and ABC level count `lev`
  - derive Tflop (Tcq+Tsu) and per-level gate delay via linear extrapolation:
        D = Tflop + lev * per_level_delay

Then for each (primitive, corner, freq):
  - budget = period_ps - Tflop
  - max_levels = floor(budget / per_level_delay)

Covers all 9 chain/tree FUBs under rtl/asic_only/fub/.  The MULT row doubles
as the recommended proxy for "mixed-bag" combinational logic since a real
multiplier tree is structurally diverse (AND, XOR, full adder, carry).

Output: /tmp/charwork/asap7/timing_char_data.csv
"""
from __future__ import annotations
import csv
import math
import re
import subprocess
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path

ASIC_ONLY = Path("/mnt/data/github/RTLDesignSherpa/projects/NexysA7/timing_characterization/rtl/asic_only")
FUB = ASIC_ONLY / "fub"
COMMON = ASIC_ONLY / "common"
LIB_DIR = Path.home() / "eda/asap7_merged"
LIB = {c: LIB_DIR / f"asap7sc7p5t_RVT_{c}_nldm.lib" for c in ("TT", "FF", "SS")}

WORK = Path("/tmp/charwork/asap7/char_sweep")
WORK.mkdir(parents=True, exist_ok=True)
CSV_OUT = Path("/tmp/charwork/asap7/timing_char_data.csv")

FREQS_MHZ = [500, 750, 1000]
CORNERS   = ["TT", "FF", "SS"]

# Filelist passed to slang: every primitive + every common dep.  slang resolves
# module references by name, so we hand it the whole tree.
ALL_SV = sorted(FUB.glob("*.sv")) + sorted(COMMON.glob("*.sv"))

# ---------------------------------------------------------------------------- #
# Primitive registry
# ---------------------------------------------------------------------------- #
@dataclass
class Prim:
    name:      str              # SV module name
    label:     str              # row label in characterization sheet
    param:     str              # parameter we vary for the 2-point probe
    short_val: int
    long_val:  int
    extra:     dict = field(default_factory=dict)  # other -G params
    note:      str = ""

PRIMS = [
    Prim("inverter_chain",     "INV",      "NUM_INVERTERS", 4, 16,
         note="ABC strash collapses INV pairs - chain depth is not preserved."),
    Prim("nand_chain",         "NAND",     "LEVELS",        3, 6),
    Prim("xor_tree",           "XOR",      "LEVELS",        3, 6),
    Prim("mux_tree",           "MUX",      "LEVELS",        3, 6),
    Prim("carry_chain",        "CARRY",    "WIDTH",         8, 32,
         note="ripple-carry adder; per-bit carry propagation delay"),
    Prim("multiplier_tree",    "MULT",     "WIDTH",         8, 16,
         extra={"MULT_TYPE": 0},
         note="inferred mult tree; RECOMMENDED PROXY for generic mixed logic"),
    Prim("gray_counter_chain", "GRAY_CTR", "WIDTH",         8, 32),
    Prim("queue_depth",        "QUEUE",    "DEPTH",         4, 16,
         extra={"DATA_WIDTH": 4},
         note="FIFO output-mux depth scales as log2(DEPTH)"),
    Prim("clock_divider_chain","CLK_DIV",  "NUM_STAGES",    2, 8,
         extra={"COUNTER_WIDTH": 8, "PICKOFF": 1}),
]

# ---------------------------------------------------------------------------- #
# Yosys script
# ---------------------------------------------------------------------------- #
def build_ys(prim: Prim, value: int, corner: str, period_ps: int, work: Path) -> Path:
    lib = LIB[corner]
    gparams_list = [f"-G {prim.param}={value}"]
    for k, v in prim.extra.items():
        gparams_list.append(f"-G {k}={v}")
    gparams = " ".join(gparams_list)
    sv_files = " \\\n        ".join(str(f) for f in ALL_SV)
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
        {sv_files}
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
    r = subprocess.run(cmd, capture_output=True, text=True, cwd=work, timeout=600)
    dt = time.time() - t0
    if r.returncode != 0:
        return {"status": "FAIL", "elapsed_s": round(dt, 1),
                "error": (r.stderr[:300] or log.read_text()[-300:])}
    delay, lev = parse_abc(log.read_text())
    return {"status": "OK", "delay_ps": delay, "lev": lev,
            "elapsed_s": round(dt, 1)}

def main():
    PROBE_PERIOD = 1000  # ABC target — we read the achieved delay regardless

    rows = []
    total = len(PRIMS) * 2 * len(CORNERS)
    print(f"[char_sweep] {len(PRIMS)} primitives x 2 sizes x {len(CORNERS)} corners "
          f"= {total} runs", file=sys.stderr)
    i = 0
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
                    print(f"FAIL  {res.get('error','')[:140]}", file=sys.stderr)
                row = {"primitive": prim.label, "param": prim.param, "value": value,
                       "corner": corner, "note": prim.note, **res}
                rows.append(row)

    with CSV_OUT.open("w", newline="") as f:
        cols = ["primitive", "param", "value", "corner", "status",
                "delay_ps", "lev", "elapsed_s", "note", "error"]
        w = csv.DictWriter(f, fieldnames=cols, extrasaction="ignore")
        w.writeheader()
        for r in rows:
            w.writerow(r)
    print(f"[char_sweep] -> {CSV_OUT}", file=sys.stderr)

if __name__ == "__main__":
    main()
