#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
#
# Regenerates the committed figures for "Simplified RV32IM: peregrine":
#   - assets/wavedrom/wvf_*.png    the three PRD section-5 waveforms
#                                  (wavedrom-cli + inkscape)
#   - assets/images/fig_*.png      copies of the MAS block diagrams the book
#                                  teaches from (the MAS graphviz is the
#                                  source; rerun this after it changes)
#
# The waveforms are drawn from the cycle rules the MAS documents
# (peregrine_mas ch04_behavior: 01_pipeline_cycle, 03_branch_prediction,
# 04_traps, 05_m_unit) and that the RVFI checks in the cocotb suites
# enforce: a mispredict costs 2 bubbles, a trap, mret or fence.i 3, an
# iterative M instruction 33 stall cycles.
#
# Usage: python3 gen_figures.py   (from any directory)

import json
import pathlib
import shutil
import subprocess
import sys

BOOK = pathlib.Path(__file__).resolve().parent
WAV = BOOK / "assets" / "wavedrom"
IMG = BOOK / "assets" / "images"
MAS_GV = BOOK.parent / "peregrine_mas" / "assets" / "graphviz"

COPIES = [
    (MAS_GV / "peregrine_pipeline.png", IMG / "fig_1_1_pipeline.png"),
    (MAS_GV / "peregrine_predictor.png", IMG / "fig_2_1_predictor.png"),
    (MAS_GV / "peregrine_traps.png", IMG / "fig_3_1_traps.png"),
    (MAS_GV / "peregrine_dside.png", IMG / "fig_5_1_dside.png"),
]

GAP = object()   # a '|' column: time skipped, the previous value continues


def row(name, vals):
    """A data row: equal neighbours merge, None is 'x', GAP is '|'."""
    wave, data, prev = "", [], ()
    for v in vals:
        if v is GAP:
            wave += "|"
            continue
        if v is None:
            wave += "." if prev is None else "x"
        elif v == prev:
            wave += "."
        else:
            wave += "="
            data.append(v)
        prev = v
    return {"name": name, "wave": wave, "data": data}


def bit(name, vals):
    wave, prev = "", None
    for v in vals:
        if v is GAP:
            wave += "|"
            continue
        wave += "." if v == prev else str(v)
        prev = v
    return {"name": name, "wave": wave}


def clk(n, gaps=()):
    return {"name": "clk", "wave": "".join("|" if i in gaps else "P" for i in range(n))}


def cycles(labels):
    return {"name": "cycle", "wave": "".join("|" if l is GAP else "2" for l in labels),
            "data": [l for l in labels if l is not GAP]}


B = "-"   # a bubble: a flushed or empty stage

# ------------------------------------------------- 1: taken branch, two ways
# A taken branch BR fetched at n.  Predicted (BTB hit, counter taken): IF
# fetches the target T at n+1 and nothing is lost.  Mispredicted (predicted
# not taken): BR resolves in EX at n+2, the redirect flushes IF/ID and
# ID/EX, IF fetches T at n+3, and two retire slots are empty.
N8 = [f"n+{i}" if i else "n" for i in range(8)]
WAVE_BRANCH = {
    "signal": [
        clk(8),
        cycles(N8),
        ["predicted taken",
         row("IF", ["BR", "T", "T+4", "T+8", "T+12", "T+16", "T+20", "T+24"]),
         row("ID", [None, "BR", "T", "T+4", "T+8", "T+12", "T+16", "T+20"]),
         row("EX", [None, None, "BR", "T", "T+4", "T+8", "T+12", "T+16"]),
         bit("ex_mispredict", [0] * 8),
         row("retire (WB)", [None, None, None, None, "BR", "T", "T+4", "T+8"]),
         ],
        {},
        ["mispredicted",
         row("IF", ["BR", "BR+4", "BR+8", "T", "T+4", "T+8", "T+12", "T+16"]),
         row("ID", [None, "BR", "BR+4", B, "T", "T+4", "T+8", "T+12"]),
         row("EX", [None, None, "BR", B, B + " ", "T", "T+4", "T+8"]),
         bit("ex_mispredict", [0, 0, 1, 0, 0, 0, 0, 0]),
         row("retire (WB)", [None, None, None, None, "BR", B, B + " ", "T"]),
         ],
    ],
    "config": {"hscale": 1.6},
    "head": {"text": "A taken branch: predicted, 0 bubbles; mispredicted, 2 (redirect from EX)"},
}

# ----------------------------------------------------------- 2: trap entry
# An ecall E reaches MEM at m.  The trap commits there: mepc and mcause are
# written at the edge, the PC goes to mtvec (handler H), and IF/ID, ID/EX
# and the instruction leaving EX are flushed.  E retires as a trap beat at
# m+1 with no effects; the handler's first instruction retires at m+5.
M7 = ["m-1", "m", "m+1", "m+2", "m+3", "m+4", "m+5"]
WAVE_TRAP = {
    "signal": [
        clk(7),
        cycles(M7),
        row("IF", ["E+8", "E+12", "H", "H+4", "H+8", "H+12", "H+16"]),
        row("ID", ["E+4", "E+8", B, "H", "H+4", "H+8", "H+12"]),
        row("EX", ["E", "E+4", B, B + " ", "H", "H+4", "H+8"]),
        row("MEM", ["E-4", "E", B, B + " ", B + "  ", "H", "H+4"]),
        bit("mem_trap", [0, 1, 0, 0, 0, 0, 0]),
        row("mepc / mcause", ["old", "old", "E / 11", "E / 11", "E / 11", "E / 11", "E / 11"]),
        row("retire (WB)", ["E-8", "E-4", "E", B, B + " ", B + "  ", "H"]),
        bit("rvfi_trap", [0, 0, 1, 0, 0, 0, 0]),
    ],
    "config": {"hscale": 1.6},
    "head": {"text": "Trap entry: ecall commits in MEM, retires as a trap beat, 3 bubbles to the handler"},
}

# --------------------------------------------------------- 3: M-unit stall
# MUL reaches EX at e.  The unit starts (operands latched) at e, steps 32
# times, and is done at e+33: 33 stall cycles.  The PC, IF/ID and ID/EX
# hold; EX/MEM takes a bubble every cycle, so the older instructions drain
# and retire.  MUL leaves EX after e+33 and retires at e+35.
E10 = ["e-1", "e", "e+1", "e+2", GAP, "e+32", "e+33", "e+34", "e+35", "e+36"]
G = 4
WAVE_MDU = {
    "signal": [
        clk(10, gaps=(G,)),
        cycles(E10),
        row("ID", ["MUL", "A", "A", "A", GAP, "A", "A", "A+4", "A+8", "A+12"]),
        row("EX", ["X", "MUL", "MUL", "MUL", GAP, "MUL", "MUL", "A", "A+4", "A+8"]),
        bit("ex_m_stall", [0, 1, 1, 1, GAP, 1, 0, 0, 0, 0]),
        bit("mdu busy", [0, 0, 1, 1, GAP, 1, 0, 0, 0, 0]),
        bit("mdu done", [0, 0, 0, 0, GAP, 0, 1, 0, 0, 0]),
        row("MEM", ["W", "X", B, B, GAP, B, B, "MUL", "A", "A+4"]),
        row("retire (WB)", ["V", "W", "X", B, GAP, B, B, B, "MUL", "A"]),
    ],
    "config": {"hscale": 1.6},
    "head": {"text": "An iterative MUL holds EX for 33 stall cycles; EX/MEM takes bubbles while older work drains"},
}

WAVEFORMS = [
    ("wvf_2_1_branch", WAVE_BRANCH),
    ("wvf_3_1_trap_entry", WAVE_TRAP),
    ("wvf_4_1_m_stall", WAVE_MDU),
]


def gen_wavedrom():
    WAV.mkdir(parents=True, exist_ok=True)
    for stem, doc in WAVEFORMS:
        json_path = WAV / f"{stem}.json"
        svg_path = WAV / f"{stem}.svg"
        png_path = WAV / f"{stem}.png"
        json_path.write_text(json.dumps(doc, indent=2) + "\n")
        subprocess.run(["wavedrom-cli", "-i", str(json_path), "-s", str(svg_path)],
                       check=True, capture_output=True)
        subprocess.run(["inkscape", str(svg_path), "--export-filename=" + str(png_path),
                        "-w", "1500"], check=True, capture_output=True)
        print(f"  wrote {png_path.relative_to(BOOK)}")


def copy_figures():
    IMG.mkdir(parents=True, exist_ok=True)
    for src, dst in COPIES:
        if not src.is_file():
            sys.exit(f"missing MAS diagram {src}; run its regenerate_all_graphviz.sh")
        shutil.copyfile(src, dst)
        print(f"  copied {dst.relative_to(BOOK)}")


def main() -> int:
    print("figures:")
    copy_figures()
    print("waveforms:")
    gen_wavedrom()
    print("done.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
