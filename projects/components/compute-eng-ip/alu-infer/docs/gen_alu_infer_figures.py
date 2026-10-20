#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
#
# Regenerates the committed figures for the alu-infer MAS:
#   - alu_infer_mas/assets/wavedrom/wvf_3_1_invocation_handshake.png
#   - alu_infer_mas/assets/wavedrom/wvf_4_1_mac_chain.png
#     (wavedrom-cli + inkscape)
#   - title-page logo, copied from docs/logos.
# The block diagrams (datapath overview, full block) live in
# ../assets/graphviz/ (the PRD's directory) and are copied into
# alu_infer_mas/assets/graphviz/ by this script with a "derived from"
# header — keep the PRD copies canonical and re-run this script after
# re-rendering them.
#
# Usage: python3 gen_alu_infer_figures.py   (run from this directory)

import pathlib
import shutil
import subprocess
import sys

import json

DOCS = pathlib.Path(__file__).resolve().parent
REPO_LOGOS = DOCS.parents[4] / "docs" / "logos" / "Logo_200px.png"
PRD_GRAPHS = DOCS.parent / "assets" / "graphviz"

MAS_IMG = DOCS / "alu_infer_mas" / "assets" / "images"
MAS_WAV = DOCS / "alu_infer_mas" / "assets" / "wavedrom"
MAS_GRAPHS = DOCS / "alu_infer_mas" / "assets" / "graphviz"

DERIVED_NOTE = (
    "// DERIVED from ../../assets/graphviz/{name} (PRD-canonical) — keep in\n"
    "// line by copying after regenerating the PRD figure; do not edit here.\n"
)


# ----------------------------------------------------------------- wavedrom
WAVEFORMS = [
    (
        MAS_WAV / "wvf_3_1_invocation_handshake.json",
        MAS_WAV / "wvf_3_1_invocation_handshake.png",
        {
            "signal": [
                {"name": "clk", "wave": "P.........."},
                {"name": "", "wave": "2222222222", "data": ["n", "n+1", "n+2", "n+3", "n+4", "n+5", "n+6", "n+7", "n+8", "n+9"]},
                {"name": "valid (FSM)", "wave": "110......."},
                {"name": "func_sel[4:0]", "wave": "22x.......", "data": ["MUL", "MUL"]},
                {"name": "ready (ALU)", "wave": "010......."},
                {"name": "issue = valid & ready", "wave": ".10......."},
                {"name": "operand lines", "wave": "x=x.......", "data": ["A0/B0 · A1/B1 (same clock)"]},
                {"name": "result_valid (ALU)", "wave": ".....1110."},
                {"name": "result_ready (FSM)", "wave": "111110011."},
                {"name": "result_line", "wave": "x....=22x.", "data": ["result"]},
                {"name": "retire", "wave": ".......10."},
            ],
            "config": {"hscale": 2.2},
            "head": {"text": "Elastic handshake: input stall, all operand lines captured at issue, result offered at L = 4, output stall holds until consumed"},
        },
    ),
    (
        MAS_WAV / "wvf_3_2_back_to_back.json",
        MAS_WAV / "wvf_3_2_back_to_back.png",
        {
            "signal": [
                {"name": "clk", "wave": "P......."},
                {"name": "", "wave": "22222222", "data": ["n", "n+1", "n+2", "n+3", "n+4", "n+5", "n+6", "n+7"]},
                {"name": "valid (FSM)", "wave": "1110...."},
                {"name": "func_sel[4:0]", "wave": "222x....", "data": ["MUL", "MUL", "RELU"]},
                {"name": "ready (ALU)", "wave": "0111...."},
                {"name": "result_line", "wave": "x....222", "data": ["r(MUL)", "r(MUL)", "r(RELU)"]},
            ],
            "config": {"hscale": 2.2},
            "head": {"text": "Back-to-back issue: any opcodes, one per clock while ready, in-order results (L drawn = 4)"},
        },
    ),
    (
        MAS_WAV / "wvf_4_1_mac_chain.json",
        MAS_WAV / "wvf_4_1_mac_chain.png",
        {
            "signal": [
                {"name": "clk", "wave": "P......."},
                {"name": "", "wave": "22222222", "data": ["n", "n+1", "n+2", "n+3", "n+4", "n+5", "n+6", "n+7"]},
                {"name": "acc_ctrl[1:0]", "wave": ".22222x.", "data": ["CLEAR", "ACC", "ACC", "ACC", "DRAIN"]},
                {"name": "valid (FSM)", "wave": "0111110."},
                {"name": "ready (ALU)", "wave": "0111110."},
                {"name": "acc lane 0 (fp32)", "wave": "==2=2==x", "data": ["0", "p0", "p0+p1", "p0+p1+p2"]},
                {"name": "result_line", "wave": "x..2222x", "data": ["view0", "view1", "view2", "drain"]},
            ],
            "config": {"hscale": 2.2},
            "head": {"text": "MAC chain at II=1: pipelined exact product + 1-cycle fp32 accumulate"},
        },
    ),
]


def gen_wavedrom():
    for json_path, png_path, doc in WAVEFORMS:
        json_path.parent.mkdir(parents=True, exist_ok=True)
        json_path.write_text(json.dumps(doc, indent=2) + "\n")
        svg_path = json_path.with_suffix(".svg").resolve()
        png_abs = png_path.resolve()
        subprocess.run(["wavedrom-cli", "-i", str(json_path), "-s", str(svg_path)],
                       check=True, capture_output=True)
        subprocess.run(["inkscape", str(svg_path),
                        "--export-filename=" + str(png_abs), "-w", "1500"],
                       check=True, capture_output=True)
        print(f"  wrote {png_path.relative_to(DOCS)}")


def copy_graphviz():
    MAS_GRAPHS.mkdir(parents=True, exist_ok=True)
    for src in sorted(PRD_GRAPHS.glob("0*.dot")):
        dst = MAS_GRAPHS / src.name
        text = src.read_text()
        note = DERIVED_NOTE.format(name=src.name)
        if not text.startswith("// DERIVED"):
            text = note + text
        dst.write_text(text)
        print(f"  wrote {dst.relative_to(DOCS)} (from PRD assets)")
    regen = PRD_GRAPHS / "regenerate_all_graphviz.sh"
    if regen.exists():
        shutil.copyfile(regen, MAS_GRAPHS / regen.name)
        pngs = sorted(PRD_GRAPHS.glob("0*.png"))
        for p in pngs:
            shutil.copyfile(p, MAS_GRAPHS / p.name)
        print(f"  copied {len(pngs)} rendered PNGs + regenerate script")


def main():
    MAS_IMG.mkdir(parents=True, exist_ok=True)
    print("copies:")
    shutil.copyfile(REPO_LOGOS, MAS_IMG / "logo.png")
    print(f"  copied {MAS_IMG.relative_to(DOCS)}/logo.png")
    print("graphviz:")
    copy_graphviz()
    print("waveforms:")
    gen_wavedrom()
    print("done.")


if __name__ == "__main__":
    sys.exit(main())
