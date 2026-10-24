#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
#
# Regenerates the committed figures for the gatling HAS/MAS docs:
#   - gatling_mas/assets/wavedrom/wvf_4_1_rotation.png   (wavedrom-cli + inkscape)
#   - copies: the title-page logos from docs/logos.
# The block diagrams (datapath, register file, memory system, system
# context, programmer view) and the two table figures (rotation grid,
# board address map) are graphviz sources in gatling_{has,mas}/assets/
# graphviz/, rendered by that directory's regenerate_all_graphviz.sh.
#
# Usage: python3 gen_gatling_figures.py   (run from this directory)

import json
import pathlib
import shutil
import subprocess
import sys

DOCS = pathlib.Path(__file__).resolve().parent
REPO_LOGOS = DOCS.parents[4] / "docs" / "logos" / "Logo_200px.png"

HAS_IMG = DOCS / "gatling_has" / "assets" / "images"
MAS_IMG = DOCS / "gatling_mas" / "assets" / "images"
MAS_WAV = DOCS / "gatling_mas" / "assets" / "wavedrom"


def copy(src, dst):
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(src, dst)
    print(f"  copied {dst.relative_to(DOCS)}")


# ----------------------------------------------------------------- wavedrom
# One rotation window on the core's pins, from rtl/top/gatling_core.sv:
# context 0's instruction i (a load) is fetched at t, its word is on
# imem_rdata at t+1 (D), it issues its data access at t+2 (X), the load
# word arrives and the beat retires at t+3 (W); context 0's next fetch is
# at t+4. Contexts 1-3 fill the other slots.
WAVEFORMS = [
    (
        MAS_WAV / "wvf_4_1_rotation.json",
        MAS_WAV / "wvf_4_1_rotation.png",
        {
            "signal": [
                {"name": "clk", "wave": "PPPPPPPP"},
                {"name": "", "wave": "22222222", "data": ["t", "t+1", "t+2", "t+3", "t+4", "t+5", "t+6", "t+7"]},
                {"name": "sel_q (context in F)", "wave": "========", "data": ["c0", "c1", "c2", "c3", "c0", "c1", "c2", "c3"]},
                {"name": "imem_ctx, imem_addr", "wave": "========", "data": ["c0: A", "c1", "c2", "c3", "c0: A+4", "c1", "c2", "c3"]},
                {"name": "imem_rdata (in D)", "wave": "x=======", "data": ["LW (c0)", "c1", "c2", "c3", "ADDI (c0)", "c1", "c2"]},
                {"name": "dmem_req (in X)", "wave": "0.10...."},
                {"name": "dmem_ctx, dmem_addr", "wave": "x.=x....", "data": ["c0: W"]},
                {"name": "dmem_rdata (in W)", "wave": "x..=x...", "data": ["mem[W]"]},
                {"name": "rvfi_valid", "wave": "0..1...."},
                {"name": "rvfi_ctx", "wave": "x..=====", "data": ["c0", "c1", "c2", "c3", "c0"]},
                {"name": "rvfi_insn", "wave": "x..=====", "data": ["LW", "c1", "c2", "c3", "ADDI"]},
            ],
            "config": {"hscale": 2.2},
            "head": {"text": "One rotation window on the pins: context 0's LW fetched at t retires at t+3; its ADDI is fetched at t+4"},
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


def main():
    HAS_IMG.mkdir(parents=True, exist_ok=True)
    MAS_IMG.mkdir(parents=True, exist_ok=True)
    print("copies:")
    copy(REPO_LOGOS, HAS_IMG / "logo.png")
    copy(REPO_LOGOS, MAS_IMG / "logo.png")
    print("waveforms:")
    gen_wavedrom()
    print("done.")


if __name__ == "__main__":
    sys.exit(main())
