#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
#
# Regenerates the committed figures for the kestrel HAS/MAS docs:
#   - kestrel_mas/assets/wavedrom/wvf_4_1_basic_cycle.png    (wavedrom-cli + inkscape)
#   - kestrel_mas/assets/wavedrom/wvf_4_2_retry_sh3.png      (wavedrom-cli + inkscape)
#   - copies: the falcon ladder from the simplified_rv32i book assets, and
#     the title-page logos from docs/logos.
# The block diagrams (system context, datapath, loader composition) are
# graphviz sources in kestrel_{has,mas}/assets/graphviz/, rendered by that
# directory's regenerate_all_graphviz.sh.
#
# Usage: python3 gen_kestrel_figures.py   (run from this directory)

import pathlib
import shutil
import subprocess
import sys

DOCS = pathlib.Path(__file__).resolve().parent
BOOK = DOCS / "simplified_rv32i"
REPO_LOGOS = DOCS.parents[4] / "docs" / "logos" / "Logo_200px.png"

HAS_IMG = DOCS / "kestrel_has" / "assets" / "images"
MAS_IMG = DOCS / "kestrel_mas" / "assets" / "images"
MAS_WAV = DOCS / "kestrel_mas" / "assets" / "wavedrom"



def copy(src, dst):
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(src, dst)
    print(f"  copied {dst.relative_to(DOCS)}")


# ----------------------------------------------------------------- wavedrom
WAVFOMS = [
    (
        MAS_WAV / "wvf_4_1_basic_cycle.json",
        MAS_WAV / "wvf_4_1_basic_cycle.png",
        {
            "signal": [
                {"name": "clk", "wave": "PP"},
                {"name": "", "wave": "22", "data": ["cycle n", "cycle n+1"]},
                {"name": "pc", "wave": "==", "data": ["A0", "A0+4"]},
                {"name": "imem_addr", "wave": "==", "data": ["A0", "A0+4"]},
                {"name": "dmem_req", "wave": "10"},
                {"name": "dmem_we", "wave": "00"},
                {"name": "dmem_addr", "wave": "=x", "data": ["W"]},
                {"name": "dmem_rdata", "wave": "=x", "data": ["mem[W]"]},
                {"name": "rvfi_valid", "wave": "11"},
                {"name": "rvfi_order", "wave": "==", "data": ["k", "k+1"]},
            ],
            "config": {"hscale": 2.4},
            "head": {"text": "Basic single-cycle execution: LW at cycle n, ADDI at cycle n+1"},
        },
    ),
    (
        MAS_WAV / "wvf_4_2_retry_sh3.json",
        MAS_WAV / "wvf_4_2_retry_sh3.png",
        {
            "signal": [
                {"name": "clk", "wave": "PPP"},
                {"name": "", "wave": "222", "data": ["cycle n", "cycle n+1", "cycle n+2"]},
                {"name": "pc", "wave": "===", "data": ["A4", "A4", "A4+4"]},
                {"name": "dmem_req", "wave": "110"},
                {"name": "dmem_we", "wave": "110"},
                {"name": "dmem_addr", "wave": "==x", "data": ["W", "W+4"]},
                {"name": "dmem_wstrb", "wave": "22x", "data": ["4'b1000", "4'b0001"]},
                {"name": "ls_retry", "wave": "010"},
                {"name": "rvfi_valid", "wave": "010"},
            ],
            "config": {"hscale": 2.4},
            "head": {"text": "Cross-word store of a halfword at byte offset 3 (SH@3): beat 1 at cycle n, beat 2 at cycle n+1"},
        },
    ),
]


def gen_wavedrom():
    import json
    for json_path, png_path, doc in WAVFOMS:
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
    copy(BOOK / "assets" / "images" / "fig_1_1_falcon_ladder.png",
         HAS_IMG / "fig_1_1_falcon_ladder.png")
    copy(REPO_LOGOS, HAS_IMG / "logo.png")
    copy(REPO_LOGOS, MAS_IMG / "logo.png")
    print("waveforms:")
    gen_wavedrom()
    print("done.")


if __name__ == "__main__":
    sys.exit(main())
