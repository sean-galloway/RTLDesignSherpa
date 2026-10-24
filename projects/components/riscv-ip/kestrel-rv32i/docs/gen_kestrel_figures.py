#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
#
# Regenerates the committed figures for the kestrel HAS/MAS docs:
#   - kestrel_mas/assets/wavedrom/wvf_4_1_basic_cycle.png    (wavedrom-cli + inkscape)
#   - kestrel_mas/assets/wavedrom/wvf_2_7_bram_load.png      (wavedrom-cli + inkscape)
#   - kestrel_mas/assets/wavedrom/wvf_4_3_halt.png           (wavedrom-cli + inkscape)
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
        # Kept byte-identical to the committed asset (back-ported 2026-10-21:
        # the JSON had been edited by hand without updating this dict, so a
        # regen churned it; the script is the source again).
        {
            "signal": [
                {
                    "name": "clk",
                    "wave": "P...",
                    "period": 1
                },
                {
                    "name": "",
                    "wave": "x2x2x.",
                    "data": [
                        "cycle n (LW)",
                        "cycle n+1 (ADDI)"
                    ]
                },
                {
                    "name": "pc",
                    "wave": "=.==",
                    "data": [
                        "A0",
                        "A0+4"
                    ],
                    "period": 1
                },
                {
                    "name": "imem_addr",
                    "wave": "=.==",
                    "data": [
                        "A0",
                        "A0+4"
                    ],
                    "period": 1
                },
                {
                    "name": "dmem_req",
                    "wave": "10..",
                    "period": 1
                },
                {
                    "name": "dmem_we",
                    "wave": "0...",
                    "period": 1
                },
                {
                    "name": "dmem_addr",
                    "wave": "x=x.",
                    "data": [
                        "W (rs1+imm)"
                    ]
                },
                {
                    "name": "dmem_rdata",
                    "wave": "x=x.",
                    "data": [
                        "mem[W]"
                    ]
                },
                {
                    "name": "rvfi_valid",
                    "wave": "11..",
                    "period": 1
                },
                {
                    "name": "rvfi_order",
                    "wave": "=.==",
                    "data": [
                        "k",
                        "k+1"
                    ],
                    "period": 1
                }
            ],
            "config": {
                "hscale": 1.6
            },
            "head": {
                "text": "Basic single-cycle execution: LW at cycle n, ADDI at cycle n+1"
            }
        },
    ),
    (
        MAS_WAV / "wvf_2_7_bram_load.json",
        MAS_WAV / "wvf_2_7_bram_load.png",
        {
            "signal": [
                {"name": "clk", "wave": "PPPP"},
                {"name": "", "wave": "2222", "data": ["cycle n", "cycle n+1", "cycle n+2", "cycle n+3"]},
                {"name": "pc", "wave": "==.=", "data": ["A0", "A4", "A8"]},
                {"name": "imem_addr_next", "wave": "=.==", "data": ["A4", "A8", "A12"]},
                {"name": "imem_rdata", "wave": "==.=", "data": ["ADDI", "LW", "next"]},
                {"name": "mem_wait", "wave": "010."},
                {"name": "dmem_req", "wave": "01.0"},
                {"name": "dmem_addr", "wave": "x=.x", "data": ["W"]},
                {"name": "dmem_rdata", "wave": "x.=x", "data": ["mem[W]"]},
                {"name": "rvfi_valid", "wave": "101."},
            ],
            "config": {"hscale": 2.4},
            "head": {"text": "Fetch at the next PC; LW waits one cycle"},
        },
    ),
    # The halt timing contract on the pins (rtl/top/kestrel_core.sv):
    # halt = halt_q | halt_now is visible on the detection cycle n, the
    # halting instruction retires that cycle as the one trap beat, and
    # from n+1 halt_q holds rvfi_valid low and the PC frozen.
    (
        MAS_WAV / "wvf_4_3_halt.json",
        MAS_WAV / "wvf_4_3_halt.png",
        {
            "signal": [
                {"name": "clk", "wave": "PPPPP"},
                {"name": "", "wave": "22222", "data": ["n-1", "n (halting)", "n+1", "n+2", "n+3"]},
                {"name": "pc", "wave": "==...", "data": ["P", "P+4"]},
                {"name": "insn", "wave": "==...", "data": ["ADDI", "ECALL"]},
                {"name": "halt_now", "wave": "010.."},
                {"name": "halt_q", "wave": "0.1.."},
                {"name": "halt", "wave": "01..."},
                {"name": "halt_cause", "wave": "=====", "data": ["0", "1", "1", "1", "1"]},
                {"name": "rvfi_valid", "wave": "1.0.."},
                {"name": "rvfi_trap", "wave": "010.."},
                {"name": "rvfi_rd_addr", "wave": "==x..", "data": ["rd", "0"]},
            ],
            "config": {"hscale": 2.4},
            "head": {"text": "Halt on the pins: trap beat at cycle n, frozen from n+1"},
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
