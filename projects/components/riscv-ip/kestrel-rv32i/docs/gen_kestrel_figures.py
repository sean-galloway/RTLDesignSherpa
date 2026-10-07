#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
#
# Regenerates the committed figures for the kestrel HAS/MAS docs:
#   - kestrel_has/assets/images/fig_2_1_system_context.png   (matplotlib)
#   - kestrel_mas/assets/images/fig_2_1_loader_composition.png (matplotlib)
#   - kestrel_mas/assets/wavedrom/wvf_4_1_basic_cycle.png    (wavedrom-cli + inkscape)
#   - kestrel_mas/assets/wavedrom/wvf_4_2_retry_sh3.png      (wavedrom-cli + inkscape)
#   - copies: falcon ladder + datapath diagrams from the simplified_rv32i
#     book assets, and the title-page logos from docs/logos.
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

GREEN = "#2E7D32"
GREEN_FILL = "#E8F5E9"
GRAY = "#424242"
LIGHT = "#F5F5F5"


# ---------------------------------------------------------------- matplotlib
def _boxes_draw(fig):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.patches import FancyBboxPatch, FancyArrowPatch

    plt.rcParams.update({"font.size": 11, "font.family": "DejaVu Sans"})

    def box(ax, x, y, w, h, text, fc="white", ec=GRAY, bold=False, fs=11):
        ax.add_patch(FancyBboxPatch((x, y), w, h,
                                    boxstyle="round,pad=0.02,rounding_size=0.04",
                                    linewidth=1.6, edgecolor=ec, facecolor=fc))
        ax.text(x + w / 2, y + h / 2, text, ha="center", va="center",
                fontsize=fs, color=GRAY,
                fontweight="bold" if bold else "normal")

    def arrow(ax, x0, y0, x1, y1, text="", lx=0, ly=0, style="-|>", color=GRAY):
        ax.add_patch(FancyArrowPatch((x0, y0), (x1, y1), arrowstyle=style,
                                     mutation_scale=16, linewidth=1.5,
                                     color=color))
        if text:
            ax.text((x0 + x1) / 2 + lx, (y0 + y1) / 2 + ly, text,
                    ha="center", va="center", fontsize=9, color=GRAY,
                    style="italic")

    return plt, FancyBboxPatch, box, arrow


def gen_system_context():
    plt, _, box, arrow = _boxes_draw(None)
    fig, ax = plt.subplots(figsize=(13.2, 6.6))
    ax.set_xlim(0, 13.2)
    ax.set_ylim(0, 6.6)
    ax.axis("off")

    # ---- left: minimal integration -------------------------------------
    ax.text(0.15, 6.25, "Minimal integration (no loader)",
            fontsize=13, color=GREEN, fontweight="bold")
    box(ax, 0.6, 3.3, 3.2, 1.7, "kestrel_core\n(RESET_ADDR)", fc=GREEN_FILL,
        ec=GREEN, bold=True, fs=12)
    box(ax, 5.2, 4.6, 3.3, 1.4, "instruction memory\n32-bit, combinational read")
    box(ax, 5.2, 2.4, 3.3, 1.4,
        "data memory\n32-bit, combinational read\nper-byte write merge")
    box(ax, 10.1, 3.4, 2.6, 1.3, "trace fabric\nRVFI + halt", fc=LIGHT)

    arrow(ax, 3.8, 4.55, 5.2, 5.2, "imem_addr", 0, 0.28)
    arrow(ax, 5.2, 4.75, 3.8, 4.1, "imem_rdata", 0, -0.3)
    arrow(ax, 3.8, 3.75, 5.2, 3.3, "dmem_req/we/addr\nwstrb/wdata", -0.1, 0.32)
    arrow(ax, 5.2, 2.7, 3.8, 3.25, "dmem_rdata", 0, -0.28)
    arrow(ax, 3.8, 3.6, 10.1, 3.95, "", 0, 0)
    ax.text(2.1, 2.55, "clk, rst_n", fontsize=9, color=GRAY, style="italic")
    arrow(ax, 2.1, 2.9, 2.1, 3.3)

    # ---- right: loader integration --------------------------------------
    ax.text(0.15, 1.95, "Loader integration (board)",
            fontsize=13, color=GREEN, fontweight="bold")
    box(ax, 0.6, 0.35, 2.5, 1.2, "host AXIL master\n(CPU / DMA / debug)")
    box(ax, 3.9, 0.15, 5.6, 1.7, "", fc=GREEN_FILL, ec=GREEN)
    ax.text(6.7, 1.55, "kestrel_mem_loader", ha="center", fontsize=12,
            color=GREEN, fontweight="bold")
    ax.text(6.7, 1.16, "imem[16K words]  dmem[16K words]  (distributed RAM)",
            ha="center", fontsize=9.5, color=GRAY)
    ax.text(6.7, 0.82, "CTRL (bit0=run)   axil4_slave_wr + axil4_slave_rd leaves",
            ha="center", fontsize=9.5, color=GRAY)
    ax.text(6.7, 0.45, "unified map: addr[17]=CTRL  addr[16]=array  addr[13:0]=index",
            ha="center", fontsize=9.5, color=GRAY)
    box(ax, 10.6, 0.35, 2.1, 1.2, "kestrel_core\n(clk, core_rst_n)",
        fc=GREEN_FILL, ec=GREEN, bold=True, fs=10)

    arrow(ax, 3.1, 0.95, 3.9, 0.95, "s_axil_* (AW/W/B, AR/R)", 0, 0.26)
    arrow(ax, 9.5, 1.15, 10.6, 1.05, "imem/dmem ports", 0, 0.26)
    arrow(ax, 9.2, 0.25, 10.6, 0.5, "core_rst_n", 0.1, -0.24)

    fig.tight_layout()
    out = HAS_IMG / "fig_2_1_system_context.png"
    fig.savefig(out, dpi=200, bbox_inches="tight", facecolor="white")
    plt.close(fig)
    print(f"  wrote {out.relative_to(DOCS)}")


def gen_loader_composition():
    plt, _, box, arrow = _boxes_draw(None)
    fig, ax = plt.subplots(figsize=(12.6, 7.2))
    ax.set_xlim(0, 12.6)
    ax.set_ylim(0, 7.2)
    ax.axis("off")

    box(ax, 0.3, 4.9, 2.5, 1.5, "AXIL master\n(host)")
    box(ax, 3.5, 5.6, 3.2, 1.2, "axil4_slave_wr\nAW/W/B skids (2/2/2)")
    box(ax, 3.5, 3.9, 3.2, 1.2, "axil4_slave_rd\nAR/R skids (2/4)")
    box(ax, 7.6, 4.6, 4.4, 2.4, "", fc=GREEN_FILL, ec=GREEN)
    ax.text(9.8, 6.65, "wrapper logic", ha="center", fontsize=11.5,
            color=GREEN, fontweight="bold")
    ax.text(9.8, 6.2, "wr_addr_q, wr_addr_pending_q, b_pending_q", ha="center",
            fontsize=9.5, color=GRAY)
    ax.text(9.8, 5.85, "run_q (CTRL bit0)  ->  core_rst_n", ha="center",
            fontsize=9.5, color=GRAY)
    ax.text(9.8, 5.5, "ld_wr_* (load mode)  core_wr_* (run mode)", ha="center",
            fontsize=9.5, color=GRAY)
    ax.text(9.8, 5.12, "one write process per array,\nper-byte merge (wstrb / dmem_wstrb)",
            ha="center", fontsize=9.5, color=GRAY)
    ax.text(9.8, 4.72, "comb read mux: index = addr[13:0], select = addr[16]",
            ha="center", fontsize=9.5, color=GRAY)

    box(ax, 7.6, 2.2, 2.1, 1.3, "imem\n16384 words", fc=LIGHT)
    box(ax, 9.9, 2.2, 2.1, 1.3, "dmem\n16384 words", fc=LIGHT)
    box(ax, 0.3, 0.5, 2.5, 1.2, "kestrel_core\n(imem/dmem ports)")

    arrow(ax, 2.8, 5.9, 3.5, 6.0, "s_axil AW/W/B", 0, 0.26)
    arrow(ax, 2.8, 5.3, 3.5, 4.6, "s_axil AR/R", 0, 0.28)
    arrow(ax, 6.7, 6.1, 7.6, 6.1, "fub_aw/w/b", 0, 0.24)
    arrow(ax, 6.7, 4.5, 7.6, 5.1, "fub_ar/r", 0, 0.24)
    arrow(ax, 9.0, 4.6, 8.6, 3.5, "imem wr + 3 comb reads", -0.9, 0.1)
    arrow(ax, 10.6, 4.6, 10.9, 3.5, "dmem wr + 3 comb reads", 1.05, 0.1)
    arrow(ax, 2.8, 1.1, 7.6, 1.35, "", 0, 0)
    arrow(ax, 7.6, 1.35, 2.8, 1.5, "", 0, 0)
    ax.text(5.2, 1.75, "core fetch + L/S (unified map)", fontsize=9, color=GRAY,
            style="italic", ha="center")
    arrow(ax, 11.6, 4.6, 11.9, 0.9, "core_rst_n", 0.55, 0)
    ax.text(3.5, 3.4, "o_dbg_busy_wr / o_dbg_busy_rd", fontsize=9, color=GRAY,
            style="italic")

    fig.tight_layout()
    out = MAS_IMG / "fig_2_1_loader_composition.png"
    fig.savefig(out, dpi=200, bbox_inches="tight", facecolor="white")
    plt.close(fig)
    print(f"  wrote {out.relative_to(DOCS)}")


# ------------------------------------------------------------------ copies
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
    copy(BOOK / "assets" / "images" / "fig_3_1_datapath.png",
         MAS_IMG / "fig_1_1_datapath.png")
    copy(REPO_LOGOS, HAS_IMG / "logo.png")
    copy(REPO_LOGOS, MAS_IMG / "logo.png")
    print("figures:")
    gen_system_context()
    gen_loader_composition()
    print("waveforms:")
    gen_wavedrom()
    print("done.")


if __name__ == "__main__":
    sys.exit(main())
