#!/usr/bin/env bash
# ==============================================================================
# gen_litedram.sh -- generate fb_litedram, the S0 DDR3 controller (LiteDRAM)
# ==============================================================================
# Input:  rtl/litedram/fb_litedram.yml
# Output: rtl/generated/fb_litedram/        the core, VexRiscv.v, BIOS ROM .init
#                                           files and the core's own XDC
#                                           (gitignored: toolchain output)
#         rtl/generated/fb_litedram_bb/     Verilator blackbox of the core's
#                                           ports (tracked; the lint filelists)
#
# The recipe and its traps are the board-proven memtest build's
# (mem-ctrl-ip/scoria/build-litedram/regen.sh): run litedram_gen from a neutral
# directory, install LiteX from git, and copy VexRiscv.v in because
# litedram_gen does not emit it. --bios is always on here: the BIOS is what
# calibrates the PHY at boot.
#
# Skips when the outputs are current for this exact config (a hash stamp), so
# it can run as every build's PREBUILD without regenerating the BIOS each time.
# FB_LITEDRAM_FORCE=1 regenerates regardless. LITEX_VENV sets the venv;
# RISCV_GCC_DIR the RISC-V GCC the BIOS is compiled with.
# ==============================================================================
set -euo pipefail
AREA="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
REPO_ROOT="${REPO_ROOT:-$(git -C "$AREA" rev-parse --show-toplevel)}"
CFG="$AREA/rtl/litedram/fb_litedram.yml"
OUT="$AREA/rtl/generated/fb_litedram"
BB_DIR="$AREA/rtl/generated/fb_litedram_bb"
BB="$BB_DIR/fb_litedram_bb.sv"
STAMP="$OUT/.config.sha256"
VENV="${LITEX_VENV:-/tmp/claude-1000/litex-venv}"
GEN="$VENV/bin/litedram_gen"
BLACKBOX="$REPO_ROOT/projects/fpga-systems/Genesys2/mem-ctrl-ip/scoria/bin/gen_core_blackbox.py"
# The BIOS build needs a RISC-V GCC and the venv's meson/ninja on PATH.
RISCV_GCC_DIR="${RISCV_GCC_DIR:-/mnt/data/tools/xpack-riscv-none-elf-gcc/bin}"
export PATH="$RISCV_GCC_DIR:$VENV/bin:$PATH"

want="$(sha256sum "$CFG" | cut -d' ' -f1)"
if [ "${FB_LITEDRAM_FORCE:-0}" != "1" ] && [ -f "$STAMP" ] && [ "$(cat "$STAMP")" = "$want" ] \
   && [ -f "$OUT/gateware/fb_litedram.v" ] && [ -f "$OUT/gateware/VexRiscv.v" ] && [ -f "$BB" ]; then
    echo "[gen_litedram] current ($CFG)"
    exit 0
fi

[ -x "$GEN" ] || {
    echo "[gen_litedram] no litedram_gen in $VENV -- set LITEX_VENV (recipe: the"
    echo "  memtest build's regen.sh header) or restore rtl/generated/fb_litedram"
    exit 1
}

SCRATCH="$(mktemp -d)"; trap 'rm -rf "$SCRATCH"' EXIT
cd "$SCRATCH"
echo "[gen_litedram] $CFG -> $OUT (with BIOS)"
rm -rf "$OUT"
"$GEN" "$CFG" --name fb_litedram --output-dir "$OUT" --no-compile-gateware

VEX_DIR="$("$VENV/bin/python" -c 'import pythondata_cpu_vexriscv, os; print(os.path.join(os.path.dirname(pythondata_cpu_vexriscv.__file__), "verilog"))')"
[ -f "$VEX_DIR/VexRiscv.v" ] || { echo "[gen_litedram] no VexRiscv.v under $VEX_DIR"; exit 1; }
cp "$VEX_DIR/VexRiscv.v" "$OUT/gateware/VexRiscv.v"

mkdir -p "$BB_DIR"
python3 "$BLACKBOX" "$OUT/gateware/fb_litedram.v" -m fb_litedram -o "$BB"
echo "$want" > "$STAMP"
echo "[gen_litedram] done: $(ls "$OUT/gateware" | tr '\n' ' ')"
