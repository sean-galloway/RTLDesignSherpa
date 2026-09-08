#!/usr/bin/env bash
# Regenerate the LiteDRAM DDR2 cores for the comparison harness.
# Uses litex-venv310 (the proven build env; the 3.12 venv trips a LiteX CSR
# name-introspection bug). Requires litescope (auto-installed once).
#
#   ./regen.sh            # RTL only (structure/interface; empty BIOS ROM)
#   ./regen.sh --bios     # functional cores WITH the BIOS baked in (needs riscv-gcc)
set -euo pipefail
VENV=/tmp/litex-venv310
GEN="$VENV/bin/litedram_gen"
CFG=litedram_hp.yml

"$VENV/bin/python" -c 'import litescope' 2>/dev/null || \
  uv pip install --python "$VENV/bin/python" litescope

SW_FLAG="--no-compile-software"        # default: skip BIOS (no riscv-gcc needed)
[ "${1:-}" = "--bios" ] && SW_FLAG=""  # functional: compile BIOS into ROM (needs riscv-gcc)

echo "[regen] board core (real A7DDRPHY) ..."
"$GEN" "$CFG" --name litedram_core     --output-dir build_board --no-compile-gateware $SW_FLAG
echo "[regen] sim core (SDRAMPHYModel) ..."
"$GEN" "$CFG" --sim --name litedram_core_sim --output-dir build_sim --no-compile-gateware $SW_FLAG || true
echo "[regen] done. cores:"
find build_board build_sim -name '*.v' | xargs ls -l | awk '{print "   "$5"B  "$NF}'
