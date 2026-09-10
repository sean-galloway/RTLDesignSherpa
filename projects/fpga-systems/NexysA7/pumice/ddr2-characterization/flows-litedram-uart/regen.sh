#!/usr/bin/env bash
# Regenerate the LiteDRAM DDR2 cores for the comparison harness.
# Uses litex-venv310 (the proven build env; the 3.12 venv trips a LiteX CSR
# name-introspection bug). Requires litescope (auto-installed once).
#
#   ./regen.sh            # RTL only (structure/interface; empty BIOS ROM)
#   ./regen.sh --bios     # functional cores WITH the BIOS baked in (needs riscv-gcc)
set -euo pipefail
# Override with LITEX_VENV=... ; /tmp is cleared between sessions, so a
# hardcoded /tmp path is a guarantee this script stops working. See
# 2026-09-10_tooling_notes.md for the install recipe (git, NOT PyPI).
VENV="${LITEX_VENV:-/tmp/litex-venv310}"
GEN="$VENV/bin/litedram_gen"
CFG=litedram_hp.yml

[ -x "$GEN" ] || { echo "no litedram_gen in $VENV -- set LITEX_VENV (see 2026-09-10_tooling_notes.md)"; exit 1; }
"$VENV/bin/python" -c 'import litescope' 2>/dev/null || \
  "$VENV/bin/pip" install -q litescope

SW_FLAG="--no-compile-software"        # default: skip BIOS (no riscv-gcc needed)
[ "${1:-}" = "--bios" ] && SW_FLAG=""  # functional: compile BIOS into ROM (needs riscv-gcc)

echo "[regen] board core (real A7DDRPHY) ..."
"$GEN" "$CFG" --name litedram_core     --output-dir build_board --no-compile-gateware $SW_FLAG
echo "[regen] sim core (SDRAMPHYModel) ..."
"$GEN" "$CFG" --sim --name litedram_core_sim --output-dir build_sim --no-compile-gateware $SW_FLAG || true
# Vendor the BIOS CPU beside the core: the generated litedram_core.tcl refers
# to VexRiscv.v by an absolute path inside the LiteX venv, which does not
# survive the venv being rebuilt (and /tmp being cleared).
VEX=$(grep -o '/[^ }]*VexRiscv\.v' build_board/gateware/litedram_core.tcl 2>/dev/null | head -1 || true)
if [ -n "${VEX:-}" ] && [ -f "$VEX" ]; then
  cp "$VEX" build_board/gateware/VexRiscv.v
  echo "[regen] vendored $(basename "$VEX") beside the core"
fi

echo "[regen] done. cores:"
find build_board build_sim -name '*.v' | xargs ls -l | awk '{print "   "$5"B  "$NF}'
