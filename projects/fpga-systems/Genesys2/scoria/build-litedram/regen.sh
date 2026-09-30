#!/usr/bin/env bash
# Generate the Genesys 2 LiteDRAM DDR3 core for BUILDING.
#
# Differs from the scoria component's regen_litedram_ddr3_ref.sh, which makes a
# core to be READ: that one targets A7DDRPHY for continuity with the DDR2
# reference and is never synthesized. This one targets the real board, so it
# builds the gateware sources Vivado will consume, and --bios builds the BIOS
# the memtest runs from.
#
# TRAPS -- all three cost an attempt the first time this was run, and none of
# them fails in a way that points at itself:
#
#  1. RUN FROM A NEUTRAL DIRECTORY. If the cwd contains the litex/migen CLONES,
#     `import migen` resolves to the clone ROOT as a namespace package rather
#     than the installed one, and generation dies with a misleading
#     "NameError: name 'Signal' is not defined" from inside litex/gen/signal.py.
#     Nothing is wrong with the install. This script cds to a scratch dir.
#  2. --no-compile-software DOES NOT avoid the software dependencies.
#     litedram_gen imports pythondata-software-picolibc AND
#     pythondata-software-compiler_rt at module load regardless of the flag, so
#     both must be installed (from git) even when no BIOS is built.
#  3. The "Python 3.10" in the recorded recipe is about PyPI, not Python. migen
#     installed FROM GIT infers ClockDomain names correctly on 3.12; only PyPI
#     migen 0.9.2 is broken.
#
# Install the venv from GIT, never PyPI -- recipe in the pumice flow's
# 2026-09-10_tooling_notes.md. LITEX_VENV overrides the location, which matters
# because a venv under /tmp does not survive a reboot.
#
#   ./regen.sh            gateware only (enough to lint and synthesize)
#   ./regen.sh --bios     gateware + BIOS (needed for the on-board memtest)
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VENV="${LITEX_VENV:-/tmp/claude-1000/litex-venv}"
GEN="$VENV/bin/litedram_gen"
CFG="$HERE/litedram_genesys2_ddr3.yml"
OUT="$HERE/gen"

WITH_BIOS=0
[ "${1:-}" = "--bios" ] && WITH_BIOS=1

[ -x "$GEN" ] || {
    echo "no litedram_gen in $VENV"
    echo "set LITEX_VENV, or build one from GIT (recipe:"
    echo "  projects/fpga-systems/NexysA7/pumice/ddr2-characterization/flows-litedram-uart/2026-09-10_tooling_notes.md)"
    exit 1
}

SCRATCH="$(mktemp -d)"; trap 'rm -rf "$SCRATCH"' EXIT
cd "$SCRATCH"          # trap 1

FLAGS=(--no-compile-gateware)   # Vivado runs from our own tcl, not litex's
[ "$WITH_BIOS" = "0" ] && FLAGS+=(--no-compile-software)

echo "[regen] $CFG -> $OUT  (bios=$WITH_BIOS)"
"$GEN" "$CFG" --name litedram_genesys2_ddr3 --output-dir "$OUT" "${FLAGS[@]}"

echo "generated:"
find "$OUT" -name '*.v' | xargs ls -l 2>/dev/null | awk '{print "   "$5"B  "$NF}'
