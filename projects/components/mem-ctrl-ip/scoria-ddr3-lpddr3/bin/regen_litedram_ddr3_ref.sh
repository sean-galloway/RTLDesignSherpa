#!/usr/bin/env bash
# Generate the LiteDRAM DDR3 reference core for READING (not for building).
#
# See litedram_ddr3_ref.yml for why this exists. The output is a reference
# implementation to compare scoria's HAS against -- particularly ZQ calibration
# scheduling, write leveling and the MR0-MR3 init order, none of which the DDR2
# LiteDRAM core in the pumice flow contains.
#
# The venv: install from GIT, not PyPI. PyPI migen's ClockDomain() infers its
# name by inspecting caller bytecode and that inference is broken on modern
# Python, killing every target. The recipe is in the pumice flow's
# 2026-09-10_tooling_notes.md; LITEX_VENV overrides the location, which matters
# because a venv under /tmp does not survive the session.
# TRAPS, all three of which cost an attempt when this was first run:
#
#  1. RUN FROM A NEUTRAL DIRECTORY. If the cwd contains the litex/migen CLONES,
#     `import migen` resolves to the clone ROOT as a namespace package instead
#     of the installed package, and generation dies with a misleading
#     "NameError: name 'Signal' is not defined" from inside litex/gen/signal.py.
#     Nothing is wrong with the install. This script cds to a scratch dir.
#  2. --no-compile-software DOES NOT avoid the software dependencies.
#     litedram_gen imports pythondata-software-picolibc AND
#     pythondata-software-compiler_rt at module load regardless of the flag, so
#     both must be installed (from git) even though no BIOS is built.
#  3. The "Python 3.10" in the recorded recipe is about PyPI, not Python.
#     migen installed FROM GIT infers ClockDomain names correctly on 3.12
#     (verified: ClockDomain().name == 'cd'). Only PyPI migen 0.9.2 is broken.
set -euo pipefail
VENV="${LITEX_VENV:-/tmp/claude-1000/litex-venv}"
GEN="$VENV/bin/litedram_gen"
CFG="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/litedram_ddr3_ref.yml"
OUT="${1:-/tmp/litedram_ddr3_ref}"
SCRATCH="$(mktemp -d)"; trap 'rm -rf "$SCRATCH"' EXIT

[ -x "$GEN" ] || { echo "no litedram_gen in $VENV -- set LITEX_VENV (recipe: pumice flow 2026-09-10_tooling_notes.md)"; exit 1; }

# --no-compile-gateware: no Vivado. --no-compile-software: no BIOS, so no
# riscv-gcc and no picolibc, neither of which is needed to read the RTL.
# cd into scratch: see trap 1 above.
cd "$SCRATCH"
"$GEN" "$CFG" --name litedram_ddr3_ref --output-dir "$OUT" \
       --no-compile-gateware --no-compile-software

echo "generated under $OUT:"
find "$OUT" -name '*.v' | xargs ls -l 2>/dev/null | awk '{print "   "$5"B  "$NF}'
