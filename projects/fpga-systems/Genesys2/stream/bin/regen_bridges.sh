#!/bin/bash
# ==============================================================================
# regen_bridges.sh — regenerate every bridge owned by stream_char_framework
# ==============================================================================
#
# Walks $FRAMEWORK_ROOT/rtl/bridges/configs/*.toml and runs the bridge
# generator (projects/components/bridge/bin/bridge_generator.py) on each
# one, dropping outputs into:
#   $FRAMEWORK_ROOT/rtl/bridges/generated/<bridge>/   ← RTL package + adapters
#   $FRAMEWORK_ROOT/rtl/bridges/filelists/<bridge>.f  ← filelist (REPO_ROOT-anchored)
#
# RTL and filelists ONLY. The DV collateral under rtl/bridges/dv/ is
# hand-maintained; this script must not write there.
#
# It used to pass --generate-tests, and because it is the PREBUILD for
# `make bitstream`, building a bitstream silently reverted the test files. It
# destroyed three separate rounds of committed fixes (33ac787e, 90bca4c1,
# bd79af49) -- restoring, in each case, a generated import that is a literal
# SyntaxError, so the five bridge tests were not failing but ABSENT from the
# report. The generator no longer emits that import (it falls back to a
# sys.path import when a directory component is not a legal Python identifier),
# but the DV files also carry area-specific things a shared generator cannot
# know -- the TEST_LEVEL scaling from bin/stream_levels.py, and the
# -Wno-MULTIDRIVEN the generated PeakRDL CSR needs to COMPILE.
#
# The tradeoff, stated plainly: CFG_PREFIXES in the test files no longer tracks
# a .toml change by itself. Edit the .toml, edit the test. bin/tests/
# test_bridge_dv_not_generated.py fails if this script starts writing there
# again.
#
# Why this exists:
#   - Both `make bitstream` (Vivado) and `make run` (cocotb) need the bridge
#     RTL on disk. Without an explicit regen step you end up debugging stale
#     RTL from the last person's machine.
#   - Hooking this into the Makefile chains means the bridge is always
#     consistent with the .toml config; no "did you remember to regenerate?"
#     surprises during board bringup.
#
# Usage:
#   ./regen_bridges.sh           # regenerate every bridge in configs/
#   ./regen_bridges.sh <name>    # regenerate just that one bridge
#                                # (looks for configs/<name>.toml)
#
# Requires REPO_ROOT in env (sourced from $REPO_ROOT/env_python).
# ==============================================================================

set -euo pipefail

if [ -z "${REPO_ROOT:-}" ]; then
    echo "ERROR: REPO_ROOT not set. source \$REPO_ROOT/env_python first."
    exit 1
fi

# Anchor everything off this script's location so cwd doesn't matter.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
FRAMEWORK_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
BRIDGES_DIR="$FRAMEWORK_ROOT/rtl/bridges"
CONFIGS_DIR="$BRIDGES_DIR/configs"
RTL_OUT="$BRIDGES_DIR/generated"

GENERATOR="$REPO_ROOT/projects/components/bridge/bin/bridge_generator.py"

if [ ! -x "$GENERATOR" ] && [ ! -f "$GENERATOR" ]; then
    echo "ERROR: bridge_generator.py not found at $GENERATOR"
    exit 1
fi

mkdir -p "$RTL_OUT"

# Pick the bridges to regen: arg overrides → just that one; otherwise all.
if [ "$#" -ge 1 ]; then
    requested="$1"
    config="$CONFIGS_DIR/${requested}.toml"
    if [ ! -f "$config" ]; then
        echo "ERROR: no config for '$requested' at $config"
        exit 1
    fi
    configs=("$config")
else
    mapfile -t configs < <(ls "$CONFIGS_DIR"/*.toml 2>/dev/null || true)
    if [ "${#configs[@]}" -eq 0 ]; then
        echo "ERROR: no .toml configs found under $CONFIGS_DIR"
        exit 1
    fi
fi

echo "================================================================================"
echo "Regenerating ${#configs[@]} bridge(s) under $BRIDGES_DIR"
echo "================================================================================"

for config in "${configs[@]}"; do
    name="$(basename "$config" .toml)"
    conn="$CONFIGS_DIR/${name}_connectivity.csv"

    if [ ! -f "$conn" ]; then
        echo "ERROR: no connectivity CSV next to $config (expected $conn)"
        exit 1
    fi

    echo ""
    echo "--- $name ---"
    python3 "$GENERATOR" \
        --ports "$config" \
        --connectivity "$conn" \
        --name "$name" \
        --output-dir "$RTL_OUT"
done

echo ""
echo "================================================================================"
echo "✅ All bridges regenerated."
echo "   RTL:    $RTL_OUT/<name>/"
echo "   Lists:  $BRIDGES_DIR/filelists/<name>.f"
echo "   (DV under $BRIDGES_DIR/dv/ is hand-maintained -- not written here.)"
echo "================================================================================"
