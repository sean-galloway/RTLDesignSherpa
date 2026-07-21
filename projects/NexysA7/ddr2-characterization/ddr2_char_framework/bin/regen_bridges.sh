#!/usr/bin/env bash
#
# Regenerate the DDR2 characterization bridges from their TOML configs.
#
# CRITICAL RULE #0: the bridge RTL *and* its filelist are generated. Never
# hand-edit anything under rtl/bridges/generated/ or rtl/bridges/filelists/ --
# edit the config in rtl/bridges/configs/ and re-run this script. Hand edits are
# silently destroyed on the next regeneration.
#
# This mirrors stream_char_framework/bin/regen_bridges.sh. It deliberately does
# NOT pass --generate-tests: the DDR2 bridge has no dv/ tree, and the DDR2 flow
# exercises the bridge through the UART harness rather than per-bridge cocotb
# tests. Add --generate-tests (plus --output-tb/--output-test) if that changes.
#
# Usage:
#   source $REPO_ROOT/env_python
#   ./regen_bridges.sh              # regenerate every config
#   ./regen_bridges.sh <name>       # regenerate just <name>.toml

set -euo pipefail

if [ -z "${REPO_ROOT:-}" ]; then
    echo "ERROR: REPO_ROOT not set. source \$REPO_ROOT/env_python first."
    exit 1
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
FRAMEWORK_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
BRIDGES_DIR="$FRAMEWORK_ROOT/rtl/bridges"
CONFIGS_DIR="$BRIDGES_DIR/configs"
RTL_OUT="$BRIDGES_DIR/generated"

GENERATOR="$REPO_ROOT/projects/components/bridge/bin/bridge_generator.py"
if [ ! -f "$GENERATOR" ]; then
    echo "ERROR: bridge_generator.py not found at $GENERATOR"
    exit 1
fi

mkdir -p "$RTL_OUT"

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
echo "All bridges regenerated."
echo "   RTL:   $RTL_OUT/<name>/"
echo "   Lists: $BRIDGES_DIR/filelists/<name>.f"
echo "================================================================================"
