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
# Two modes, because this script runs as the board flow's PREBUILD and the
# bridge generator is under active development:
#
#   --check   regenerate into a temp dir and DIFF against the committed output.
#             Reports drift and exits nonzero; touches nothing. This is what the
#             board build runs, so a build is reproducible from the tree and
#             does NOT silently absorb whatever the bridge generator became
#             today. Staleness still cannot rot unnoticed -- it fails loudly at
#             prebuild instead of mid-synthesis, which was the original point.
#
#   (default) regenerate in place, the deliberate act of taking a new bridge.
#
# Usage:
#   source $REPO_ROOT/env_python
#   ./regen_bridges.sh              # regenerate every config, in place
#   ./regen_bridges.sh <name>       # regenerate just <name>.toml
#   ./regen_bridges.sh --check      # verify only; no writes, nonzero on drift

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

CHECK_ONLY=0
if [ "${1:-}" = "--check" ]; then
    CHECK_ONLY=1
    shift
fi

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

if [ "$CHECK_ONLY" = "1" ]; then
    # Regenerate into a scratch tree and compare. RTL_OUT is repointed for the
    # whole loop so every step below -- generation, the subtractive uniquifier,
    # the filelist -- runs exactly as it would in place, and the comparison is
    # therefore of like with like.
    CHECK_DIR="$(mktemp -d)"
    trap 'rm -rf "$CHECK_DIR"' EXIT
    COMMITTED_OUT="$RTL_OUT"
    # The generator writes its filelist to <output-dir>/../filelists, so the
    # scratch output has to sit one level down -- otherwise the filelist lands
    # in the temp dir's PARENT, which is /tmp, and is never cleaned up.
    RTL_OUT="$CHECK_DIR/generated"
    mkdir -p "$RTL_OUT"
fi

echo "================================================================================"
if [ "$CHECK_ONLY" = "1" ]; then
    echo "Checking ${#configs[@]} bridge(s) under $BRIDGES_DIR against their configs"
else
    echo "Regenerating ${#configs[@]} bridge(s) under $BRIDGES_DIR"
fi
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

    # The shared bridge_generator emits the subtractive catch-all as a module
    # named plainly `subtractive_adapter` for EVERY bridge. This flow flattens
    # three bridges (axil/wr/rd) into one filelist, so three same-named modules
    # with different interfaces collide -- Vivado binds them all to whichever it
    # elaborates first and the AR ports of the write-only variant vanish. Make
    # the module (and its instantiation) unique per bridge here, in the flow
    # that combines them, rather than in the shared generator (which would force
    # a repo-wide regen of every bridge). Filename is unchanged, so the filelist
    # entry still resolves. See <shared-generator collision, to be filed>.
    sub="$RTL_OUT/$name/subtractive_adapter.sv"
    if [ -f "$sub" ]; then
        sed -i "s/\bsubtractive_adapter\b/${name}_subtractive_adapter/g" \
            "$RTL_OUT/$name"/*.sv
        echo "    uniquified subtractive_adapter -> ${name}_subtractive_adapter"
    fi
done

if [ "$CHECK_ONLY" = "1" ]; then
    echo ""
    echo "================================================================================"
    drift=0
    for config in "${configs[@]}"; do
        name="$(basename "$config" .toml)"
        # Only the .sv matters to the build. The copied .toml/.csv carry
        # absolute paths that differ between the real tree and the scratch one
        # and say nothing about whether the RTL moved. (diff excludes with -x;
        # --include is a grep flag and is not one here.)
        if ! diff -rq -x '*.toml' -x '*.csv' -x '*.f' \
                "$COMMITTED_OUT/$name" "$RTL_OUT/$name" >/dev/null 2>&1; then
            drift=1
            echo "DRIFT: $name"
            diff -rq -x '*.toml' -x '*.csv' -x '*.f' \
                "$COMMITTED_OUT/$name" "$RTL_OUT/$name" 2>&1 | sed 's/^/    /'
        fi
    done
    if [ "$drift" = "1" ]; then
        echo ""
        echo "The committed bridge RTL no longer matches what the generator emits."
        echo "The board build uses the COMMITTED RTL, so it is reproducible -- but"
        echo "it is now behind the generator. Take the new bridge deliberately:"
        echo ""
        echo "    bash $0"
        echo ""
        echo "then re-run the build. (REGEN_BRIDGES=1 make bitstream does both.)"
        echo "================================================================================"
        exit 1
    fi
    echo "All bridges match their configs."
    echo "================================================================================"
    exit 0
fi

echo ""
echo "================================================================================"
echo "All bridges regenerated."
echo "   RTL:   $RTL_OUT/<name>/"
echo "   Lists: $BRIDGES_DIR/filelists/<name>.f"
echo "================================================================================"
