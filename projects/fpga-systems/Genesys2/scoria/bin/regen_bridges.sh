#!/usr/bin/env bash
# SPDX-License-Identifier: MIT
# Regenerate (or CHECK) the scoria char harness's generated AXIL config bridge.
#
# The DDR3 sibling of pumice's ddr2_char_framework/bin/regen_bridges.sh, and it
# exists for the same reason: the bridge adapters instantiate the converters
# component, and twice in one week a converters-side interface change left
# pumice's checked-in generated RTL stale, surfacing as a mid-build compile
# error instead of at regen time.
#
#   ./regen_bridges.sh            regenerate every .toml under rtl/bridges/configs
#   ./regen_bridges.sh <name>     regenerate just <name>.toml
#   ./regen_bridges.sh --check    report drift and exit nonzero; touch nothing
#
# CHECK is what the board build runs as its PREBUILD, and the default is check
# rather than regenerate for pumice's reason, which is worth repeating: the
# bridge generator is under active development, and regenerating in a prebuild
# means the board design silently absorbs whatever the generator became that
# day. Between pumice's last 75 MHz close and 2026-09-13 three generator
# changes landed and its config bridge grew ~650 flops with nobody asking.
# A board build has to be reproducible from the tree to be worth measuring.
# Drift still fails loudly; it just no longer rewrites the design underneath you.
#
#   source $REPO_ROOT/env_python   first -- the generator needs the venv.
set -euo pipefail

if [ -z "${REPO_ROOT:-}" ]; then
    REPO_ROOT="$(git rev-parse --show-toplevel 2>/dev/null || true)"
    [ -n "$REPO_ROOT" ] || { echo "ERROR: REPO_ROOT not set and not in a git tree"; exit 1; }
fi
export REPO_ROOT

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BRIDGES_DIR="$HERE/../rtl/bridges"
CONFIGS_DIR="$BRIDGES_DIR/configs"
RTL_OUT="$BRIDGES_DIR/generated"
GENERATOR="$REPO_ROOT/projects/components/fabric-gen-ip/bridge/bin/bridge_generator.py"

[ -f "$GENERATOR" ] || { echo "ERROR: bridge_generator.py not found at $GENERATOR"; exit 1; }

CHECK_ONLY=0
requested=""
for a in "$@"; do
    case "$a" in
        --check) CHECK_ONLY=1 ;;
        -*)      echo "ERROR: unknown flag $a"; exit 1 ;;
        *)       requested="$a" ;;
    esac
done

if [ -n "$requested" ]; then
    config="$CONFIGS_DIR/${requested}.toml"
    [ -f "$config" ] || { echo "ERROR: no such config $config"; exit 1; }
    configs=("$config")
else
    mapfile -t configs < <(ls "$CONFIGS_DIR"/*.toml 2>/dev/null || true)
    [ "${#configs[@]}" -gt 0 ] || { echo "ERROR: no .toml configs under $CONFIGS_DIR"; exit 1; }
fi

if [ "$CHECK_ONLY" = "1" ]; then
    # Regenerate into a scratch tree and compare. RTL_OUT is repointed for the
    # whole loop so generation, the uniquifier and the filelist all run exactly
    # as they would in place -- the comparison is of like with like.
    CHECK_DIR="$(mktemp -d)"; trap 'rm -rf "$CHECK_DIR"' EXIT
    COMMITTED_OUT="$RTL_OUT"
    # The generator writes its filelist to <output-dir>/../filelists, so the
    # scratch output must sit one level down or the filelist lands in /tmp and
    # is never cleaned up.
    RTL_OUT="$CHECK_DIR/generated"; mkdir -p "$RTL_OUT"
fi

echo "================================================================================"
[ "$CHECK_ONLY" = "1" ] \
  && echo "Checking ${#configs[@]} bridge(s) under $BRIDGES_DIR against their configs" \
  || echo "Regenerating ${#configs[@]} bridge(s) under $BRIDGES_DIR"
echo "================================================================================"

for config in "${configs[@]}"; do
    name="$(basename "$config" .toml)"
    conn="$CONFIGS_DIR/${name}_connectivity.csv"
    [ -f "$conn" ] || { echo "ERROR: no connectivity CSV next to $config (expected $conn)"; exit 1; }
    echo ""; echo "--- $name ---"
    python3 "$GENERATOR" --ports "$config" --connectivity "$conn" \
        --name "$name" --output-dir "$RTL_OUT"

    # The shared generator names the subtractive catch-all plainly
    # `subtractive_adapter` for EVERY bridge. scoria has ONE bridge today, so
    # nothing collides -- but pumice's flow flattens three into one filelist and
    # three same-named modules with different interfaces made Vivado bind them
    # all to whichever it elaborated first, silently losing the AR ports of the
    # write-only variant. Uniquifying here is free and makes a second scoria
    # bridge a non-event rather than a debugging session.
    if [ -f "$RTL_OUT/$name/subtractive_adapter.sv" ]; then
        sed -i "s/\bsubtractive_adapter\b/${name}_subtractive_adapter/g" \
            "$RTL_OUT/$name"/*.sv
        echo "    uniquified subtractive_adapter -> ${name}_subtractive_adapter"
    fi
done

if [ "$CHECK_ONLY" = "1" ]; then
    echo ""; echo "================================================================================"
    drift=0
    for config in "${configs[@]}"; do
        name="$(basename "$config" .toml)"
        # Only the .sv matters to the build. The copied .toml/.csv carry absolute
        # paths that differ between the real tree and the scratch one and say
        # nothing about whether the RTL moved.
        if ! diff -rq -x '*.toml' -x '*.csv' -x '*.f' \
                "$COMMITTED_OUT/$name" "$RTL_OUT/$name" >/dev/null 2>&1; then
            drift=1; echo "DRIFT: $name"
            diff -rq -x '*.toml' -x '*.csv' -x '*.f' \
                "$COMMITTED_OUT/$name" "$RTL_OUT/$name" 2>&1 | sed 's/^/    /'
        fi
    done
    if [ "$drift" = "1" ]; then
        cat <<MSG

The committed bridge RTL no longer matches what the generator emits.
The board build uses the COMMITTED RTL, so it is reproducible -- but it is now
behind the generator. Take the new bridge deliberately:

    bash $0

then re-run the build. (REGEN_BRIDGES=1 make bitstream does both.)
================================================================================
MSG
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
