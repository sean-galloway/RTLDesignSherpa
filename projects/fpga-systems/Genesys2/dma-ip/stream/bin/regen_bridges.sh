#!/bin/bash
# ==============================================================================
# regen_bridges.sh — regenerate every bridge owned by stream_char_framework
# ==============================================================================
#
# Walks $FRAMEWORK_ROOT/rtl/bridges/configs/*.toml and runs the bridge
# generator (projects/components/fabric-gen-ip/bridge/bin/bridge_generator.py) on each
# one, dropping outputs into:
#   $FRAMEWORK_ROOT/rtl/bridges/generated/<bridge>/   ← RTL package + adapters
#   $FRAMEWORK_ROOT/rtl/bridges/filelists/<bridge>.f  ← filelist (REPO_ROOT-anchored)
#
# RTL, filelists AND the DV collateral (TB classes + tests). Nothing under
# rtl/bridges/dv/ is hand-maintained: a fix there is a generator fix plus a
# regeneration. This area once kept those files by hand (after
# --generate-tests reverted hand fixes, 33ac787e / 90bca4c1 / bd79af49); by
# 2026-10-15 the hand copies had drifted from their own TOML and the
# generator, and everything they carried is a generator feature now.
# Fixing that limitation is bridge GitHub #119 L8;
# bin/tests/test_bridge_dv_is_generated.py holds that line.
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
TB_OUT="$BRIDGES_DIR/dv/tbclasses"
TEST_OUT="$BRIDGES_DIR/dv/tests"

# Serialise. RTL_OUT is FRAMEWORK-level -- every build-* under this area shares
# it -- and bridge_generator.py rmtree()s each bridge directory before rewriting
# it (bridge_generator.py:700). Two builds running this script at once delete
# each other's output mid-write:
#
#   FileNotFoundError: [Errno 2] No such file or directory:
#       .../rtl/bridges/generated/bridge_stream_mon_axil
#
# which is exactly how a concurrent `make bitstream` across build-mon, build-obs
# and build-perf killed the perf build (2026-09-19). It is a TOCTOU inside
# rmtree: the directory existed at the check and was gone by the unlink.
#
# fpga_flow.mk's existing lock cannot cover this. BUILD_LOCK is deliberately per
# BUILD DIRECTORY (fpga_flow.mk:82) so the three builds CAN run Vivado at the
# same time -- right for Vivado, useless for a writer all three share.
#
# BLOCKING, unlike the Vivado lock's `flock -n`. A second Vivado run on one
# project directory must abort; a second regen should just wait a few seconds
# and then find the same bytes, because regeneration is idempotent.
REGEN_LOCK="$BRIDGES_DIR/.regen.lock"     # *.lock is gitignored
if [ -z "${REGEN_LOCKED:-}" ]; then
    # `bash "$0"`, not `"$0"`: PREBUILD invokes this script as
    # `bash regen_bridges.sh ...`, so the exec bit is not load-bearing
    # anywhere else. Re-exec'ing it directly would quietly make every
    # stream build depend on a mode bit a fresh clone need not carry.
    exec env REGEN_LOCKED=1 flock "$REGEN_LOCK" bash "$0" "$@"
fi

GENERATOR="$REPO_ROOT/projects/components/fabric-gen-ip/bridge/bin/bridge_generator.py"

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
        --output-dir "$RTL_OUT" \
        --generate-tests \
        --output-tb "$TB_OUT" \
        --output-test "$TEST_OUT"
done

echo ""
echo "================================================================================"
echo "✅ All bridges regenerated."
echo "   RTL:    $RTL_OUT/<name>/"
echo "   Lists:  $BRIDGES_DIR/filelists/<name>.f"
echo "   DV:     $TB_OUT/<name>_tb.py, $TEST_OUT/test_<name>*.py"
echo "================================================================================"
