#!/usr/bin/env bash
# Program each of the four images in turn and measure its bandwidth.
#
# Pairs with build_image_matrix.sh: that one builds, this one measures. Both
# are scripted because the configuration that produced a number is part of the
# number, and last time it lived only in scrollback.
#
# Bandwidth is read as a SLOPE over two block counts. A single run's
# productive/window is (rate*B)/(rate*B + fill) and sits below the truth at
# every finite B -- on this design the same hardware reads 71.5 cycles/block at
# 16 blocks and 63.5 at 256. Differencing cancels the fill.
#
# AXI4 runs are capped at CFG_AXI4_MAX_BLOCKS = CFG_AXI4_MEM_DEPTH/CFG_N_BEATS
# = 65 blocks per kick, and the harness REFUSES a larger one rather than
# clamping it, so the AXI4 pair is 64/16 where AXIS can use 256/64.
#
# Needs the board. Run it detached so the harness cannot SIGTERM Vivado:
#   setsid nohup bin/measure_image_matrix.sh > /path/to/log 2>&1 &
set -u
cd "$(dirname "$0")/.." || exit 1
ROOT=$(pwd)
REPO=$(cd "$ROOT/../../../.." && pwd)
HOST=$ROOT/build-loop/host/host_rs_loop.py
OUT=$ROOT/stable/reports/bandwidth.txt
BOARD=nexys_a7_100t

: > "$OUT"
for cfg in "axis_ribm 256 64" "axis_euclid 256 64" \
           "axi4_ribm 64 16" "axi4_euclid 64 16"; do
    set -- $cfg
    name=$1; big=$2; small=$3
    bit=$ROOT/stable/reports/$name/rs_loop_$name.bit
    echo "=== $name at $(date -Is)" | tee -a "$OUT"
    if [ ! -f "$bit" ]; then
        echo "  no bitstream at $bit -- build it first" | tee -a "$OUT"; continue
    fi

    python3 "$REPO/projects/fpga-systems/bin/fpga_board.py" --board "$BOARD" \
        program --bitstream "$bit" > /tmp/prog_$name.log 2>&1
    rc=$?
    if [ $rc -ne 0 ]; then
        echo "  PROGRAM FAILED rc=$rc (see /tmp/prog_$name.log)" | tee -a "$OUT"; continue
    fi
    grep -q "identity: verified" /tmp/prog_$name.log \
        || echo "  WARNING: identity not verified" | tee -a "$OUT"

    # correctness first: a bandwidth number off a miscomputing design is noise
    timeout 600 python3 "$HOST" random 2>&1 | grep -E "^\[random\]|ALL PASS|FAIL" \
        | sed 's/^/  /' | tee -a "$OUT"
    timeout 600 python3 "$HOST" bw --blocks "$big" --small "$small" --slope 2>&1 \
        | grep -vE "^\[autodetect\]|^Connected" | sed 's/^/  /' | tee -a "$OUT"
    echo | tee -a "$OUT"
done
echo "=== done at $(date -Is)" | tee -a "$OUT"
