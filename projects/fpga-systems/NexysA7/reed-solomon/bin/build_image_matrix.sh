#!/usr/bin/env bash
# Build the four board images -- datapath (AXIS|AXI4) x solver (RIBM|EUCLID).
#
# ONE SOLVER PER BITSTREAM. Both solvers in one image is a different design:
# it doubles the key-equation area and the comparator changes the handshake
# the meters measure. RS_ENABLE_COMPARE=0 everywhere for that reason.
#
# Serial on purpose -- all four share build-loop/fpga/, so parallel runs would
# overwrite each other's project and reports. Run it detached:
#   setsid nohup bin/build_image_matrix.sh > /path/to/log 2>&1 &
# (the harness SIGTERMs backgrounded children; setsid is what survives it)
set -u
cd "$(dirname "$0")/.." || exit 1
ROOT=$(pwd)
BUILD=$ROOT/build-loop
OUT=$ROOT/stable/reports
SUMMARY=$OUT/matrix_summary.txt

: > "$SUMMARY"
printf '%-14s %10s %8s %10s %8s %s\n' image WNS endpoints LUTs BRAM status >> "$SUMMARY"

for cfg in "axis_ribm AXIS RIBM" "axis_euclid AXIS EUCLID" \
           "axi4_ribm AXI4 RIBM" "axi4_euclid AXI4 EUCLID"; do
    set -- $cfg
    name=$1; iface=$2; algo=$3
    echo "=== building $name (IFACE=$iface KES_ALGO_A=$algo) at $(date -Is)"
    ( cd "$BUILD" && RS_IFACE=$iface RS_KES_ALGO_A=$algo RS_ENABLE_COMPARE=0 \
        RS_IMPL_EFFORT=explore make bitstream ) > "$BUILD/build_$name.log" 2>&1
    rc=$?

    dst=$OUT/$name
    mkdir -p "$dst"
    cp -f "$BUILD"/fpga/reports/* "$dst"/ 2>/dev/null
    cp -f "$BUILD/build_$name.log" "$dst"/ 2>/dev/null
    [ -f "$BUILD/fpga/bitstream/rs_loop.bit" ] && \
        cp -f "$BUILD/fpga/bitstream/rs_loop.bit" "$dst/rs_loop_$name.bit"

    ts=$dst/timing_summary.txt
    ut=$dst/utilization_impl.txt
    wns=$(awk '/^ *-?[0-9]+\.[0-9]+ /{print $1; exit}' "$ts" 2>/dev/null)
    eps=$(awk '/^ *-?[0-9]+\.[0-9]+ /{print $3; exit}' "$ts" 2>/dev/null)
    luts=$(awk -F'|' '/Slice LUTs/{gsub(/ /,"",$3); print $3; exit}' "$ut" 2>/dev/null)
    bram=$(awk -F'|' '/Block RAM Tile/{gsub(/ /,"",$3); print $3; exit}' "$ut" 2>/dev/null)
    printf '%-14s %10s %8s %10s %8s rc=%s\n' \
        "$name" "${wns:-?}" "${eps:-?}" "${luts:-?}" "${bram:-?}" "$rc" >> "$SUMMARY"
    echo "=== $name done rc=$rc WNS=${wns:-?} LUTs=${luts:-?} at $(date -Is)"
done

echo "=== matrix complete at $(date -Is)"
cat "$SUMMARY"
