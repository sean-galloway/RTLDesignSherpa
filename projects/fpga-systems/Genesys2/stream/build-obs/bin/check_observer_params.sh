#!/usr/bin/env bash
# Gate: prove what the build ACTUALLY contains, before quoting any timing number.
#
# WHY THIS EXISTS
# ---------------
# 2026-08-17: two Genesys 2 builds were reported with WNS figures for a
# "banked, four-CAM" observer. They were not that design -- a stale Vivado
# project was elaborating old content. Both numbers had to be withdrawn.
#
# WHAT DOES *NOT* WORK AS EVIDENCE, all learned the hard way:
#
#   * The synthesis log carries NO per-instance parameter echo. Grepping it for
#     MAX_TRANSACTIONS finds nothing whether or not the design is banked, and an
#     empty grep reads like "absent".
#   * "Applying generics: ..." proves a property was SET, not that it was USED.
#   * Instance paths in the TIMING REPORTS are a partial signal: the reports
#     only list paths that were reported. A correct four-bank build showed
#     banks {0,1,3} in one run and {0} in another -- bank 2 has never appeared
#     in any report. An earlier version of this script hard-failed on that and
#     declared a perfectly good 8-channel build "NOT the banked design".
#   * get_cells -hier on a routed OR post-synth checkpoint cannot see purely
#     combinational blocks: synthesis inlines them and the generate-block path
#     disappears. axi_monitor_reporter_{error,timeout,compl} have zero
#     always_ff, so they are invisible this way -- which produced two separate
#     false "the error cone is missing" conclusions.
#
# WHAT DOES WORK: Verilator's elaboration dump. It reflects the design AFTER
# parameter resolution and generate evaluation but BEFORE any optimization, so
# generate arms and combinational instances are all still there. Run it with
# the SAME generics as the bitstream and it answers "what did this config
# actually build" exactly.
#
# Usage: bin/check_observer_params.sh [reports_dir]
#   env: NCH, FLAVOR, WANT_BANKS, WANT_PERIOD_NS

set -uo pipefail
REPORTS="${1:-fpga/reports}"
: "${NCH:=8}"
: "${FLAVOR:=2}"
: "${WANT_BANKS:=4}"
: "${WANT_PERIOD_NS:=11.111}"

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
REPO="$(cd "$HERE/../../../../.." && pwd)"
export REPO_ROOT="$REPO"
export FRAMEWORK_ROOT="$REPO/projects/fpga-systems/Genesys2/stream"
export STREAM_CHAR_FRAMEWORK_ROOT="$FRAMEWORK_ROOT"
export STREAM_CHAR_ROOT="$FRAMEWORK_ROOT"
export STREAM_ROOT="$REPO/projects/components/dmas/stream"
export CONVERTERS_ROOT="$REPO/projects/components/converters"
export MISC_ROOT="$REPO/projects/components/misc"

rc=0
XML="$(mktemp -d)/elab.xml"

echo "=== elaborating NUM_CHANNELS=$NCH MON_ERROR_FLAVOR=$FLAVOR ==="
if ! verilator --xml-only -Wno-fatal --top-module stream_genesys2_top \
        -GNUM_CHANNELS="$NCH" -GMON_ERROR_FLAVOR="$FLAVOR" \
        --xml-output "$XML" \
        -f "$FRAMEWORK_ROOT/rtl/filelists/stream_genesys2_top.f" >/dev/null 2>&1; then
    echo "FAIL: elaboration failed -- cannot verify build content."
    exit 2
fi

BANKS=$(grep -oE 'g_cam_bank\[[0-9]+\]' "$XML" | sort -u | wc -l)
ERRC=$(grep -cE '<cell [^>]*axi_monitor_reporter_error' "$XML")
echo "  CAM banks : $BANKS (want $WANT_BANKS)"
echo "  error cone: $ERRC instance(s)"

[[ "$BANKS" -eq "$WANT_BANKS" ]] || { echo "FAIL: expected $WANT_BANKS CAM banks."; rc=1; }
if [[ "$FLAVOR" == "2" || "$FLAVOR" == "1" ]]; then
    [[ "$ERRC" -ge 1 ]] || { echo "FAIL: flavor $FLAVOR must contain the error cone."; rc=1; }
else
    [[ "$ERRC" -eq 0 ]] || { echo "FAIL: flavor 0 must NOT contain the error cone."; rc=1; }
fi

echo
echo "=== clock period ==="
if grep -q "$WANT_PERIOD_NS" "$REPORTS/timing_summary.txt" 2>/dev/null; then
    echo "  ${WANT_PERIOD_NS} ns present: build is at the intended frequency."
else
    echo "FAIL: ${WANT_PERIOD_NS} ns not found in $REPORTS/timing_summary.txt."
    rc=1
fi

echo
if [[ $rc -eq 0 ]]; then
    echo "=== timing + utilization (gates passed -- safe to quote) ==="
    awk '/Design Timing Summary/{f=1}
         f && /^ *-?[0-9]+\.[0-9]+/{print "  WNS="$1"  TNS="$2"  failing_endpoints="$3"  WHS="$5; exit}' \
        "$REPORTS/timing_summary.txt"
    grep -E "^\| Slice LUTs " "$REPORTS/utilization_impl.txt" 2>/dev/null | sed 's/^/  /'
else
    echo "GATES FAILED -- do not quote timing from this build."
fi
exit $rc
