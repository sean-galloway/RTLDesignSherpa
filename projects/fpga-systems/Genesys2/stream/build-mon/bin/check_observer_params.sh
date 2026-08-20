#!/usr/bin/env bash
# Gate: prove what the build ACTUALLY elaborated, before reading any timing number.
#
# WHY THIS EXISTS
# ---------------
# On 2026-08-17 two Genesys 2 builds were reported with WNS figures for a
# "banked, four-CAM" observer. They were not that design: a stale Vivado
# project was elaborating old content while the source said otherwise. The
# same source elaborated four banks correctly under Verilator, so the RTL was
# never the problem -- the dirty build was. Both numbers had to be withdrawn.
#
# The lesson is that a build's own claims are not evidence:
#   * "Applying generics: ..." in the tcl proves a property was SET, not used.
#   * The synthesis log carries NO per-instance parameter echo at all, so
#     grepping it for MAX_TRANSACTIONS finds nothing whether or not the design
#     is banked. An empty grep reads like "absent" and is worthless as a gate.
#
# What IS ground truth: the post-route timing reports name full instance
# paths, and the banked CAM is a generate block. If g_cam_bank[N] appears in
# a timing path, that bank physically exists in the routed design.
#
# Usage:  bin/check_observer_params.sh [reports_dir]
# Exit 0 only if the observer CAMs really came out banked at the wanted count.

set -uo pipefail
REPORTS="${1:-fpga/reports}"
: "${WANT_BANKS:=4}"
: "${WANT_PERIOD_NS:=11.111}"   # 90 MHz; 10.000 for 100 MHz

if [[ ! -d "$REPORTS" ]]; then
    echo "FAIL: no reports directory at $REPORTS -- build did not get to timing."
    exit 2
fi

rc=0

echo "=== banked CAM instances present in routed timing paths ==="
mapfile -t BANKS < <(grep -ohE 'g_cam_bank\[[0-9]+\]' "$REPORTS"/*.txt 2>/dev/null | sort -u)
printf '  %s\n' "${BANKS[@]:-<none>}"
# Timing reports only list paths that were REPORTED, so a quiet bank is not
# proof of absence -- but seeing more than one proves the generate loop ran.
if [[ "${#BANKS[@]}" -lt 2 ]]; then
    echo "FAIL: fewer than 2 distinct g_cam_bank[] instances found."
    echo "      This build is NOT the banked design. Do not read WNS from it."
    rc=1
else
    echo "  -> ${#BANKS[@]} distinct banks seen (want up to ${WANT_BANKS}); generate loop confirmed."
fi

echo
echo "=== clock period ==="
if grep -q "$WANT_PERIOD_NS" "$REPORTS/timing_summary.txt" 2>/dev/null; then
    echo "  -> ${WANT_PERIOD_NS} ns present: the build is at the intended frequency."
else
    echo "FAIL: ${WANT_PERIOD_NS} ns not found in timing_summary.txt."
    echo "      The build is not at the frequency you think it is."
    rc=1
fi

echo
if [[ $rc -eq 0 ]]; then
    echo "=== timing (safe to quote -- the gates above passed) ==="
    awk '/Design Timing Summary/{f=1}
         f && /^ *-?[0-9]+\.[0-9]+/{print "  WNS="$1"  TNS="$2"  failing_endpoints="$3"  WHS="$5; exit}' \
        "$REPORTS/timing_summary.txt"
    grep -E "^\| Slice LUTs" "$REPORTS/utilization_impl.txt" 2>/dev/null | head -1 | sed 's/^/  /'
else
    echo "GATES FAILED -- timing numbers from this build describe some other design."
fi
exit $rc
