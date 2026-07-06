#!/usr/bin/env bash
# Open one of the stashed core_macro WAVES=1 dumps in gtkwave with the
# pre-built signal save (.gtkw).
#
# Usage:  ./open_ddr2_wave.sh {grid_bl4_n16 | grid_bl8_n16 | profile_burst_pause_n64}
set -e
CFG=${1:-grid_bl8_n16}
HERE=$(cd "$(dirname "$0")" && pwd)
DUMP=/tmp/ddr2_wave_dumps/${CFG}.fst
if [ ! -f "$DUMP" ]; then
    echo "ERROR: dump not found: $DUMP" >&2
    echo "Available:" >&2
    ls /tmp/ddr2_wave_dumps/ >&2
    exit 1
fi
exec gtkwave -a "$HERE/ddr2_lpddr2_core_macro.gtkw" "$DUMP"
