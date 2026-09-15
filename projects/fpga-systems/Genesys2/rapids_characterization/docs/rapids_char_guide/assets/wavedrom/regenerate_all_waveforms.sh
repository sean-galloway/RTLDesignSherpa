#!/bin/bash
#==============================================================================
# Regenerate all WaveDrom timing diagrams in this directory (.json -> .svg)
#==============================================================================
# Requires: wavedrom-cli (npm install -g wavedrom-cli).
#==============================================================================
set -u
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"
command -v wavedrom-cli >/dev/null || { echo "ERROR: wavedrom-cli not found (npm install -g wavedrom-cli)"; exit 1; }
fail=0
for json in *.json; do
    [[ -f "$json" ]] || continue
    svg="${json%.json}.svg"
    echo -n "Generating $svg ... "
    if wavedrom-cli -i "$json" -s "$svg" 2>/tmp/wavedrom_cdc_err.log; then
        echo "OK ($(stat -c%s "$svg") bytes)"
    else
        echo "FAILED"; head -5 /tmp/wavedrom_cdc_err.log; fail=1
    fi
done
exit $fail
