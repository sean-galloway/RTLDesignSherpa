#!/bin/bash
# Regenerate all WaveDrom waveforms from .json source files as SVG
# This script converts WaveDrom JSON to high-quality SVG vector graphics

set -e  # Exit on error

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

SVG_DIR="../svg"
mkdir -p "$SVG_DIR"

echo "======================================"
echo "Regenerating HPET WaveDrom SVG Waveforms"
echo "======================================"
echo

success_count=0
error_count=0

# Process .json files
for json in *.json; do
    if [ ! -f "$json" ]; then
        continue
    fi

    svg="${json%.json}.svg"
    echo -n "Generating $svg ... "

    # Generate SVG using wavedrom-cli
    if wavedrom-cli -i "$json" -s "$SVG_DIR/$svg" 2>/tmp/wavedrom_error.log; then
        echo "✓"
        success_count=$((success_count + 1))
    else
        echo "✗"
        echo "  Error details:"
        cat /tmp/wavedrom_error.log | sed 's/^/    /'
        error_count=$((error_count + 1))
    fi
done

echo
echo "======================================"
echo "Summary:"
echo "  Success: $success_count"
echo "  Errors:  $error_count"
echo "======================================"

if [ $error_count -eq 0 ]; then
    exit 0
else
    exit 1
fi
