#!/bin/bash
#==============================================================================
# Regenerate All APB Crossbar WaveDrom Timing Diagrams
#==============================================================================
# Purpose: Convert .json WaveDrom files to .svg
# Method: Use wavedrom-cli for SVG generation
# Requirements: wavedrom-cli installed (npm install -g wavedrom-cli)
# Output: SVG format for crisp vector graphics in PDF generation
#==============================================================================

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

cd "$SCRIPT_DIR"

echo "=========================================="
echo " APB Crossbar WaveDrom Regeneration"
echo "=========================================="

# Check if wavedrom-cli is installed
if ! command -v wavedrom-cli &> /dev/null; then
    echo "ERROR: wavedrom-cli not found!"
    echo "Install with: npm install -g wavedrom-cli"
    exit 1
fi

echo "Using: wavedrom-cli"
echo "Directory: $SCRIPT_DIR"
echo ""

SUCCESS=0
FAIL=0

for json in *.json; do
    # Skip if no .json files exist
    if [[ ! -f "$json" ]]; then
        continue
    fi

    svg="${json%.json}.svg"

    echo -n "Generating $svg ... "

    # Generate SVG using wavedrom-cli
    if wavedrom-cli -i "$json" -s "$svg" 2>/tmp/wavedrom_error.log; then
        if [[ -f "$svg" ]]; then
            file_size=$(stat --format=%s "$svg" 2>/dev/null)
            echo "OK (${file_size} bytes)"
            ((SUCCESS++))
        else
            echo "FAILED (no output file)"
            cat /tmp/wavedrom_error.log | head -5
            ((FAIL++))
        fi
    else
        echo "FAILED (wavedrom-cli error)"
        cat /tmp/wavedrom_error.log | head -5
        ((FAIL++))
    fi
done

echo ""
echo "=========================================="
echo " Generation Complete"
echo "=========================================="
echo "Success: $SUCCESS"
echo "Failed:  $FAIL"
echo ""
echo "SVG files in directory:"
ls -1 *.svg 2>/dev/null | wc -l
echo ""

if [[ $FAIL -gt 0 ]]; then
    echo "WARNING: Some waveforms failed to generate!"
    exit 1
else
    echo "All waveforms generated successfully!"
    exit 0
fi
