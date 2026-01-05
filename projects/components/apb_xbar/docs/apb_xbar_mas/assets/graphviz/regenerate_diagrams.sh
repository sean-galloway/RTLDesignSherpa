#!/bin/bash
#==============================================================================
# Regenerate All APB Crossbar Graphviz Diagrams
#==============================================================================
# Purpose: Convert .gv (Graphviz) files to .svg
# Method: Use dot command from graphviz package
# Requirements: graphviz installed (apt-get install graphviz)
# Output: SVG format for crisp vector graphics in PDF generation
#==============================================================================

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SVG_DIR="$SCRIPT_DIR/../svg"

cd "$SCRIPT_DIR"

echo "=========================================="
echo " APB Crossbar Graphviz Regeneration"
echo "=========================================="

# Check if dot is installed
if ! command -v dot &> /dev/null; then
    echo "ERROR: dot (graphviz) not found!"
    echo "Install with: sudo apt-get install graphviz"
    exit 1
fi

echo "Using: dot (graphviz) $(dot -V 2>&1 | head -1)"
echo "Source: $SCRIPT_DIR"
echo "Output: $SVG_DIR"
echo ""

SUCCESS=0
FAIL=0

for gv in *.gv; do
    # Skip if no .gv files exist
    if [[ ! -f "$gv" ]]; then
        continue
    fi

    svg="${gv%.gv}.svg"
    output_path="$SVG_DIR/$svg"

    echo -n "Generating $svg ... "

    # Generate SVG using dot
    if dot -Tsvg "$gv" -o "$output_path" 2>/tmp/dot_error.log; then
        if [[ -f "$output_path" ]]; then
            file_size=$(stat --format=%s "$output_path" 2>/dev/null)
            echo "OK (${file_size} bytes)"
            ((SUCCESS++))
        else
            echo "FAILED (no output file)"
            cat /tmp/dot_error.log | head -5
            ((FAIL++))
        fi
    else
        echo "FAILED (dot error)"
        cat /tmp/dot_error.log | head -5
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
echo "SVG files in $SVG_DIR:"
ls -1 "$SVG_DIR"/*.svg 2>/dev/null | wc -l
echo ""

if [[ $FAIL -gt 0 ]]; then
    echo "WARNING: Some diagrams failed to generate!"
    exit 1
else
    echo "All diagrams generated successfully!"
    exit 0
fi
