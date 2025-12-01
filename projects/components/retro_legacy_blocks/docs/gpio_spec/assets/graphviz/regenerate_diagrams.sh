#!/bin/bash
# Regenerate all Graphviz diagrams from .gv source files as SVG
# This script converts Graphviz files to high-quality SVG vector graphics

set -e  # Exit on error

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

SVG_DIR="../svg"
mkdir -p "$SVG_DIR"

echo "======================================"
echo "Regenerating GPIO Graphviz SVG Diagrams"
echo "======================================"
echo

success_count=0
error_count=0

# Process .gv and .dot files
for gv in *.gv *.dot; do
    if [ ! -f "$gv" ]; then
        continue
    fi

    # Extract base name and generate SVG filename
    base="${gv%.*}"
    svg="${base}.svg"
    echo -n "Generating $svg ... "

    # Generate SVG using dot
    if dot -Tsvg "$gv" -o "$SVG_DIR/$svg" 2>/tmp/dot_error.log; then
        echo "done"
        success_count=$((success_count + 1))
    else
        echo "FAILED"
        echo "  Error details:"
        cat /tmp/dot_error.log | sed 's/^/    /'
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
