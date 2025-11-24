#!/bin/bash
# Regenerate all Graphviz diagrams from .gv and .dot source files as SVG
# This script converts Graphviz files to high-quality SVG vector graphics

set -e  # Exit on error

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

SVG_DIR="../svg"
mkdir -p "$SVG_DIR"

echo "======================================"
echo "Regenerating IOAPIC Graphviz SVG Diagrams"
echo "======================================"
echo

success_count=0
error_count=0

# Process .gv files
for gv in *.gv; do
    if [ ! -f "$gv" ]; then
        continue
    fi

    svg="${gv%.gv}.svg"
    echo -n "Generating $svg ... "

    # Generate SVG using dot
    if dot -Tsvg "$gv" -o "$SVG_DIR/$svg" 2>/tmp/dot_error.log; then
        echo "✓"
        success_count=$((success_count + 1))
    else
        echo "✗"
        echo "  Error details:"
        cat /tmp/dot_error.log | sed 's/^/    /'
        error_count=$((error_count + 1))
    fi
done

# Process .dot files
for dot_file in *.dot; do
    if [ ! -f "$dot_file" ]; then
        continue
    fi

    svg="${dot_file%.dot}.svg"
    echo -n "Generating $svg ... "

    # Generate SVG using dot
    if dot -Tsvg "$dot_file" -o "$SVG_DIR/$svg" 2>/tmp/dot_error.log; then
        echo "✓"
        success_count=$((success_count + 1))
    else
        echo "✗"
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
