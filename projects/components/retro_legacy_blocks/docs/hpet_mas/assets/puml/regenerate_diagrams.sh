#!/bin/bash
# Regenerate all PlantUML diagrams from .puml source files as SVG
# This script converts PlantUML files to high-quality SVG vector graphics

set -e  # Exit on error

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

SVG_DIR="../svg"
mkdir -p "$SVG_DIR"

echo "======================================"
echo "Regenerating HPET PlantUML SVG Diagrams"
echo "======================================"
echo

success_count=0
error_count=0

# Process .puml files
for puml in *.puml; do
    if [ ! -f "$puml" ]; then
        continue
    fi

    svg="${puml%.puml}.svg"
    echo -n "Generating $svg ... "

    # Generate SVG using plantuml
    if plantuml -tsvg "$puml" 2>/tmp/plantuml_error.log; then
        # Move to svg directory
        mv "$svg" "$SVG_DIR/" 2>/dev/null || true
        echo "✓"
        success_count=$((success_count + 1))
    else
        echo "✗"
        echo "  Error details:"
        cat /tmp/plantuml_error.log | sed 's/^/    /'
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
