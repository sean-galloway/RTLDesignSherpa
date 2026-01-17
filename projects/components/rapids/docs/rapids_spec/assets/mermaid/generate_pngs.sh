#!/usr/bin/env bash
# ------------------------------------------------------------
# Generate PNG images from Mermaid diagram files
# ------------------------------------------------------------
# This script requires mmdc (mermaid-cli) and a display (X11/Wayland)
# Install: npm install -g @mermaid-js/mermaid-cli
#
# Usage: ./generate_pngs.sh
# ------------------------------------------------------------

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "${SCRIPT_DIR}"

echo "Generating Mermaid PNGs..."

for f in *.mmd; do
    if [[ -f "$f" ]]; then
        png_file="${f%.mmd}.png"
        echo "  ${f} -> ${png_file}"
        mmdc -i "$f" -o "${png_file}" -b transparent -w 1200 2>/dev/null || {
            echo "    Warning: Failed to generate ${png_file} (mmdc requires display)"
        }
    fi
done

echo ""
echo "Generated files:"
ls -la *.png 2>/dev/null || echo "  No PNG files found"
