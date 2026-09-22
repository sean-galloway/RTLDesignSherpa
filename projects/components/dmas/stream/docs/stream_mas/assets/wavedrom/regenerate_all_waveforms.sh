#!/bin/bash
#==============================================================================
# Regenerate all WaveDrom timing diagrams in this directory (.json -> .png)
#==============================================================================
# Requires: wavedrom-cli (npm install -g wavedrom-cli) and rsvg-convert
#           (apt install librsvg2-bin).
#
# The .svg is an INTERMEDIATE ONLY. Markdown must reference the .png -- see
# vault/handbook/authoring/doc-pipeline.md. An earlier version of this script
# stopped at .svg, which is how a book ends up with image refs the PDF
# pipeline cannot resolve. Do not remove the conversion step.
#
# rsvg-convert, NOT inkscape: the snap build of inkscape resolves relative
# paths against $HOME, fails to find the input, and EXITS 0 HAVING WRITTEN
# NOTHING -- so a `set -e` or a check=True cannot catch it.
#==============================================================================
set -u
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"
command -v wavedrom-cli >/dev/null || { echo "ERROR: wavedrom-cli not found (npm install -g wavedrom-cli)"; exit 1; }
command -v rsvg-convert >/dev/null || { echo "ERROR: rsvg-convert not found (apt install librsvg2-bin)"; exit 1; }

# 2x the SVG's own declared width: wavedrom emits at CSS pixel scale, and the
# PDF pipeline assumes 96 px/in, so 1x is soft once fitted to a page.
SCALE="${SCALE:-2}"

fail=0
for json in *.json; do
    [[ -f "$json" ]] || continue
    base="${json%.json}"; svg="$base.svg"; png="$base.png"
    echo -n "Generating $png ... "
    if ! wavedrom-cli -i "$json" -s "$svg" 2>/tmp/wavedrom_err.log; then
        echo "FAILED (wavedrom-cli)"; head -5 /tmp/wavedrom_err.log; fail=1; continue
    fi
    nat=$(grep -o 'width="[0-9]*"' "$svg" | head -1 | tr -dc 0-9)
    [[ -n "$nat" ]] || { echo "FAILED (no width in svg)"; fail=1; continue; }
    if ! rsvg-convert -w $((nat * SCALE)) -o "$png" "$svg" 2>/tmp/rsvg_err.log; then
        echo "FAILED (rsvg-convert)"; head -5 /tmp/rsvg_err.log; fail=1; continue
    fi
    # Palette-encode: these are flat line art, so 64 colours is visually
    # identical and roughly a third of the bytes.
    command -v convert >/dev/null && convert "$png" -colors 64 PNG8:"$png"
    echo "OK ($(stat -c%s "$png") bytes, $(identify -format '%wx%h' "$png" 2>/dev/null))"
done
exit $fail
