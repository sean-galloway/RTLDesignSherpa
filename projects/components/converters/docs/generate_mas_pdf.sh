#!/bin/bash
#
# Generate Converters MAS PDF from markdown sources
#
# Usage: ./generate_mas_pdf.sh
#

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../../../.." && pwd)"
MAS_DIR="$SCRIPT_DIR/converter_mas"
OUTPUT_DIR="$SCRIPT_DIR"

# Output files
DOCX_FILE="$OUTPUT_DIR/Converters_MAS_v1.0.docx"
PDF_FILE="$OUTPUT_DIR/Converters_MAS_v1.0.pdf"

echo "=== Generating Converters MAS Documentation ==="
echo "Source: $MAS_DIR"
echo "Output: $OUTPUT_DIR"
echo ""

# Check for md_to_docx.py
MD_TO_DOCX="$REPO_ROOT/bin/md_to_docx.py"
if [[ ! -f "$MD_TO_DOCX" ]]; then
    echo "ERROR: md_to_docx.py not found at $MD_TO_DOCX"
    exit 1
fi

# Check for styles file
STYLES_FILE="$MAS_DIR/converter_mas_styles.yaml"
if [[ ! -f "$STYLES_FILE" ]]; then
    echo "ERROR: Styles file not found: $STYLES_FILE"
    echo "Copy from: bridge/docs/bridge_has/bridge_has_styles.yaml"
    exit 1
fi

# Check for required logo (title page won't work without it)
ASSETS="$MAS_DIR/assets"
if [[ ! -f "$ASSETS/images/logo.png" ]]; then
    echo "ERROR: Logo not found: $ASSETS/images/logo.png"
    echo "Copy from: bridge/docs/bridge_has/assets/images/logo.png"
    exit 1
fi

# Generate DOCX and PDF
echo "Generating DOCX and PDF..."

python3 "$MD_TO_DOCX" \
    "$MAS_DIR/converter_mas_index.md" \
    "$DOCX_FILE" \
    --style "$STYLES_FILE" \
    --expand-index \
    --skip-index-content \
    --toc \
    --number-sections \
    --title-page \
    --pdf \
    --lof \
    --lot \
    --pagebreak \
    --narrow-margins \
    --pdf-engine=lualatex \
    --mainfont "Noto Serif" \
    --monofont "Noto Sans Mono" \
    --sansfont "Noto Sans" \
    --mathfont "Noto Serif" \
    --assets-dir "$ASSETS" \
    --assets-dir "$ASSETS/images" \
    --assets-dir "$ASSETS/mermaid" \
    --assets-dir "$ASSETS/wavedrom" \
    --quiet

if [[ ! -f "$DOCX_FILE" ]]; then
    echo "ERROR: DOCX generation failed"
    exit 1
fi
echo "Created: $DOCX_FILE"

if [[ -f "$PDF_FILE" ]]; then
    echo "Created: $PDF_FILE"
else
    echo "WARNING: PDF generation may have failed (check if xelatex is installed)"
fi

echo ""
echo "=== Generation Complete ==="
echo "Files:"
ls -la "$OUTPUT_DIR"/Converters_MAS_* 2>/dev/null || echo "  (no output files found)"
