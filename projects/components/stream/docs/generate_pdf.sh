#!/bin/bash
# Generate STREAM Specification PDF
# This script should be run from the docs directory

REPO_ROOT="../../../.."
SPEC_INDEX="stream_spec/stream_index.md"
OUTPUT_FILE="STREAM_Specification_v0.90.docx"

echo "Generating STREAM Specification PDF..."
echo "  Input: $SPEC_INDEX"
echo "  Output: $OUTPUT_FILE (and .pdf)"

cd "$(dirname "$0")"

python "$REPO_ROOT/bin/md_to_docx.py" \
    "$SPEC_INDEX" \
    "$OUTPUT_FILE" \
    --toc \
    --title-page \
    --pdf

if [ $? -eq 0 ]; then
    echo "✓ PDF generated successfully!"
    echo "  Files created:"
    echo "    - $OUTPUT_FILE"
    echo "    - ${OUTPUT_FILE%.docx}.pdf"
else
    echo "✗ PDF generation failed"
    exit 1
fi
