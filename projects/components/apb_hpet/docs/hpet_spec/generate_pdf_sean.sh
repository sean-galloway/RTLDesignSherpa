#!/bin/bash
# Generate HPET Specification PDF
# This script should be run from the docs directory


SPEC_INDEX="hpet_index.md"
OUTPUT_FILE="HPET_Specification_v0.25.docx"

echo "Generating HPET Specification PDF..."
echo "  Input: $SPEC_INDEX"
echo "  Output: $OUTPUT_FILE (and .pdf)"

cd "$(dirname "$0")"

python3 "$REPO_ROOT/bin/md_to_docx.py" \
    "$SPEC_INDEX" \
    -o "$OUTPUT_FILE" \
    --pdf

if [ $? -eq 0 ]; then
    echo "SUCCESS: PDF generated successfully!"
    echo "  Files created:"
    echo "    - $OUTPUT_FILE"
    echo "    - ${OUTPUT_FILE%.docx}.pdf"
else
    echo "ERROR: PDF generation failed"
    exit 1
fi
