#!/usr/bin/env bash
# Generate the "CDC Counter Display on the Nexys A7 -- The FPGA System" book
# (DOCX + PDF) from docs/cdc_fpga_system/ through bin/md_to_docx.py.
#
# Usage: ./generate_fpga_system_pdf.sh [--rev 1.0]
# Diagrams: cdc_fpga_system/assets/graphviz/*.dot are rendered to .png by
# assets/graphviz/regenerate_all_graphviz.sh; run that first after a .dot edit.
set -euo pipefail

REV="1.0"
DOC="cdc_fpga_system"
ASSETS="${DOC}/assets"
SPEC_INDEX="${DOC}/${DOC}_index.md"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(git -C "${SCRIPT_DIR}" rev-parse --show-toplevel)"

while [[ $# -gt 0 ]]; do
  case "$1" in
    -r|--rev) REV="${2:-}"; [[ -z "$REV" ]] && { echo "Error: missing --rev value" >&2; exit 1; }; shift 2;;
    -h|--help) echo "Usage: $0 [--rev <version>]"; exit 0;;
    *) echo "Error: unknown argument '$1'" >&2; exit 1;;
  esac
done

OUTPUT_BASENAME="CDC_FPGA_System_v${REV}"
OUTPUT_DOCX="${OUTPUT_BASENAME}.docx"
OUTPUT_PDF="${OUTPUT_BASENAME}.pdf"

cd "${SCRIPT_DIR}"
echo "Generating ${OUTPUT_DOCX} and ${OUTPUT_PDF} from ${SPEC_INDEX} (rev ${REV})"

python3 "${REPO_ROOT}/bin/md_to_docx.py" \
  "${SPEC_INDEX}" "${OUTPUT_DOCX}" \
  --style "${DOC}/${DOC}_styles.yaml" \
  --title-page "${DOC}/title.md" \
  --expand-index \
  --skip-index-content \
  --toc \
  --number-sections \
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
  --assets-dir "${ASSETS}" \
  --assets-dir "${ASSETS}/images" \
  --assets-dir "${ASSETS}/graphviz" \
  --quiet

echo "Done: ${OUTPUT_DOCX} ${OUTPUT_PDF}"
