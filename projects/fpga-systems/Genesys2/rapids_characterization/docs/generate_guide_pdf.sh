#!/usr/bin/env bash
set -euo pipefail

# ------------------------------------------------------------
# RAPIDS Characterization — Project Guide PDF Generator
# ------------------------------------------------------------
# Usage:
#   ./generate_guide_pdf.sh [--rev <version>] [--help]
#
# Builds the CDC Counter Display operator/developer guide (DOCX + PDF) from the
# chapterized Markdown under cdc_demo_guide/ using bin/md_to_docx.py. Skeleton-
# identical to the STREAM generate_*_pdf.sh scripts; only the doc name, index,
# and styles file differ.
# ------------------------------------------------------------

REV="0.90"
DOC="rapids_char_guide"
ASSETS="${DOC}/assets"
SPEC_INDEX="${DOC}/${DOC}_index.md"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(git -C "${SCRIPT_DIR}" rev-parse --show-toplevel)"

show_help() {
  cat <<EOF
Usage: $0 [OPTIONS]

Options:
  -r, --rev <version>    Set document revision (default: ${REV})
  -h, --help             Show this help message and exit

Description:
  Generates a DOCX and PDF of the CDC Counter Display project guide by invoking
  bin/md_to_docx.py on ${SPEC_INDEX}.
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    -r|--rev) REV="${2:-}"; [[ -z "$REV" ]] && { echo "Error: missing --rev value" >&2; exit 1; }; shift 2;;
    -h|--help) show_help; exit 0;;
    *) echo "Error: unknown argument '$1'" >&2; echo "Use '$0 --help'."; exit 1;;
  esac
done

OUTPUT_BASENAME="RAPIDS_Characterization_Guide_v${REV}"
OUTPUT_DOCX="${OUTPUT_BASENAME}.docx"
OUTPUT_PDF="${OUTPUT_BASENAME}.pdf"

cd "${SCRIPT_DIR}"

echo "------------------------------------------------------------"
echo " Generating RAPIDS Characterization Project Guide"
echo "------------------------------------------------------------"
echo "  Version:   ${REV}"
echo "  Input:     ${SPEC_INDEX}"
echo "  Output:    ${OUTPUT_DOCX} (and ${OUTPUT_PDF})"
echo "  Repo Root: ${REPO_ROOT}"
echo "------------------------------------------------------------"

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
  --assets-dir "${ASSETS}/mermaid" \
  --assets-dir "${ASSETS}/wavedrom" \
  --quiet

echo
echo "Done: Generated ${OUTPUT_DOCX} and ${OUTPUT_PDF}"
