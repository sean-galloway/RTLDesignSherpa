#!/usr/bin/env bash
# Generate the "Binary BCH Board Validation Report" book (DOCX + PDF) from
# docs/bch_board_validation/ through bin/md_to_docx.py.
#
# Usage: ./generate_bch_board_validation.sh [--rev 0.1]
set -euo pipefail

REV="0.1"
DOC="bch_board_validation"
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

OUTPUT_BASENAME="Binary_BCH_Board_Validation_v${REV}"
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
  --assets-dir "${REPO_ROOT}/projects/fpga-systems/Genesys2/bch/stable/results/2026-10-05_soak" \
 

echo "Done: ${OUTPUT_DOCX} ${OUTPUT_PDF}"
