#!/usr/bin/env bash
set -euo pipefail

# ------------------------------------------------------------
# Monitor System Whitepaper PDF Generator
# ------------------------------------------------------------
# Usage:
#   ./generate_whitepaper_pdf.sh [--rev <version>] [--help]
#
# Example:
#   ./generate_whitepaper_pdf.sh --rev 0.91
#
# Builds the AMBA Monitor System whitepaper as a single-file
# DOCX + PDF via bin/md_to_docx.py. Models the same flag set
# as projects/components/stream/docs/generate_mas_pdf.sh so
# the corporate styling stays consistent across documents.
# ------------------------------------------------------------

REV="0.90"
INPUT="monitor_system_whitepaper.md"
ASSETS="assets"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../../.." && pwd)"

show_help() {
  cat <<EOF
Usage: $0 [OPTIONS]

Options:
  -r, --rev <version>    Set document revision (default: ${REV})
  -h, --help             Show this help message and exit

Example:
  $0 --rev 1.0

Description:
  Generates a DOCX and PDF version of the AMBA Monitor System whitepaper
  using bin/md_to_docx.py with the same style/font/layout conventions as
  the STREAM specification.
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    -r|--rev)
      REV="${2:-}"
      if [[ -z "$REV" ]]; then
        echo "Error: Missing value for --rev" >&2
        exit 1
      fi
      shift 2
      ;;
    -h|--help)
      show_help
      exit 0
      ;;
    *)
      echo "Error: Unknown argument '$1'" >&2
      echo "Use '$0 --help' for usage."
      exit 1
      ;;
  esac
done

OUTPUT_BASENAME="MonitorSystem_Whitepaper_v${REV}"
OUTPUT_DOCX="${OUTPUT_BASENAME}.docx"
OUTPUT_PDF="${OUTPUT_BASENAME}.pdf"

# Local style sheet derived from STREAM's corporate single-source-of-truth
# (projects/components/stream/docs/stream_mas/stream_styles.yaml). Only the
# title_page block is customized for this document; fonts / colors / heading
# rules match the corporate template so this PDF renders consistently with
# the STREAM and bridge spec PDFs. The logo path inside the YAML points back
# at STREAM's logo asset so there is still one image source of truth.
STYLE_PATH="${SCRIPT_DIR}/monitor_whitepaper_styles.yaml"

echo "------------------------------------------------------------"
echo " Generating AMBA Monitor System Whitepaper"
echo "------------------------------------------------------------"
echo "  Version:     ${REV}"
echo "  Input:       ${INPUT}"
echo "  Assets:      ${ASSETS}"
echo "  Output:      ${OUTPUT_DOCX} (and ${OUTPUT_PDF})"
echo "  Style:       ${STYLE_PATH}"
echo "  Repo Root:   ${REPO_ROOT}"
echo "------------------------------------------------------------"

cd "${SCRIPT_DIR}"

python3 "${REPO_ROOT}/bin/md_to_docx.py" \
  "${INPUT}" "${OUTPUT_DOCX}" \
  --style "${STYLE_PATH}" \
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
  --assets-dir "${ASSETS}" \
  --assets-dir "${ASSETS}/mermaid" \
  --quiet

echo
echo "Done: Generated ${OUTPUT_DOCX} and ${OUTPUT_PDF}"
