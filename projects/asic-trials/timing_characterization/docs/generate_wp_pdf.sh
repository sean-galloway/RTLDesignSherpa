#!/usr/bin/env bash
set -euo pipefail

# ------------------------------------------------------------
# Pre-Synth Timing Prediction White Paper PDF Generator
# ------------------------------------------------------------
# Usage:
#   ./generate_wp_pdf.sh [--rev <version>] [--help]
#
# Example:
#   ./generate_wp_pdf.sh --rev 3.1
#
# Builds the Pre-Synth Timing Prediction White Paper (DOCX and PDF)
# straight from the project README.md using md_to_docx.py + the styles
# YAML under pre_synth_timing_wp/.
# ------------------------------------------------------------

REV="3.1"
STYLES="pre_synth_timing_wp/pre_synth_timing_wp_styles.yaml"
ASSETS_README="../assets"
ASSETS_WP="pre_synth_timing_wp/assets"
INPUT_MD="../README.md"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../../../.." && pwd)"

show_help() {
  cat <<EOF
Usage: $0 [OPTIONS]

Options:
  -r, --rev <version>    Set document revision (default: ${REV})
  -h, --help             Show this help message and exit

Example:
  $0 --rev 3.1

Description:
  Generates DOCX and PDF versions of the Pre-Synth Timing Prediction
  White Paper from the project README.md, applying the corporate
  styling YAML (forest-green theme, Noto fonts, narrow margins, title
  page + TOC + LOT + LOF).
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    -r|--rev) REV="${2:-}"; shift 2 ;;
    -h|--help) show_help; exit 0 ;;
    *) echo "Error: unknown arg '$1'" >&2; show_help; exit 1 ;;
  esac
done

OUTPUT_BASENAME="Pre_Synth_Timing_Prediction_White_Paper_v${REV}"
OUTPUT_DOCX="${OUTPUT_BASENAME}.docx"
OUTPUT_PDF="${OUTPUT_BASENAME}.pdf"

echo "------------------------------------------------------------"
echo " Generating Pre-Synth Timing Prediction White Paper"
echo "------------------------------------------------------------"
echo "  Version:  ${REV}"
echo "  Input:    ${INPUT_MD}"
echo "  Styles:   ${STYLES}"
echo "  Output:   ${OUTPUT_DOCX} + ${OUTPUT_PDF}"
echo "  Repo:     ${REPO_ROOT}"
echo "------------------------------------------------------------"

python3 "${REPO_ROOT}/bin/md_to_docx.py" \
  "${INPUT_MD}" "${OUTPUT_DOCX}" \
  --style "${STYLES}" \
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
  --assets-dir "${ASSETS_README}" \
  --assets-dir "${ASSETS_WP}" \
  --assets-dir "${ASSETS_WP}/images" \
  --quiet

echo
echo "Done: Generated ${OUTPUT_DOCX} and ${OUTPUT_PDF}"
