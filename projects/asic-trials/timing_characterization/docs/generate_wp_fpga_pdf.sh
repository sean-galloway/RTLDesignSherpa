#!/usr/bin/env bash
set -euo pipefail

# ------------------------------------------------------------
# Pre-Bitstream Timing Prediction on FPGA (Artix-7) — PDF generator
# ------------------------------------------------------------
# Usage:   ./generate_wp_fpga_pdf.sh [--rev <version>]
# Example: ./generate_wp_fpga_pdf.sh --rev 0.1
#
# Builds the FPGA companion white paper (DOCX + PDF) from README_FPGA.md
# using bin/md_to_docx.py + the styles YAML under pre_synth_timing_wp_fpga/.
# ------------------------------------------------------------

REV="0.1"
STYLES="pre_synth_timing_wp_fpga/pre_synth_timing_wp_fpga_styles.yaml"
ASSETS_README="../assets"
ASSETS_WP="pre_synth_timing_wp_fpga/assets"
INPUT_MD="../README_FPGA.md"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../../../.." && pwd)"

show_help() {
  cat <<EOF
Usage: $0 [OPTIONS]

Options:
  -r, --rev <version>    Set document revision (default: ${REV})
  -h, --help             Show this help message and exit

Description:
  Generates DOCX and PDF of the Pre-Bitstream Timing Prediction on FPGA
  white paper from README_FPGA.md, applying the corporate styling YAML
  (forest-green theme, Noto fonts, narrow margins, title page + TOC).
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    -r|--rev) REV="${2:-}"; shift 2 ;;
    -h|--help) show_help; exit 0 ;;
    *) echo "Error: unknown arg '$1'" >&2; show_help; exit 1 ;;
  esac
done

OUTPUT_BASENAME="Pre_Synth_Timing_Prediction_FPGA_v${REV}"
OUTPUT_DOCX="${OUTPUT_BASENAME}.docx"
OUTPUT_PDF="${OUTPUT_BASENAME}.pdf"

echo "------------------------------------------------------------"
echo " Generating Pre-Bitstream Timing Prediction on FPGA"
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
