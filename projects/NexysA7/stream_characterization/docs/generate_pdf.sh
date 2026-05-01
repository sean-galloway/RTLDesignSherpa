#!/usr/bin/env bash
# ----------------------------------------------------------------------
# STREAM DMA Characterization Report — DOCX/PDF Generator
# ----------------------------------------------------------------------
# Usage:
#   ./generate_pdf.sh [--rev <version>] [--help]
#
# Builds STREAM_CharacterizationReport_v<rev>.docx and .pdf from the
# single-file Markdown source using bin/md_to_docx.py with the corporate
# style sheet, header/footer, TOC, list-of-figures, and title page.
# ----------------------------------------------------------------------

set -euo pipefail

REV="0.90"
DOC_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CHAR_ROOT="$(cd "${DOC_DIR}/.." && pwd)"
REPO_ROOT="$(cd "${DOC_DIR}/../../../.." && pwd)"

ASSETS="${DOC_DIR}/assets"
INPUT="${DOC_DIR}/characterization_v1_findings.md"
STYLES="${DOC_DIR}/characterization_styles.yaml"
TITLE="${DOC_DIR}/title.md"

# Each flow's plots/ contributes to the shared writeup. The sync below
# pulls fresh PNGs from every flow into docs/assets/png/ at build time
# so the generated DOCX/PDF is a self-contained bundle.
FLOW_PLOTS_DIRS=(
  "${CHAR_ROOT}/flows-stream-bridge/plots"
  "${CHAR_ROOT}/flows-vivado-mcdma/plots"
  "${CHAR_ROOT}/flows-stream-vivado-bridge/plots"
  "${CHAR_ROOT}/flows-vivado-mcdma-vivado-bridge/plots"
)

show_help() {
  cat <<EOF
Usage: $0 [OPTIONS]

Options:
  -r, --rev <version>    Set document revision (default: ${REV})
  -h, --help             Show this help message and exit

Builds:
  STREAM_CharacterizationReport_v<rev>.docx
  STREAM_CharacterizationReport_v<rev>.pdf
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    -r|--rev)
      REV="${2:-}"
      [[ -z "$REV" ]] && { echo "Error: --rev needs a value" >&2; exit 1; }
      shift 2
      ;;
    -h|--help) show_help; exit 0 ;;
    *) echo "Error: unknown arg '$1'" >&2; exit 1 ;;
  esac
done

OUT_BASE="STREAM_CharacterizationReport_v${REV}"
OUT_DOCX="${DOC_DIR}/${OUT_BASE}.docx"

echo "------------------------------------------------------------"
echo " STREAM Characterization Report Generator"
echo "------------------------------------------------------------"
echo "  Version : ${REV}"
echo "  Source  : ${INPUT}"
echo "  Title   : ${TITLE}"
echo "  Styles  : ${STYLES}"
echo "  Output  : ${OUT_BASE}.docx + .pdf"
echo "------------------------------------------------------------"

# Sync the live sweep plots from every flow's plots/ into docs/assets/png/
# so the doc is a self-contained bundle. The graphviz PNGs already live
# there; we overlay each flow's freshest plot PNGs on top.
for plots_dir in "${FLOW_PLOTS_DIRS[@]}"; do
  if [[ -d "${plots_dir}" ]]; then
    if compgen -G "${plots_dir}/*.png" >/dev/null; then
      echo "Syncing plots:  ${plots_dir}/*.png  →  ${ASSETS}/png/"
      cp -u "${plots_dir}"/*.png "${ASSETS}/png/" 2>/dev/null || true
    fi
  fi
done

cd "${DOC_DIR}"
python3 "${REPO_ROOT}/bin/md_to_docx.py" \
  "${INPUT}" "${OUT_DOCX}" \
  --style "${STYLES}" \
  --title-page "${TITLE}" \
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
  --assets-dir "${ASSETS}/png" \
  --assets-dir "${ASSETS}/dot" \
  --quiet

echo
echo "Done: ${OUT_BASE}.docx and ${OUT_BASE}.pdf"
