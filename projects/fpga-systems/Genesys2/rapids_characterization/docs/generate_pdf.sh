#!/usr/bin/env bash
# ----------------------------------------------------------------------
# RAPIDS Beats DMA Characterization Report — DOCX/PDF Generator
# ----------------------------------------------------------------------
# Usage:
#   ./generate_pdf.sh [--rev <version>] [--help]
#
# Builds RAPIDS_CharacterizationReport_v<rev>.docx and .pdf from the
# single-file Markdown source using bin/md_to_docx.py with the corporate
# style sheet, header/footer, TOC, list-of-figures, and title page.
#
# House-style convention: mirrors STREAM's docs/generate_pdf.sh. All
# deliverable docs render through this house pipeline; throwaway / tracking
# files stay plain Markdown and are exempt.
# ----------------------------------------------------------------------

set -euo pipefail

REV="1.0"

# REPO_ROOT must be set in the environment (source env_python). We don't
# compute it from relative paths — too brittle when the tree gets reshuffled.
: "${REPO_ROOT:?REPO_ROOT is not set. Source env_python or export REPO_ROOT manually before running this script.}"

DOC_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

ASSETS="${DOC_DIR}/assets"
INPUT="${DOC_DIR}/rapids_characterization_findings.md"
STYLES="${DOC_DIR}/characterization_styles.yaml"
TITLE="${DOC_DIR}/title.md"

show_help() {
  cat <<EOF
Usage: $0 [OPTIONS]

Options:
  -r, --rev <version>    Set document revision (default: ${REV})
  -h, --help             Show this help message and exit

Builds:
  RAPIDS_CharacterizationReport_v<rev>.docx
  RAPIDS_CharacterizationReport_v<rev>.pdf
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

OUT_BASE="RAPIDS_CharacterizationReport_v${REV}"
OUT_DOCX="${DOC_DIR}/${OUT_BASE}.docx"

echo "------------------------------------------------------------"
echo " RAPIDS Beats DMA Characterization Report Generator"
echo "------------------------------------------------------------"
echo "  Version : ${REV}"
echo "  Source  : ${INPUT}"
echo "  Title   : ${TITLE}"
echo "  Styles  : ${STYLES}"
echo "  Output  : ${OUT_BASE}.docx + .pdf"
echo "------------------------------------------------------------"

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
  --quiet

echo
echo "Done: ${OUT_BASE}.docx and ${OUT_BASE}.pdf"
