#!/usr/bin/env bash
set -euo pipefail

# ============================================================
# FPGA Systems MAS PDF Generator
# ============================================================
# Usage:
#   ./generate_mas_pdf.sh [--help]
#
# Builds the FPGA Systems host-layer specification (DOCX and PDF)
# from the Markdown sources using bin/md_to_docx.py.
#
# Diagrams are NOT rebuilt here. They are mermaid sources under
# fpga_systems_mas/assets/mermaid/; regenerate with:
#   make -C fpga_systems_mas/assets/mermaid
# which needs mmdc (npm install -g @mermaid-js/mermaid-cli).
# ============================================================

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="${REPO_ROOT:-$(cd "$SCRIPT_DIR/../../.." && pwd)}"

show_help() {
  cat <<EOF
Usage: $0 [OPTIONS]

Options:
  -h, --help    Show this help message and exit

Output:
  FPGA_SYSTEMS_MAS_v1.0.docx
  FPGA_SYSTEMS_MAS_v1.0.pdf
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help) show_help; exit 0 ;;
    *) echo "Error: Unknown argument '$1'" >&2; echo "Use '$0 --help' for usage."; exit 1 ;;
  esac
done

cd "$SCRIPT_DIR"

MAS_DIR="fpga_systems_mas"
MAS_INDEX="${MAS_DIR}/fpga_systems_mas_index.md"
STYLES="${MAS_DIR}/fpga_systems_mas_styles.yaml"
ASSETS="${MAS_DIR}/assets"
OUT_BASE="FPGA_SYSTEMS_MAS_v1.0"

# Fail early and by name. A missing styles file or logo otherwise surfaces as a
# pandoc error that names neither.
for required in "$MAS_INDEX" "$STYLES" "$ASSETS/images/logo.png"; do
  if [[ ! -f "$required" ]]; then
    echo "ERROR: required file not found: $required" >&2
    exit 1
  fi
done

# Every diagram referenced by a chapter must exist as a PNG, or it silently
# drops out of the PDF -- the one failure this build cannot otherwise detect.
missing=0
while read -r png; do
  if [[ ! -f "${MAS_DIR}/${png#../}" ]]; then
    echo "ERROR: referenced diagram missing: ${png#../}" >&2
    missing=1
  fi
done < <(grep -ohE '\.\./assets/mermaid/[a-z_]+\.png' "${MAS_DIR}"/ch*/*.md | sort -u)
if [[ $missing -ne 0 ]]; then
  echo "Run: make -C ${MAS_DIR}/assets/mermaid" >&2
  exit 1
fi

echo "============================================================"
echo " Generating FPGA Systems MAS"
echo "============================================================"
echo "  Input:   ${MAS_INDEX}"
echo "  Styles:  ${STYLES}"
echo "  Assets:  ${ASSETS}"
echo "  Output:  ${OUT_BASE}.docx / .pdf"
echo "============================================================"
echo

python3 "$REPO_ROOT/bin/md_to_docx.py" \
  "$MAS_INDEX" \
  "${OUT_BASE}.docx" \
  --style "$STYLES" \
  --expand-index \
  --skip-index-content \
  --toc \
  --number-sections \
  --title-page \
  --pdf \
  --lof \
  --lot \
  --low \
  --pagebreak \
  --narrow-margins \
  --pdf-engine=lualatex \
  --mainfont "Noto Serif" \
  --monofont "Noto Sans Mono" \
  --sansfont "Noto Sans" \
  --mathfont "Noto Serif" \
  --assets-dir "$ASSETS" \
  --assets-dir "$ASSETS/images" \
  --assets-dir "$ASSETS/mermaid"

echo
echo "Done: ${OUT_BASE}.docx and ${OUT_BASE}.pdf"
