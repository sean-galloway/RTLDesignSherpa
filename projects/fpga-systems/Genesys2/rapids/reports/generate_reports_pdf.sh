#!/usr/bin/env bash
set -euo pipefail

# ------------------------------------------------------------
# RAPIDS Byte Characterization Report PDF Generator
# ------------------------------------------------------------
# Builds DOCX + PDF for RAPIDS_ByteCharacterizationReport from perf/README.md
# (written by make_byte_perf_report.py) through bin/md_to_docx.py with the
# RTL Design Sherpa house style.
#
# Usage:
#   ./generate_reports_pdf.sh [--rev <version>] [--help]
#
# Output (next to the README):
#   perf/RAPIDS_ByteCharacterizationReport_v<REV>.{docx,pdf}
# ------------------------------------------------------------

REV="0.1"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# This script lives at projects/fpga-systems/Genesys2/rapids/reports/: FIVE
# levels up to the repo root (env_python's REPO_ROOT wins when set).
REPO_ROOT="${REPO_ROOT:-$(cd "${SCRIPT_DIR}/../../../../.." && pwd)}"

show_help() {
  cat <<EOF
Usage: $0 [OPTIONS]

Options:
  -r, --rev <version>   Set document revision (default: ${REV})
  -h, --help            Show this help message and exit
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    -r|--rev)  REV="${2:-}"; [[ -z "$REV" ]] && { echo "Error: missing value for --rev" >&2; exit 1; }; shift 2 ;;
    -h|--help) show_help; exit 0 ;;
    *) echo "Error: unknown argument '$1'" >&2; echo "Use '$0 --help' for usage."; exit 1 ;;
  esac
done

cd "${SCRIPT_DIR}"
OUT_BASE="perf/RAPIDS_ByteCharacterizationReport_v${REV}"

echo "============================================================"
echo " RAPIDS Byte Characterization Report  v${REV}"
echo "   Repo Root: ${REPO_ROOT}"
echo "============================================================"

python3 "${REPO_ROOT}/bin/md_to_docx.py" \
  "perf/README.md" "${OUT_BASE}.docx" \
  --style "perf_styles.yaml" \
  --toc \
  --title-page \
  --pdf \
  --lot \
  --lof \
  --pagebreak \
  --narrow-margins \
  --pdf-engine=lualatex \
  --mainfont "Noto Serif" \
  --monofont "Noto Sans Mono" \
  --sansfont "Noto Sans" \
  --mathfont "Noto Serif" \
  --assets-dir "${SCRIPT_DIR}/assets" \
  --assets-dir "${SCRIPT_DIR}/assets/images" \
  --assets-dir "${SCRIPT_DIR}/perf" \
  --quiet

echo "Done: ${OUT_BASE}.docx / .pdf"
