#!/usr/bin/env bash
set -euo pipefail

# ------------------------------------------------------------
# APB Crossbar Spec PDF Generator
# ------------------------------------------------------------
# Usage:
#   ./generate_pdf.sh [--rev <version>] [--help]
#
# Example:
#   ./generate_pdf.sh --rev 1.1
#
# This script builds the APB Crossbar specification document
# (DOCX and PDF) from Markdown sources using md_to_docx.py.
# ------------------------------------------------------------

# Default values
REV="1.0"
ASSETS="apb_xbar_spec/assets"
SPEC_INDEX="apb_xbar_spec/apb_xbar_index.md"

# Detect repository root (go up from docs/ to project root)
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../../../.." && pwd)"

# ------------------------------------------------------------
# Parse command line arguments
# ------------------------------------------------------------
show_help() {
  cat <<EOF
Usage: $0 [OPTIONS]

Options:
  -r, --rev <version>    Set document revision (default: ${REV})
  -h, --help             Show this help message and exit

Example:
  $0 --rev 1.1

Description:
  This script generates a DOCX and PDF version of the APB Crossbar specification
  by invoking the md_to_docx.py converter. It stitches together the Markdown
  chapters, applies page breaks, and includes assets for images and diagrams.
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

# ------------------------------------------------------------
# Build filenames dynamically
# ------------------------------------------------------------
OUTPUT_BASENAME="APB_Crossbar_Specification_v${REV}"
OUTPUT_DOCX="${OUTPUT_BASENAME}.docx"
OUTPUT_PDF="${OUTPUT_BASENAME}.pdf"

# ------------------------------------------------------------
# Run converter
# ------------------------------------------------------------
echo "------------------------------------------------------------"
echo " Generating APB Crossbar Specification"
echo "------------------------------------------------------------"
echo "  Version:     ${REV}"
echo "  Input:       ${SPEC_INDEX}"
echo "  Assets:      ${ASSETS}"
echo "  Output:      ${OUTPUT_DOCX} (and ${OUTPUT_PDF})"
echo "  Repo Root:   ${REPO_ROOT}"
echo "------------------------------------------------------------"

python3 "${REPO_ROOT}/bin/md_to_docx.py" \
  --expand-index --toc --pagebreak --title-page --pdf \
  --pdf-engine=lualatex \
  --mainfont "Noto Serif" \
  --monofont "Noto Sans Mono" \
  --sansfont "Noto Sans" \
  --mathfont "Noto Serif" \
  --assets-dir "${ASSETS}" \
  --assets-dir "${ASSETS}/svg" \
  --assets-dir "${ASSETS}/graphviz" \
  --assets-dir "${ASSETS}/wavedrom" \
  "${SPEC_INDEX}" "${OUTPUT_DOCX}"


echo
echo "✅ Done: Generated ${OUTPUT_DOCX} and ${OUTPUT_PDF}"
