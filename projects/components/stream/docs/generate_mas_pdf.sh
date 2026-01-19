#!/usr/bin/env bash
set -euo pipefail

# ------------------------------------------------------------
# STREAM Specification PDF Generator
# ------------------------------------------------------------
# Usage:
#   ./generate_pdf.sh [--rev <version>] [--help]
#
# Example:
#   ./generate_pdf.sh --rev 0.90
#
# This script builds the STREAM specification document
# (DOCX and PDF) from Markdown sources using md_to_docx.py.
# ------------------------------------------------------------

# Default values
REV="0.90"
ASSETS="stream_mas/assets"
SPEC_INDEX="stream_mas/stream_index.md"

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
  $0 --rev 1.0

Description:
  This script generates a DOCX and PDF version of the STREAM specification
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
OUTPUT_BASENAME="STREAM_MAS_v${REV}"
OUTPUT_DOCX="${OUTPUT_BASENAME}.docx"
OUTPUT_PDF="${OUTPUT_BASENAME}.pdf"

# ------------------------------------------------------------
# Run converter
# ------------------------------------------------------------
echo "------------------------------------------------------------"
echo " Generating STREAM Specification"
echo "------------------------------------------------------------"
echo "  Version:     ${REV}"
echo "  Input:       ${SPEC_INDEX}"
echo "  Assets:      ${ASSETS}"
echo "  Output:      ${OUTPUT_DOCX} (and ${OUTPUT_PDF})"
echo "  Repo Root:   ${REPO_ROOT}"
echo "------------------------------------------------------------"

python3 "${REPO_ROOT}/bin/md_to_docx.py" \
  "${SPEC_INDEX}" "${OUTPUT_DOCX}" \
  --style "stream_mas/stream_styles.yaml" \
  --expand-index \
  --skip-index-content \
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
  --assets-dir "${ASSETS}/images" \
  --assets-dir "${ASSETS}/puml" \
  --assets-dir "${ASSETS}/draw.io" \
  --assets-dir "${ASSETS}/mermaid" \
  --quiet


echo
echo "Done: Generated ${OUTPUT_DOCX} and ${OUTPUT_PDF}"
