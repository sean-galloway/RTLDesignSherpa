#!/usr/bin/env bash
set -euo pipefail

# ------------------------------------------------------------
# Delta Specification PDF Generator
# ------------------------------------------------------------
# Usage:
#   ./generate_pdf.sh [--rev <version>] [--help]
#
# Example:
#   ./generate_pdf.sh --rev 0.25
#
# This script builds the Delta specification document
# (DOCX and PDF) from Markdown sources using md_to_docx.py.
# ------------------------------------------------------------

# Default values
REV="0.25"
ASSETS="delta_spec/assets"
SPEC_INDEX="delta_spec/delta_index.md"

# Detect repository root (go up from noc-ip/ to repo root)
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(git -C "${SCRIPT_DIR}" rev-parse --show-toplevel)"  # move-proof (was ../../../.., one level too high after the noc-ip move)

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
  $0 --rev 0.30

Description:
  This script generates a DOCX and PDF version of the Delta specification
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
OUTPUT_BASENAME="Delta_Specification_v${REV}"
OUTPUT_DOCX="delta_spec/${OUTPUT_BASENAME}.docx"
OUTPUT_PDF="delta_spec/${OUTPUT_BASENAME}.pdf"

# ------------------------------------------------------------
# Run converter
# ------------------------------------------------------------
echo "------------------------------------------------------------"
echo " Generating Delta Specification"
echo "------------------------------------------------------------"
echo "  Version:     ${REV}"
echo "  Input:       ${SPEC_INDEX}"
echo "  Assets:      ${ASSETS}"
echo "  Output:      ${OUTPUT_DOCX} (and ${OUTPUT_PDF})"
echo "  Repo Root:   ${REPO_ROOT}"
echo "------------------------------------------------------------"

python3 "${REPO_ROOT}/bin/md_to_docx.py" \
  --style "delta_spec/delta_spec_styles.yaml" \
  --expand-index --skip-index-content --toc --pagebreak --title-page --pdf \
  --pdf-engine=lualatex \
  --mainfont "Noto Serif" \
  --monofont "Noto Sans Mono" \
  --sansfont "Noto Sans" \
  --mathfont "Noto Serif" \
  --assets-dir "${ASSETS}" \
  --assets-dir "${ASSETS}/images" \
  --assets-dir "${ASSETS}/puml" \
  --assets-dir "${ASSETS}/waves" \
  "${SPEC_INDEX}" "${OUTPUT_DOCX}"


echo
echo "Done: Generated ${OUTPUT_DOCX} and ${OUTPUT_PDF}"
