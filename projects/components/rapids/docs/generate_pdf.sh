#!/usr/bin/env bash
set -euo pipefail

# ------------------------------------------------------------
# RAPIDS Beats HAS/MAS PDF Generator
# ------------------------------------------------------------
# Usage:
#   ./generate_pdf.sh [--rev <version>] [--help]
#
# Example:
#   ./generate_pdf.sh --rev 1.0
#
# This script builds both the RAPIDS Beats HAS and MAS documents
# (DOCX and PDF) from Markdown sources using md_to_docx.py.
# ------------------------------------------------------------

# Default values
REV="0.5"

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
  This script generates DOCX and PDF versions of both the RAPIDS Beats
  HAS (Hardware Architecture Specification) and MAS (Module Architecture
  Specification) by invoking the md_to_docx.py converter.
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
# Common converter options
# ------------------------------------------------------------
COMMON_OPTS=(
  --expand-index
  --skip-index-content
  --toc
  --number-sections
  --title-page
  --pdf
  --lof
  --lot
  --pagebreak
  --narrow-margins
  --pdf-engine=lualatex
  --mainfont "Noto Serif"
  --monofont "Noto Sans Mono"
  --sansfont "Noto Sans"
  --mathfont "Noto Serif"
  --quiet
)

# ------------------------------------------------------------
# Generate HAS
# ------------------------------------------------------------
HAS_INDEX="rapids_beats_has/rapids_beats_has_index.md"
HAS_ASSETS="rapids_beats_has/assets"
HAS_DOCX="RAPIDS_Beats_HAS_v${REV}.docx"
HAS_PDF="RAPIDS_Beats_HAS_v${REV}.pdf"

if [[ -f "${HAS_INDEX}" ]]; then
  echo "------------------------------------------------------------"
  echo " Generating RAPIDS Beats HAS (Hardware Architecture Spec)"
  echo "------------------------------------------------------------"
  echo "  Version:     ${REV}"
  echo "  Input:       ${HAS_INDEX}"
  echo "  Output:      ${HAS_DOCX} / ${HAS_PDF}"
  echo "------------------------------------------------------------"

  python3 "${REPO_ROOT}/bin/md_to_docx.py" \
    "${HAS_INDEX}" "${HAS_DOCX}" \
    "${COMMON_OPTS[@]}" \
    --assets-dir "${HAS_ASSETS}" \
    --assets-dir "${HAS_ASSETS}/mermaid" \
    --assets-dir "${HAS_ASSETS}/wavedrom"

  echo "  Done: ${HAS_DOCX} and ${HAS_PDF}"
  echo
else
  echo "Skipping HAS: ${HAS_INDEX} not found"
  echo
fi

# ------------------------------------------------------------
# Generate MAS
# ------------------------------------------------------------
MAS_INDEX="rapids_beats_mas/rapids_beats_mas_index.md"
MAS_ASSETS="rapids_beats_mas/assets"
MAS_DOCX="RAPIDS_Beats_MAS_v${REV}.docx"
MAS_PDF="RAPIDS_Beats_MAS_v${REV}.pdf"

if [[ -f "${MAS_INDEX}" ]]; then
  echo "------------------------------------------------------------"
  echo " Generating RAPIDS Beats MAS (Module Architecture Spec)"
  echo "------------------------------------------------------------"
  echo "  Version:     ${REV}"
  echo "  Input:       ${MAS_INDEX}"
  echo "  Output:      ${MAS_DOCX} / ${MAS_PDF}"
  echo "------------------------------------------------------------"

  python3 "${REPO_ROOT}/bin/md_to_docx.py" \
    "${MAS_INDEX}" "${MAS_DOCX}" \
    "${COMMON_OPTS[@]}" \
    --assets-dir "${MAS_ASSETS}" \
    --assets-dir "${MAS_ASSETS}/mermaid" \
    --assets-dir "${MAS_ASSETS}/wavedrom"

  echo "  Done: ${MAS_DOCX} and ${MAS_PDF}"
  echo
else
  echo "Skipping MAS: ${MAS_INDEX} not found"
  echo
fi

echo "============================================================"
echo " PDF Generation Complete"
echo "============================================================"
