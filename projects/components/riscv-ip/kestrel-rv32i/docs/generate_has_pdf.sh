#!/usr/bin/env bash
set -euo pipefail

# ------------------------------------------------------------
# KESTREL-RV32I Hardware Architecture Specification PDF Generator
# ------------------------------------------------------------
# Usage:
#   ./generate_has_pdf.sh [--rev <version>] [--help]
#
# Example:
#   ./generate_has_pdf.sh --rev 0.1
#
# This script builds the KESTREL Hardware Architecture Specification
# (DOCX and PDF) from Markdown sources using md_to_docx.py.
# Modeled on RTLDesignSherpa/projects/components/dma-ip/stream/docs/
# generate_has_pdf.sh. May be invoked from any directory; it cd's
# to its own location before resolving relative paths.
# ------------------------------------------------------------

# Default values
REV="0.1"
ASSETS="kestrel_has/assets"
HAS_INDEX="kestrel_has/kestrel_has_index.md"

# md_to_docx.py lives in the RTLDesignSherpa repo, not this directory.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
RTLDS_ROOT="${RTLDS_ROOT:-$(cd "${SCRIPT_DIR}/../../../../.." && pwd)}"
MD2DOCX="${RTLDS_ROOT}/bin/md_to_docx.py"

if [[ ! -f "${MD2DOCX}" ]]; then
  echo "Error: md_to_docx.py not found at ${MD2DOCX}" >&2
  echo "Set RTLDS_ROOT to the RTLDesignSherpa repo root." >&2
  exit 1
fi

# ------------------------------------------------------------
# Dependency checks (fail loudly so a missing tool does not
# silently regress the output).
# ------------------------------------------------------------
check_python_module() {
  local module="$1"
  local pip_name="$2"
  if ! python3 -c "import ${module}" 2>/dev/null; then
    echo "Error: required Python module '${module}' is not installed." >&2
    echo "Install with: pip install --user ${pip_name}" >&2
    exit 1
  fi
}

check_python_module docx python-docx
check_python_module yaml PyYAML

if ! command -v pandoc >/dev/null 2>&1; then
  echo "Error: 'pandoc' not found in PATH." >&2
  exit 1
fi

if ! command -v soffice >/dev/null 2>&1 && ! command -v libreoffice >/dev/null 2>&1; then
  echo "Error: LibreOffice ('soffice' or 'libreoffice') not found in PATH." >&2
  echo "PDF conversion requires LibreOffice writer_pdf_Export filter." >&2
  exit 1
fi

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
  $0 --rev 0.2

Description:
  This script generates a DOCX and PDF version of the KESTREL-RV32I
  Hardware Architecture Specification by invoking the md_to_docx.py
  converter. It stitches together the Markdown chapters, applies page
  breaks, and includes assets for images and diagrams.

Environment:
  RTLDS_ROOT    Path to the RTLDesignSherpa repo root
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
OUTPUT_BASENAME="KESTREL_HAS_v${REV}"
OUTPUT_DOCX="${OUTPUT_BASENAME}.docx"
OUTPUT_PDF="${OUTPUT_BASENAME}.pdf"

# All relative paths below resolve against the script location,
# so the invocation works from a clean shell in any directory.
cd "${SCRIPT_DIR}"

# ------------------------------------------------------------
# Run converter
# ------------------------------------------------------------
echo "------------------------------------------------------------"
echo " Generating KESTREL-RV32I Hardware Architecture Specification"
echo "------------------------------------------------------------"
echo "  Version:     ${REV}"
echo "  Input:       ${HAS_INDEX}"
echo "  Assets:      ${ASSETS}"
echo "  Output:      ${OUTPUT_DOCX} (and ${OUTPUT_PDF})"
echo "  RTLDS root:  ${RTLDS_ROOT}"
echo "------------------------------------------------------------"

python3 "${MD2DOCX}" \
  "${HAS_INDEX}" "${OUTPUT_DOCX}" \
  --style "kestrel_has/kestrel_has_styles.yaml" \
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
  --assets-dir "${ASSETS}/wavedrom" \
  --quiet

echo
echo "Done: Generated ${OUTPUT_DOCX} and ${OUTPUT_PDF}"
