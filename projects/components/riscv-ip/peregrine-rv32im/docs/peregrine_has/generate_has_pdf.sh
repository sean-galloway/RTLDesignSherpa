#!/usr/bin/env bash
set -euo pipefail

# ------------------------------------------------------------
# PEREGRINE-RV32IM Hardware Architecture Specification PDF Generator
# ------------------------------------------------------------
# Usage:
#   ./generate_has_pdf.sh [--rev <version>] [--help]
#
# Builds PEREGRINE_HAS_v<rev>.docx and .pdf in this directory from
# peregrine_has_index.md with bin/md_to_docx.py (--style, so the PDF
# goes through LibreOffice and the lists come from the style YAML).
# Modeled on kestrel-rv32i/docs/generate_has_pdf.sh. May be invoked
# from any directory. Pipeline mechanics:
# vault/handbook/authoring/doc-generation.md.
#
# Regenerate what the chapters are built from first:
#   python3 ../peregrine_mas/gen_port_tables.py   (port/parameter tables)
#   assets/graphviz/regenerate_all_graphviz.sh    (block diagrams)
# The table check below fails the build if a table is stale.
# ------------------------------------------------------------

REV="0.1"
BOOK="peregrine_has"
ASSETS="assets"
INDEX="${BOOK}_index.md"
OUTPUT_BASENAME_STEM="PEREGRINE_HAS"
TITLE="PEREGRINE-RV32IM Hardware Architecture Specification"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
RTLDS_ROOT="${RTLDS_ROOT:-$(git -C "${SCRIPT_DIR}" rev-parse --show-toplevel)}"
MD2DOCX="${RTLDS_ROOT}/bin/md_to_docx.py"

if [[ ! -f "${MD2DOCX}" ]]; then
  echo "Error: md_to_docx.py not found at ${MD2DOCX}" >&2
  echo "Set RTLDS_ROOT to the RTLDesignSherpa repo root." >&2
  exit 1
fi

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

show_help() {
  cat <<HELP
Usage: $0 [OPTIONS]

Options:
  -r, --rev <version>    Set document revision (default: ${REV})
  -h, --help             Show this help message and exit

Environment:
  RTLDS_ROOT    Path to the RTLDesignSherpa repo root
HELP
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

OUTPUT_BASENAME="${OUTPUT_BASENAME_STEM}_v${REV}"
OUTPUT_DOCX="${OUTPUT_BASENAME}.docx"
OUTPUT_PDF="${OUTPUT_BASENAME}.pdf"

cd "${SCRIPT_DIR}"

echo "------------------------------------------------------------"
echo " Generating ${TITLE}"
echo "------------------------------------------------------------"
echo "  Version:     ${REV}"
echo "  Input:       ${INDEX}"
echo "  Output:      ${OUTPUT_DOCX} (and ${OUTPUT_PDF})"
echo "------------------------------------------------------------"

# The port and parameter tables must match the RTL.
python3 "${SCRIPT_DIR}/../peregrine_mas/gen_port_tables.py" --check

# Build-time styles copy: stamp today's date and the requested revision
# onto the title page (vault/handbook/authoring/spec-doc-standards.md,
# "Page layout"); the checked-in YAML keeps its own values.
STYLE_SRC="${BOOK}_styles.yaml"
BUILD_STYLE="${STYLE_SRC%.yaml}.build.yaml"
sed -e "s/^  date: .*/  date: \"$(date +'%B %-d, %Y')\"/" \
    -e "s/\(Specification\) [0-9][0-9.]*\"/\1 ${REV}\"/" \
    "${STYLE_SRC}" > "${BUILD_STYLE}"
trap 'rm -f "${SCRIPT_DIR}/${BUILD_STYLE}"' EXIT

python3 "${MD2DOCX}" \
  "${INDEX}" "${OUTPUT_DOCX}" \
  --style "${BUILD_STYLE}" \
  --expand-index \
  --skip-index-content \
  --toc \
  --number-sections \
  --title-page \
  --pdf \
  --pagebreak \
  --narrow-margins \
  --pdf-engine=lualatex \
  --mainfont "Noto Serif" \
  --monofont "Noto Sans Mono" \
  --sansfont "Noto Sans" \
  --mathfont "Noto Serif" \
  --assets-dir "${ASSETS}" \
  --assets-dir "${ASSETS}/images" \
  --assets-dir "${ASSETS}/graphviz" \
  --quiet

echo
echo "Done: Generated ${OUTPUT_DOCX} and ${OUTPUT_PDF}"
