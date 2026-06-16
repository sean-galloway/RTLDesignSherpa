#!/usr/bin/env bash
set -euo pipefail

# ------------------------------------------------------------
# STREAM Characterization Reports PDF Generator
# ------------------------------------------------------------
# Mirrors projects/components/stream/docs/generate_{has,mas}_pdf.sh.
# Builds DOCX + PDF for the STREAM characterization reports
# (perf + compression) from their Markdown READMEs using
# bin/md_to_docx.py with the RTL Design Sherpa house style.
#
# Usage:
#   ./generate_reports_pdf.sh [--rev <version>] [--only perf|compression] [--help]
#
# Example:
#   ./generate_reports_pdf.sh --rev 1.0
#   ./generate_reports_pdf.sh --only compression
#
# Outputs (next to each report's README, gitignored):
#   perf/STREAM_Char_Perf_v<REV>.{docx,pdf}
#   compression/STREAM_Char_Compression_v<REV>.{docx,pdf}
# ------------------------------------------------------------

REV="0.92"
ONLY="all"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# reports/ -> stream_characterization/ -> NexysA7/ -> projects/ -> repo root
REPO_ROOT="$(cd "${SCRIPT_DIR}/../../../.." && pwd)"

show_help() {
  cat <<EOF
Usage: $0 [OPTIONS]

Options:
  -r, --rev <version>          Set document revision (default: ${REV})
  -o, --only <perf|compression>  Build just one report (default: both)
  -h, --help                   Show this help message and exit

Description:
  Generates DOCX + PDF for the STREAM characterization reports by invoking
  bin/md_to_docx.py with the per-report house-style YAMLs. The PDF is
  produced from the styled DOCX via LibreOffice so it matches the STREAM
  HAS/MAS corporate look (logo title page, forest-green/gray headings,
  three-part footer, TOC + List of Tables, numbered sections).
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    -r|--rev)  REV="${2:-}"; [[ -z "$REV" ]] && { echo "Error: missing value for --rev" >&2; exit 1; }; shift 2 ;;
    -o|--only) ONLY="${2:-}"; shift 2 ;;
    -h|--help) show_help; exit 0 ;;
    *) echo "Error: unknown argument '$1'" >&2; echo "Use '$0 --help' for usage."; exit 1 ;;
  esac
done

# ------------------------------------------------------------
# Per-report build: <input md> <style yaml> <output basename>
# ------------------------------------------------------------
build_report() {
  local input_md="$1" style="$2" out_base="$3"
  local out_docx="${out_base}.docx" out_pdf="${out_base}.pdf"

  echo "------------------------------------------------------------"
  echo "  Input:    ${input_md}"
  echo "  Style:    ${style}"
  echo "  Output:   ${out_docx} (and ${out_pdf})"
  echo "------------------------------------------------------------"

  python3 "${REPO_ROOT}/bin/md_to_docx.py" \
    "${input_md}" "${out_docx}" \
    --style "${style}" \
    --toc \
    --number-sections \
    --title-page \
    --pdf \
    --lot \
    --pagebreak \
    --narrow-margins \
    --pdf-engine=lualatex \
    --mainfont "Noto Serif" \
    --monofont "Noto Sans Mono" \
    --sansfont "Noto Sans" \
    --mathfont "Noto Serif" \
    --assets-dir "${SCRIPT_DIR}/assets" \
    --assets-dir "${SCRIPT_DIR}/assets/images" \
    --quiet
}

cd "${SCRIPT_DIR}"

echo "============================================================"
echo " Generating STREAM Characterization Reports"
echo "   Version:   ${REV}"
echo "   Repo Root: ${REPO_ROOT}"
echo "============================================================"

if [[ "$ONLY" == "all" || "$ONLY" == "perf" ]]; then
  build_report "perf/README.md" "perf_styles.yaml" \
               "perf/STREAM_Char_Perf_v${REV}"
fi

if [[ "$ONLY" == "all" || "$ONLY" == "compression" ]]; then
  build_report "compression/README.md" "compression_styles.yaml" \
               "compression/STREAM_Char_Compression_v${REV}"
fi

echo
echo "Done."
