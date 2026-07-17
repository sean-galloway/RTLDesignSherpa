#!/usr/bin/env bash
set -euo pipefail

# ------------------------------------------------------------
# RAPIDS Characterization Reports PDF Generator
# ------------------------------------------------------------
# Mirrors projects/NexysA7/stream_characterization/reports/generate_reports_pdf.sh.
# Builds DOCX + PDF for the RAPIDS characterization reports from their
# Markdown READMEs using bin/md_to_docx.py with the RTL Design Sherpa
# house style (logo title page, forest-green/gray headings, three-part
# footer, TOC + List of Tables/Figures, numbered sections).
#
# Usage:
#   ./generate_reports_pdf.sh [--rev <version>] [--only perf] [--help]
#
# Example:
#   ./generate_reports_pdf.sh --rev 1.0
#
# Outputs (next to each report's README, gitignored):
#   perf/RAPIDS_Char_Perf_v<REV>.{docx,pdf}
# ------------------------------------------------------------

REV="1.0"
ONLY="all"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# reports/ -> rapids_characterization/ -> NexysA7/ -> projects/ -> repo root
REPO_ROOT="$(cd "${SCRIPT_DIR}/../../../.." && pwd)"

show_help() {
  cat <<EOF
Usage: $0 [OPTIONS]

Options:
  -r, --rev <version>   Set document revision (default: ${REV})
  -o, --only <perf>     Build just one report (default: all)
  -h, --help            Show this help message and exit

Description:
  Generates DOCX + PDF for the RAPIDS characterization reports by invoking
  bin/md_to_docx.py with the per-report house-style YAMLs. The PDF is
  produced from the styled DOCX so it matches the RAPIDS/STREAM HAS/MAS
  corporate look (logo title page, forest-green/gray headings, three-part
  footer, TOC + List of Tables/Figures, numbered sections).
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
    --quiet
}

cd "${SCRIPT_DIR}"

echo "============================================================"
echo " Generating RAPIDS Characterization Reports"
echo "   Version:   ${REV}"
echo "   Repo Root: ${REPO_ROOT}"
echo "============================================================"

if [[ "$ONLY" == "all" || "$ONLY" == "perf" ]]; then
  build_report "perf/README.md" "perf_styles.yaml" \
               "perf/RAPIDS_Char_Perf_v${REV}"
fi

echo
echo "Done."
