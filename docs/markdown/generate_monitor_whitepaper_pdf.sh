#!/usr/bin/env bash
# ------------------------------------------------------------
# Render the monitor system white paper as a branded PDF.
#
#   docs/markdown/rtl-amba/monitor_system_whitepaper.md
#     -> docs/pdfs/RTL_AMBA_Monitor_Whitepaper_v<REV>.pdf
#
# Same pipeline and the same corporate style template as the RTL library
# books (generate_rtl_pdfs.sh / rtl_pdf_styles.yaml), with the title page
# filled in for this document. No LoF/LoT: the paper's figures are plain
# image embeds without "### Figure" captions, so those lists would be empty.
# No --title-page: the branded title page comes from the style YAML, and the
# flag's auto-generated "# <filename> / Generated:" section would land in the
# body ahead of the paper (the FPGA paper's PDF shows that artefact). No
# --number-sections: the paper numbers its six axes itself.
#
# Usage: ./generate_monitor_whitepaper_pdf.sh [--rev X.Y]   (default: the
#        version stated in the paper's own "**Version:**" line)
# ------------------------------------------------------------
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
INPUT_MD="${SCRIPT_DIR}/rtl-amba/monitor_system_whitepaper.md"
OUTDIR="${REPO_ROOT}/docs/pdfs"
STYLE_TMPL="${SCRIPT_DIR}/rtl_pdf_styles.yaml"

REV="$(grep -oE '^\*\*Version:\*\* [0-9]+\.[0-9]+' "${INPUT_MD}" | grep -oE '[0-9]+\.[0-9]+' | head -1)"
while [[ $# -gt 0 ]]; do
  case "$1" in
    -r|--rev) REV="${2:-}"; shift 2 ;;
    -h|--help) sed -n '2,15p' "$0"; exit 0 ;;
    *) echo "unknown arg '$1'" >&2; exit 1 ;;
  esac
done
[[ -n "${REV}" ]] || { echo "could not read the version from ${INPUT_MD}" >&2; exit 1; }

OUTBASE="${OUTDIR}/RTL_AMBA_Monitor_Whitepaper_v${REV}"
TMPSTYLE="${SCRIPT_DIR}/.whitepaper_styles.yaml"
sed -e 's|__TITLE__|The Monitor System as a Design Surface|' \
    -e "s|__SUBTITLE__|— AMBA Monitor System White Paper, Rev ${REV}|" \
    -e 's|__LOT__|false|' -e 's|__LOF__|false|' -e 's|__LOW__|false|' \
    -e "s|date: \"July 2026\"|date: \"$(date +'%B %Y')\"|" \
    "${STYLE_TMPL}" > "${TMPSTYLE}"
trap 'rm -f "${TMPSTYLE}" "${OUTBASE}.docx"' EXIT

echo "------------------------------------------------------------"
echo " Monitor system white paper  Rev ${REV}  ->  ${OUTBASE}.pdf"
echo "------------------------------------------------------------"
cd "${SCRIPT_DIR}"
python3 "${REPO_ROOT}/bin/md_to_docx.py" "${INPUT_MD}" "${OUTBASE}.docx" \
  --style "${TMPSTYLE}" \
  --strip-doc-header \
  --toc --pdf --narrow-margins \
  --pdf-engine=lualatex \
  --mainfont "Noto Serif" --monofont "Noto Sans Mono" \
  --sansfont "Noto Sans" --mathfont "Noto Serif" \
  --assets-dir "assets" --assets-dir "assets/rtl-amba" \
  --quiet
echo "wrote ${OUTBASE}.pdf"
