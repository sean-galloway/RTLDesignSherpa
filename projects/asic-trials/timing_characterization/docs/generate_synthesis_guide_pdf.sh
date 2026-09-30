#!/usr/bin/env bash
# ------------------------------------------------------------
# Render rtl/syn/SYNTHESIS_GUIDE.md as a branded DOCX + PDF
# (timing_characterization TASK-004), on the same md_to_docx pipeline
# and style template as this area's HAS, MAS and white papers.
#
#   ./generate_synthesis_guide_pdf.sh [--rev X.Y]
#     -> Timing_Characterization_Synthesis_Guide_v<REV>.{docx,pdf}
#
# Revision defaults to the guide's own "**Version:**" line. No --title-page
# (the branded title page comes from the styles YAML; the flag's auto section
# would land in the body) and no --number-sections (the guide numbers its own
# sections). No LoF/LoT: the guide has no captioned figures or tables.
# ------------------------------------------------------------
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../../../.." && pwd)"
INPUT_MD="${SCRIPT_DIR}/../rtl/syn/SYNTHESIS_GUIDE.md"
STYLES="${SCRIPT_DIR}/synthesis_guide/synthesis_guide_styles.yaml"
ASSETS="${SCRIPT_DIR}/pre_synth_timing_wp_fpga/assets"   # shared logo

REV="$(grep -m1 -oE '^\*\*Version:\*\* [0-9]+\.[0-9]+' "${INPUT_MD}" | grep -oE '[0-9]+\.[0-9]+')"
while [[ $# -gt 0 ]]; do
  case "$1" in
    -r|--rev) REV="${2:?}"; shift 2 ;;
    -h|--help) sed -n '2,13p' "$0"; exit 0 ;;
    *) echo "unknown arg '$1'" >&2; exit 1 ;;
  esac
done
OUT="${SCRIPT_DIR}/Timing_Characterization_Synthesis_Guide_v${REV}"
echo "------------------------------------------------------------"
echo " Synthesis Guide  Rev ${REV}  ->  $(basename "${OUT}").{docx,pdf}"
echo "------------------------------------------------------------"
cd "${SCRIPT_DIR}"
python3 "${REPO_ROOT}/bin/md_to_docx.py" "${INPUT_MD}" "${OUT}.docx" \
  --style "${STYLES}" \
  --strip-doc-header \
  --toc --pdf --pagebreak --narrow-margins \
  --pdf-engine=lualatex \
  --mainfont "Noto Serif" --monofont "Noto Sans Mono" \
  --sansfont "Noto Sans" --mathfont "Noto Serif" \
  --assets-dir "${ASSETS}" --assets-dir "${ASSETS}/images" \
  --quiet
echo "Done: ${OUT}.docx and ${OUT}.pdf"
