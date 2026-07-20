#!/usr/bin/env bash
set -euo pipefail

# ------------------------------------------------------------
# RTL Library PDF generator (Common + Math + AMBA-by-protocol)
# ------------------------------------------------------------
# For each "book" this script:
#   1. auto-generates a link-only index (the doc set + order) — with
#      --skip-index-content only the LINKS matter; the PDF TOC is built from the
#      module headings, so the index needs no prose.
#   2. renders DOCX + PDF via bin/md_to_docx.py, inlining every linked doc in
#      order (--expand-index), stripping the repeated logo header
#      (--strip-doc-header), and starting each module on a new page (--pagebreak).
#
# Output filenames are STABLE (no version); the revision shows in the title page.
# Usage: ./generate_rtl_pdfs.sh [--rev X.Y] [book ...]   (default: all books)
# ------------------------------------------------------------

REV="0.90"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"       # docs/markdown
REPO_ROOT="$(git -C "${SCRIPT_DIR}" rev-parse --show-toplevel)"
MD2DOCX="${REPO_ROOT}/bin/md_to_docx.py"
STYLE_TMPL="${SCRIPT_DIR}/rtl_pdf_styles.yaml"
OUTDIR="$(cd "${SCRIPT_DIR}/.." && pwd)"                          # docs/ — all book PDFs land here

ARGS=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    -r|--rev) REV="${2:?}"; shift 2;;
    -h|--help) echo "Usage: $0 [--rev X.Y] [book ...]"; exit 0;;
    *) ARGS+=("$1"); shift;;
  esac
done

cd "${SCRIPT_DIR}"

# gen_index <index_path> <title> <file...>   — emit a link-only index
gen_index() {
  local out="$1" title="$2"; shift 2
  local dir; dir="$(dirname "$out")"
  { echo "# ${title}"; echo; echo "<!-- Auto-generated link index for PDF build. Regenerate via generate_rtl_pdfs.sh -->"; echo; } > "$out"
  local f rel h1
  for f in "$@"; do
    rel="$(realpath --relative-to="$dir" "$f")"
    h1="$(grep -m1 '^# ' "$f" 2>/dev/null | sed 's/^#\s*//')"
    [[ -z "$h1" ]] && h1="$(basename "$f" .md)"
    echo "- [${h1}](${rel})" >> "$out"
  done
}

# build_book <title> <subtitle> <index_path> <out_name> [extra md_to_docx flags...]
#
# Lists (LoF/LoT/LoW) are OPT-IN PER BOOK. The flags only insert the list
# section -- entries come from caption encoding in the Markdown
# ("### Figure C.N:", "#### Waveform C.N:", and a Pandoc ": Caption" line after
# a table; see bin/DOC_GENERATION.md). A book whose sources lack that encoding
# would render an EMPTY list, so only pass the flag where the captions exist.
build_book() {
  local title="$1" subtitle="$2" index="$3" name="$4"; shift 4
  # Remaining args are list names to ENABLE: lot / lof / low
  local lot=false lof=false low=false a
  for a in "$@"; do case "$a" in lot) lot=true;; lof) lof=true;; low) low=true;; esac; done
  local outbase="${OUTDIR}/${name}"
  local tmpstyle="${SCRIPT_DIR}/.book_styles.yaml"
  sed -e "s|__TITLE__|${title}|" -e "s|__SUBTITLE__|${subtitle}|" \
      -e "s|__LOT__|${lot}|" -e "s|__LOF__|${lof}|" -e "s|__LOW__|${low}|" \
      "${STYLE_TMPL}" > "${tmpstyle}"
  echo "------------------------------------------------------------"
  echo " Building: ${title}  (${subtitle})  ->  docs/${name}.pdf"
  echo "------------------------------------------------------------"
  python3 "${MD2DOCX}" "${index}" "${outbase}.docx" \
    --style "${tmpstyle}" \
    --expand-index --skip-index-content --strip-doc-header \
    --toc --number-sections --pdf --pagebreak --narrow-margins \
    --pdf-engine=lualatex \
    --mainfont "Noto Serif" --monofont "Noto Sans Mono" \
    --sansfont "Noto Sans" --mathfont "Noto Serif" \
    --assets-dir "assets" --assets-dir "assets/RTLCommon" \
    --assets-dir "assets/RTLAmba" --assets-dir "assets/WAVES" \
    --quiet
  rm -f "${tmpstyle}" "${outbase}.docx"      # keep only the PDF at docs/ level
}

want() { [[ ${#ARGS[@]} -eq 0 ]] || printf '%s\n' "${ARGS[@]}" | grep -qx "$1"; }

SUB="Module Reference — Rev ${REV}"

# ---- Common (RTLCommon minus the math_* family) ----
if want common; then
  mapfile -t COMMON < <(ls RTLCommon/*.md | grep -vE '/(index|overview|math_|_book_)' )
  # keep overview as the lead doc for the Common book
  gen_index RTLCommon/_book_common_index.md "RTL Common Library" RTLCommon/overview.md "${COMMON[@]}"
  build_book "RTL Common Library" "${SUB}" RTLCommon/_book_common_index.md RTL_Common_Library
fi

# ---- Math (the math_* family + its overview) ----
if want math; then
  mapfile -t MATH < <(ls RTLCommon/math_*.md 2>/dev/null)
  gen_index RTLCommon/_book_math_index.md "RTL Math Library" RTLCommon/math_library.md "${MATH[@]}"
  build_book "RTL Math Library" "${SUB}" RTLCommon/_book_math_index.md RTL_Math_Library
fi

# ---- CDC (dedicated cross-cutting book: primer + primitives + gray + slaves) ----
if want cdc; then
  CDC=(
    RTLAmba/cdc/cdc.md
    RTLCommon/glitch_free_n_dff_arn.md
    RTLCommon/bin2gray.md
    RTLCommon/gray2bin.md
    RTLCommon/johnson2bin.md
    RTLCommon/counter_bingray.md
    RTLCommon/clock_pulse.md
    RTLAmba/apb/apb_slave_cdc.md
    RTLAmba/apb/apb_slave_cdc_cg.md
    RTLAmba/apb5/apb5_slave_cdc.md
    RTLAmba/apb5/apb5_slave_cdc_cg.md
  )
  gen_index _book_cdc_index.md "RTL Clock Domain Crossing" "${CDC[@]}"
  # cdc.md carries "#### Waveform C.N:" headings and ": Caption" table captions,
  # so this book can populate a List of Waveforms and a List of Tables.
  build_book "RTL Clock Domain Crossing" "${SUB}" _book_cdc_index.md RTL_CDC low lot
fi

# ---- Monitor subsystem (dedicated: all rtl/amba/monitor docs + monitor pkg docs) ----
if want monitor; then
  mapfile -t MON < <(ls RTLAmba/monitor/*.md RTLAmba/includes/monitor_*.md 2>/dev/null | grep -vE '_book_')
  gen_index RTLAmba/_book_monitor_index.md "RTL AMBA Monitor Subsystem" "${MON[@]}"
  build_book "RTL AMBA Monitor Subsystem" "${SUB}" RTLAmba/_book_monitor_index.md RTL_AMBA_Monitor
fi

# ---- AMBA, split by protocol ----
amba_book() {  # <book-key> <Title> <out-name> <subdir...>
  local key="$1" title="$2" out="$3"; shift 3
  want "$key" || return 0
  local files=(); local d
  # LC_ALL=C forces byte-order sorting. Without it `ls` uses locale collation,
  # which ignores punctuation: "axis5_master_cg.md" collates as "axis5mastercg"
  # and so sorted BEFORE "axis5_master.md", putting every clock-gated variant
  # ahead of the base module it wraps. Locale collation is also case-insensitive,
  # which sorted README.md last and buried each book's Overview at the end.
  # Byte order fixes both: '.' (0x2E) < '_' (0x5F), and 'R' (0x52) < 'a' (0x61).
  for d in "$@"; do files+=( $(LC_ALL=C ls RTLAmba/"$d"/*.md 2>/dev/null | grep -vE '/(index|_book_)') ); done
  [[ ${#files[@]} -eq 0 ]] && { echo "  (no docs for $key, skip)"; return 0; }
  gen_index "RTLAmba/_book_${key}_index.md" "${title}" "${files[@]}"
  build_book "${title}" "${SUB}" "RTLAmba/_book_${key}_index.md" "${out}"
}

amba_book apb    "RTL AMBA APB4"          RTL_AMBA_APB4          apb
amba_book apb5   "RTL AMBA APB5"          RTL_AMBA_APB5          apb5
amba_book axi4   "RTL AMBA AXI4"          RTL_AMBA_AXI4          axi4
amba_book axil4  "RTL AMBA AXI4-Lite"     RTL_AMBA_AXI4_Lite     axil4
amba_book axis4  "RTL AMBA AXI4-Stream"   RTL_AMBA_AXI4_Stream   axis4
amba_book axi5   "RTL AMBA AXI5"          RTL_AMBA_AXI5          axi5
amba_book axis5  "RTL AMBA AXI5-Stream"   RTL_AMBA_AXI5_Stream   axis5
amba_book shared "RTL AMBA Shared Infrastructure" RTL_AMBA_Shared  gaxi shared shims

echo
echo "All requested books generated (rev ${REV})."
