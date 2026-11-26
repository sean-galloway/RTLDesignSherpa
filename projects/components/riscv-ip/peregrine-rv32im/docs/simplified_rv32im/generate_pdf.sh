#!/usr/bin/env bash
set -euo pipefail

# Simplified RV32IM (peregrine) study-notes PDF generator. Builds
# SIMPLIFIED_RV32IM_v<rev>.docx/.pdf from the Markdown sources using the
# RTLDesignSherpa md_to_docx.py pipeline. REPO_ROOT must point at a
# checkout of RTLDesignSherpa.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="${REPO_ROOT:-$(git -C "$SCRIPT_DIR" rev-parse --show-toplevel)}"

cd "$SCRIPT_DIR"

INDEX="simplified_rv32im_index.md"
STYLES="simplified_rv32im_styles.yaml"
# The revision lives in the index's "**Version:**" line, not here.
REV="$(grep -m1 -oE '^\*\*Version:\*\* [0-9]+\.[0-9]+' "$INDEX" | grep -oE '[0-9]+\.[0-9]+$' || true)"
if [[ -z "$REV" ]]; then echo "ERROR: no **Version:** line in $INDEX" >&2; exit 1; fi
OUT_BASE="SIMPLIFIED_RV32IM_v${REV}"

for required in "$INDEX" "$STYLES"; do
  if [[ ! -f "$required" ]]; then
    echo "ERROR: required file not found: $required" >&2
    exit 1
  fi
done

# Title page is stamped at build time: the styles YAML hard-codes the
# date, so a copy carries today's and is removed on exit.
BUILD_STYLE="${STYLES%.yaml}.build.yaml"
sed -e "s/^  date: .*/  date: \"$(date +'%B %-d, %Y')\"/" "$STYLES" > "$BUILD_STYLE"
trap 'rm -f "$BUILD_STYLE"' EXIT

python3 "$REPO_ROOT/bin/md_to_docx.py" \
  "$INDEX" \
  "${OUT_BASE}.docx" \
  --style "$BUILD_STYLE" \
  --expand-index \
  --skip-index-content \
  --toc \
  --number-sections \
  --title-page \
  --pdf \
  --lof \
  --lot \
  --low \
  --pagebreak \
  --assets-dir assets \
  --assets-dir assets/images \
  --assets-dir assets/wavedrom

echo
echo "Done: ${OUT_BASE}.docx and ${OUT_BASE}.pdf"
