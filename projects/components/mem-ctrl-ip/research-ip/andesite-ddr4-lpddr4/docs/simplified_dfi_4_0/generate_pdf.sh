#!/usr/bin/env bash
set -euo pipefail

# Simplified DFI 4.0 study-notes PDF generator. Builds
# SIMPLIFIED_DFI_4_0_v0.1.docx/.pdf from the Markdown sources using the
# RTLDesignSherpa md_to_docx.py pipeline. REPO_ROOT must point at a
# checkout of RTLDesignSherpa.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="${REPO_ROOT:-/mnt/data/github/RTLDesignSherpa}"

cd "$SCRIPT_DIR"

INDEX="simplified_dfi_4_0_index.md"
STYLES="simplified_dfi_4_0_styles.yaml"
OUT_BASE="SIMPLIFIED_DFI_4_0_v0.1"

for required in "$INDEX" "$STYLES"; do
  if [[ ! -f "$required" ]]; then
    echo "ERROR: required file not found: $required" >&2
    exit 1
  fi
done

python3 "$REPO_ROOT/bin/md_to_docx.py" \
  "$INDEX" \
  "${OUT_BASE}.docx" \
  --style "$STYLES" \
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
  --assets-dir assets/images

echo
echo "Done: ${OUT_BASE}.docx and ${OUT_BASE}.pdf"
