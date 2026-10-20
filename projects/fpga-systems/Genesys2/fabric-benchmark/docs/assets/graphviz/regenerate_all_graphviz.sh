#!/bin/bash
#==============================================================================
# Regenerate every Graphviz diagram in this directory (.dot -> .png)
#==============================================================================
# One renderer for the whole repo: bin/render_block_diagram.py draws each
# diagram, GENERATES its key from the classes and line styles it uses, pastes
# the key centered underneath, and palette-encodes the PNG (no tIME chunk, so
# an unchanged source re-renders byte-identical). Rules:
# vault/handbook/authoring/block-diagrams.md. Markdown references the .png.
#==============================================================================
set -u
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(git -C "$SCRIPT_DIR" rev-parse --show-toplevel)"
cd "$SCRIPT_DIR"
shopt -s nullglob
dots=(*.dot)
[[ ${#dots[@]} -gt 0 ]] || { echo "no .dot files in $SCRIPT_DIR"; exit 0; }
exec python3 "$REPO_ROOT/bin/render_block_diagram.py" --dpi "${DPI:-150}" "${dots[@]}"
