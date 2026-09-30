#!/bin/bash
#==============================================================================
# Regenerate every Graphviz diagram in this directory (.dot -> .png)
#==============================================================================
# Requires: graphviz `dot` (the oss-cad-suite ships one; so does apt).
#
# PNG, not SVG: markdown must reference .png -- see
# vault/handbook/authoring/doc-pipeline.md. Rendered at 150 dpi, then
# palette-encoded (PNG8, 64 colours): the diagrams are flat line art, so the
# bytes drop by 3-5x with no visible change. -define png:exclude-chunk=tIME
# keeps an unchanged source re-rendering byte-identical rather than dirtying
# git.
#==============================================================================
set -u
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"
command -v dot >/dev/null || { echo "ERROR: graphviz 'dot' not found"; exit 1; }

DPI="${DPI:-150}"
fail=0
for src in *.dot; do
    [[ -f "$src" ]] || continue
    png="${src%.dot}.png"
    echo -n "Generating $png ... "
    if dot -Tpng -Gdpi="$DPI" "$src" -o "$png" 2>/tmp/dot_err.log && [[ -f "$png" ]]; then
        command -v convert >/dev/null && convert "$png" -colors 64 -define png:exclude-chunk=tIME PNG8:"$png"
        echo "OK ($(stat -c%s "$png") bytes, $(identify -format '%wx%h' "$png" 2>/dev/null))"
    else
        echo "FAILED"; head -5 /tmp/dot_err.log; fail=1
    fi
done
exit $fail
