#!/bin/bash
#==============================================================================
# Regenerate all Mermaid diagrams in this directory (.mmd -> .png)
#==============================================================================
# Requires: mermaid-cli (npm install -g @mermaid-js/mermaid-cli).
#
# PNG, not SVG: markdown must reference .png -- see
# vault/handbook/authoring/doc-pipeline.md. SVG out of headless Chrome also
# renders text badly when the fonts are not installed in the headless
# environment, which is why md_to_docx.py renders mermaid to PNG too.
#
# --no-sandbox: the Chromium sandbox fails on Ubuntu 23.10+ ("No usable
# sandbox!"), so the puppeteer config below is required, not optional.
#==============================================================================
set -u
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"
command -v mmdc >/dev/null || { echo "ERROR: mmdc not found (npm install -g @mermaid-js/mermaid-cli)"; exit 1; }

PUPPETEER_CFG="$(mktemp -t puppeteer-XXXXXX.json)"
trap 'rm -f "$PUPPETEER_CFG"' EXIT
printf '{"args":["--no-sandbox","--disable-setuid-sandbox"]}\n' > "$PUPPETEER_CFG"

SCALE="${SCALE:-2}"

fail=0
for mmd in *.mmd; do
    [[ -f "$mmd" ]] || continue
    png="${mmd%.mmd}.png"
    echo -n "Generating $png ... "
    if mmdc -i "$mmd" -o "$png" -s "$SCALE" -b white \
            --puppeteerConfigFile "$PUPPETEER_CFG" 2>/tmp/mmdc_err.log && [[ -f "$png" ]]; then
        command -v convert >/dev/null && convert "$png" -colors 64 PNG8:"$png"
        echo "OK ($(stat -c%s "$png") bytes, $(identify -format '%wx%h' "$png" 2>/dev/null))"
    else
        echo "FAILED"; head -5 /tmp/mmdc_err.log; fail=1
    fi
done
exit $fail
