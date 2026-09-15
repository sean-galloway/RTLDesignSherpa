#!/bin/bash
#==============================================================================
# Regenerate all Mermaid diagrams in this directory (source .mmd -> .png)
#==============================================================================
# Rebuilds the PNGs the chapters reference. Uses a puppeteer --no-sandbox config
# to bypass the Ubuntu 23.10+ Chromium sandbox restriction.
# Requires: @mermaid-js/mermaid-cli (npm install -g @mermaid-js/mermaid-cli).
#==============================================================================
set -u
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PUPPETEER_CFG="$(mktemp /tmp/pptr-cdc.XXXX.json)"
cat > "$PUPPETEER_CFG" <<'EOF'
{ "args": ["--no-sandbox", "--disable-setuid-sandbox"] }
EOF
cd "$SCRIPT_DIR"
fail=0
for mmd in *.mmd; do
    [[ -f "$mmd" ]] || continue
    png="${mmd%.mmd}.png"
    echo -n "Generating $png ... "
    if mmdc -i "$mmd" -o "$png" -b white --puppeteerConfigFile "$PUPPETEER_CFG" 2>/tmp/mmdc_cdc_err.log; then
        echo "OK ($(stat -c%s "$png") bytes)"
    else
        echo "FAILED"; head -5 /tmp/mmdc_cdc_err.log; fail=1
    fi
done
rm -f "$PUPPETEER_CFG"
exit $fail
