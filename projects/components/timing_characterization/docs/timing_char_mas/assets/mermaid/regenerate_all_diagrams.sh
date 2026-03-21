#!/bin/bash
#==============================================================================
# Regenerate All Timing Char MAS Mermaid Diagrams
#==============================================================================
# Purpose: Convert .mmd files to .svg using local mmdc (mermaid-cli)
# Method: Use --no-sandbox flag to bypass Ubuntu 23.10+ AppArmor restrictions
# Requirements: mermaid-cli installed (npm install -g @mermaid-js/mermaid-cli)
# Output: SVG + PNG (PNG used by PDF pipeline, SVG for web/markdown preview)
#==============================================================================

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PUPPETEER_CFG="/tmp/puppeteer-config-timing-char-mas.json"

# Create puppeteer config with no-sandbox flags
cat > "$PUPPETEER_CFG" << 'EOF'
{
  "args": [
    "--no-sandbox",
    "--disable-setuid-sandbox"
  ]
}
EOF

cd "$SCRIPT_DIR"

echo "=========================================="
echo " Timing Char MAS Mermaid Diagram Regeneration"
echo "=========================================="
echo "Using: mmdc (mermaid-cli) v$(mmdc --version)"
echo "Config: No-sandbox mode (Ubuntu 23.10+ compatibility)"
echo "Directory: $SCRIPT_DIR"
echo ""

SUCCESS=0
FAIL=0
SKIP=0

for mmd in *.mmd; do
    # Skip if no .mmd files exist
    if [[ ! -f "$mmd" ]]; then
        continue
    fi

    svg="${mmd%.mmd}.svg"
    png="${mmd%.mmd}.png"

    echo -n "Generating $svg + $png ... "

    # Generate SVG using mmdc with no-sandbox config
    if mmdc -i "$mmd" -o "$svg" -b transparent --puppeteerConfigFile "$PUPPETEER_CFG" 2>/tmp/mmdc_error.log; then
        # Also generate PNG for PDF pipeline compatibility
        mmdc -i "$mmd" -o "$png" -b white --puppeteerConfigFile "$PUPPETEER_CFG" 2>/dev/null
        if [[ -f "$svg" ]]; then
            file_size=$(stat --format=%s "$svg" 2>/dev/null)
            echo "OK (${file_size} bytes)"
            ((SUCCESS++))
        else
            echo "FAILED (no output file)"
            ((FAIL++))
        fi
    else
        echo "FAILED (mmdc error)"
        cat /tmp/mmdc_error.log | head -5
        ((FAIL++))
    fi
done

echo ""
echo "=========================================="
echo " Generation Complete"
echo "=========================================="
echo "Success: $SUCCESS"
echo "Failed:  $FAIL"
echo "Skipped: $SKIP"
echo ""
echo "SVG files in directory:"
ls -1 *.svg 2>/dev/null | wc -l
echo ""

# Cleanup
rm -f "$PUPPETEER_CFG"

if [[ $FAIL -gt 0 ]]; then
    echo "WARNING: Some diagrams failed to generate!"
    exit 1
else
    echo "All diagrams generated successfully!"
    exit 0
fi
