#!/bin/bash
#==============================================================================
# Regenerate All STREAM Mermaid Diagrams
#==============================================================================
# Purpose: Convert .mmd files to .svg using local mmdc (mermaid-cli)
# Method: Use --no-sandbox flag to bypass Ubuntu 23.10+ AppArmor restrictions
# Requirements: mermaid-cli installed (npm install -g @mermaid-js/mermaid-cli)
# Output: SVG format for crisp vector graphics in PDF generation
#==============================================================================

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PUPPETEER_CFG="/tmp/puppeteer-config-stream.json"

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
echo " STREAM Mermaid Diagram Regeneration"
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

    echo -n "Generating $svg ... "

    # Generate SVG using mmdc with no-sandbox config
    if mmdc -i "$mmd" -o "$svg" -b transparent --puppeteerConfigFile "$PUPPETEER_CFG" 2>/tmp/mmdc_error.log; then
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
