#!/bin/bash
# Log Analysis Script for Multi-Channel Tests
# Analyzes rdeng and wreng for all multi-channel test logs

# Get script directory and derive paths
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

EXTRACT_SCRIPT="${SCRIPT_DIR}/../../../bin/extract_axi_transactions.py"

echo "Using extraction script: extract_axi_transactions.py"

# Create output directory for analysis results
ANALYSIS_DIR="logs/analysis"
mkdir -p "$ANALYSIS_DIR"

echo "=========================================="
echo "AXI Transaction Analysis for Multi-Channel Tests"
echo "=========================================="
echo ""

# Find all multi-channel test logs
MULTI_LOGS=$(ls logs/test_stream_core_multi*.log 2>/dev/null | sort)

if [ -z "$MULTI_LOGS" ]; then
    echo "ERROR: No multi-channel test logs found in logs/"
    exit 1
fi

# Count total logs
LOG_COUNT=$(echo "$MULTI_LOGS" | wc -l)
echo "Found $LOG_COUNT multi-channel test log(s)"
echo ""

# Process each log file
for LOG_FILE in $MULTI_LOGS; do
    # Extract key parameters from filename
    # Format: test_stream_core_multi_nc04_dw0128_fd0512_dc04_nch02_standard_fast_gw3.log
    BASENAME=$(basename "$LOG_FILE" .log)

    # Extract data width (e.g., dw0128 -> 128)
    DW=$(echo "$BASENAME" | grep -oP 'dw0*\K[0-9]+')

    # Extract FIFO depth (e.g., fd0512 -> 512)
    FD=$(echo "$BASENAME" | grep -oP 'fd0*\K[0-9]+')

    # Extract descriptor count (e.g., dc04 -> 04)
    DC=$(echo "$BASENAME" | grep -oP 'dc0*\K[0-9]+')

    # Extract number of channels (e.g., nch02 -> 02)
    NCH=$(echo "$BASENAME" | grep -oP 'nch0*\K[0-9]+')

    # Extract gtkwave ID (e.g., gw3 -> 3)
    GW=$(echo "$BASENAME" | grep -oP 'gw\K[0-9]+')

    echo "----------------------------------------"
    echo "Processing: $(basename $LOG_FILE)"
    echo "  Data Width: ${DW}-bit"
    echo "  FIFO Depth: ${FD}"
    echo "  Descriptors: ${DC}"
    echo "  Channels: ${NCH}"
    echo "  GTKWave ID: ${GW}"
    echo ""

    # Determine suffix for multiple logs with same data width
    if [ $LOG_COUNT -gt 1 ]; then
        # Use gtkwave ID as unique identifier
        SUFFIX="_gw${GW}"
    else
        SUFFIX=""
    fi

    # Output file names
    RDENG_OUT="${ANALYSIS_DIR}/rdeng_dw${DW}${SUFFIX}.log"
    WRENG_OUT="${ANALYSIS_DIR}/wreng_dw${DW}${SUFFIX}.log"

    # Run rdeng analysis
    echo "  Analyzing rdeng → $(basename $RDENG_OUT)"
    python3 "$EXTRACT_SCRIPT" "$LOG_FILE" rdeng --interface rdeng --output "$RDENG_OUT"

    # Run wreng analysis
    echo "  Analyzing wreng → $(basename $WRENG_OUT)"
    python3 "$EXTRACT_SCRIPT" "$LOG_FILE" wreng --interface wreng --output "$WRENG_OUT"

    echo ""
done

echo "=========================================="
echo "Analysis Complete!"
echo "=========================================="
echo ""
echo "Output files in: $ANALYSIS_DIR/"
ls -lh "$ANALYSIS_DIR"/*.log 2>/dev/null
echo ""

# Optional: Show summary of each analysis
echo "=========================================="
echo "Quick Summary"
echo "=========================================="
for ANALYSIS_FILE in "$ANALYSIS_DIR"/*.log; do
    if [ -f "$ANALYSIS_FILE" ]; then
        echo ""
        echo "File: $(basename $ANALYSIS_FILE)"
        # Count transactions
        TX_COUNT=$(grep -c "^Transaction" "$ANALYSIS_FILE" 2>/dev/null || echo "0")
        # Count descriptors
        DESC_COUNT=$(grep -c "^Descriptor" "$ANALYSIS_FILE" 2>/dev/null || echo "0")
        echo "  Descriptors: $DESC_COUNT"
        echo "  Transactions: $TX_COUNT"
    fi
done
echo ""
