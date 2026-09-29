#!/bin/bash
# Log Analysis Script for STREAM Core Tests
# Analyzes rdeng and wreng for burst matrix, performance, and multi-channel tests
# Organizes results by test type to prevent clobbering

# Get script directory and derive paths
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
EXTRACT_SCRIPT="${SCRIPT_DIR}/../../../bin/extract_axi_transactions.py"

echo "Using extraction script: extract_axi_transactions.py"

# Create base output directory for analysis results
ANALYSIS_BASE="logs/analysis"
mkdir -p "$ANALYSIS_BASE"

#==============================================================================
# Function: Process a single log file
#==============================================================================
process_log() {
    local LOG_FILE=$1
    local TEST_TYPE=$2  # "burst", "perf", or "multi"
    local ANALYSIS_DIR="${ANALYSIS_BASE}/${TEST_TYPE}"

    mkdir -p "$ANALYSIS_DIR"

    BASENAME=$(basename "$LOG_FILE" .log)

    # Extract common parameters
    DW=$(echo "$BASENAME" | grep -oP 'dw0*\K[0-9]+')
    FD=$(echo "$BASENAME" | grep -oP 'fd0*\K[0-9]+')
    GW=$(echo "$BASENAME" | grep -oP 'gw\K[0-9]+')

    echo "----------------------------------------"
    echo "Processing: $(basename $LOG_FILE)"
    echo "  Test Type: $TEST_TYPE"
    echo "  Data Width: ${DW}-bit"
    echo "  FIFO Depth: ${FD}"

    # Build unique suffix based on test type
    case $TEST_TYPE in
        burst)
            # Extract burst sizes for burst matrix tests
            # Format: ...burst_rd16_wr8...
            RD_BURST=$(echo "$BASENAME" | grep -oP 'burst_rd\K[0-9]+')
            WR_BURST=$(echo "$BASENAME" | grep -oP '_wr\K[0-9]+')
            SRAM_SIZE=$(echo "$BASENAME" | grep -oP '\K[0-9]+KB' | head -1)
            echo "  RD Burst: ${RD_BURST}"
            echo "  WR Burst: ${WR_BURST}"
            echo "  SRAM: ${SRAM_SIZE}"
            SUFFIX="_rd${RD_BURST}_wr${WR_BURST}_${SRAM_SIZE}_gw${GW}"
            ;;
        perf)
            # Extract performance test specific parameters
            # Format: ...single/dual/quad...
            CHANNEL_TYPE=$(echo "$BASENAME" | grep -oP '(single|dual|quad)' | head -1)
            echo "  Channel Type: ${CHANNEL_TYPE}"
            SUFFIX="_${CHANNEL_TYPE}_gw${GW}"
            ;;
        multi)
            # Extract multi-channel parameters
            DC=$(echo "$BASENAME" | grep -oP 'dc0*\K[0-9]+')
            NCH=$(echo "$BASENAME" | grep -oP 'nch0*\K[0-9]+')
            echo "  Descriptors: ${DC}"
            echo "  Channels: ${NCH}"
            SUFFIX="_nch${NCH}_dc${DC}_gw${GW}"
            ;;
    esac

    # Output file names
    DESCR_OUT="${ANALYSIS_DIR}/descr_dw${DW}${SUFFIX}.log"
    RDENG_OUT="${ANALYSIS_DIR}/rdeng_dw${DW}${SUFFIX}.log"
    WRENG_OUT="${ANALYSIS_DIR}/wreng_dw${DW}${SUFFIX}.log"

    # Run descriptor analysis (parse 256-bit descriptor fields)
    echo "  Analyzing descriptors → $(basename $DESCR_OUT)"
    python3 "$EXTRACT_SCRIPT" "$LOG_FILE" rdeng --interface descr --output "$DESCR_OUT"

    # Run rdeng analysis (data read transactions)
    echo "  Analyzing rdeng → $(basename $RDENG_OUT)"
    python3 "$EXTRACT_SCRIPT" "$LOG_FILE" rdeng --interface rdeng --output "$RDENG_OUT"

    # Run wreng analysis (data write transactions)
    echo "  Analyzing wreng → $(basename $WRENG_OUT)"
    python3 "$EXTRACT_SCRIPT" "$LOG_FILE" wreng --interface wreng --output "$WRENG_OUT"

    # For burst tests, also run comparison if bursts are asymmetric or symmetric
    if [ "$TEST_TYPE" = "burst" ]; then
        COMPARE_OUT="${ANALYSIS_DIR}/compare_dw${DW}${SUFFIX}.txt"

        if [ -n "$RD_BURST" ] && [ -n "$WR_BURST" ]; then
            if [ "$RD_BURST" != "$WR_BURST" ]; then
                echo "  ⚠️  Asymmetric bursts detected (rd${RD_BURST} ≠ wr${WR_BURST})"
                echo "  Running R/W data comparison → $(basename $COMPARE_OUT)"
                python3 "${SCRIPT_DIR}/../../../bin/compare_rd_wr_data.py" "$LOG_FILE" --output "$COMPARE_OUT"
            else
                echo "  ✓ Symmetric bursts (rd${RD_BURST} = wr${WR_BURST})"
                echo "  Running R/W data comparison → $(basename $COMPARE_OUT)"
                python3 "${SCRIPT_DIR}/../../../bin/compare_rd_wr_data.py" "$LOG_FILE" --output "$COMPARE_OUT"
            fi
        fi
    fi

    echo ""
}

#==============================================================================
# Function: Show summary for analysis directory
#==============================================================================
show_summary() {
    local ANALYSIS_DIR=$1
    local TEST_TYPE=$2

    if [ ! -d "$ANALYSIS_DIR" ]; then
        return
    fi

    echo ""
    echo "=========================================="
    echo "$TEST_TYPE Test Analysis Summary"
    echo "=========================================="

    for ANALYSIS_FILE in "$ANALYSIS_DIR"/*.log; do
        if [ -f "$ANALYSIS_FILE" ]; then
            echo ""
            echo "File: $(basename $ANALYSIS_FILE)"

            # Determine file type from name
            if [[ $(basename "$ANALYSIS_FILE") == descr_* ]]; then
                # For descriptor files, count parsed descriptors
                DESC_COUNT=$(grep -c "^Descriptor [0-9]" "$ANALYSIS_FILE" 2>/dev/null || echo "0")
                CHANNELS=$(grep "CHANNEL" "$ANALYSIS_FILE" | grep -oP "CHANNEL \K[0-9]+" | sort -u | tr '\n' ',' | sed 's/,$//')
                echo "  Parsed Descriptors: $DESC_COUNT"
                echo "  Channels: $CHANNELS"
            elif [[ $(basename "$ANALYSIS_FILE") == compare_* ]]; then
                # For comparison files, extract match/mismatch counts
                TOTAL_BEATS=$(grep "Total beats compared:" "$ANALYSIS_FILE" 2>/dev/null | grep -oP '\d+' | head -1)
                MATCHES=$(grep "Matches:" "$ANALYSIS_FILE" 2>/dev/null | grep -oP '\d+' | head -1)
                MISMATCHES=$(grep "Mismatches:" "$ANALYSIS_FILE" 2>/dev/null | grep -oP '\d+' | head -1)
                RESULT=$(grep -o "✓ PASS\|✗ FAIL" "$ANALYSIS_FILE" 2>/dev/null | head -1)
                echo "  Total Beats: $TOTAL_BEATS"
                echo "  Matches: $MATCHES"
                echo "  Mismatches: $MISMATCHES"
                echo "  Result: $RESULT"
            else
                # For rdeng/wreng files, count AXI transactions
                AR_COUNT=$(grep -c "AR\[id=" "$ANALYSIS_FILE" 2>/dev/null || echo "0")
                AW_COUNT=$(grep -c "AW\[id=" "$ANALYSIS_FILE" 2>/dev/null || echo "0")
                CHANNELS=$(grep "CHANNEL" "$ANALYSIS_FILE" | grep -oP "CHANNEL \K[0-9]+" | sort -u | tr '\n' ',' | sed 's/,$//')
                if [ "$AR_COUNT" != "0" ]; then
                    echo "  AR Transactions: $AR_COUNT"
                fi
                if [ "$AW_COUNT" != "0" ]; then
                    echo "  AW Transactions: $AW_COUNT"
                fi
                echo "  Channels: $CHANNELS"
            fi
        fi
    done
}

#==============================================================================
# Main Processing
#==============================================================================

echo "=========================================="
echo "AXI Transaction Analysis for STREAM Tests"
echo "=========================================="
echo ""

TOTAL_PROCESSED=0

#------------------------------------------------------------------------------
# Process Burst Matrix Tests
#------------------------------------------------------------------------------
BURST_LOGS=$(ls logs/*burst_rd*_wr*.log 2>/dev/null | sort)

if [ -n "$BURST_LOGS" ]; then
    BURST_COUNT=$(echo "$BURST_LOGS" | wc -l)
    echo "Found $BURST_COUNT burst matrix test log(s)"
    echo ""

    for LOG_FILE in $BURST_LOGS; do
        process_log "$LOG_FILE" "burst"
        ((TOTAL_PROCESSED++))
    done
fi

#------------------------------------------------------------------------------
# Process Performance Tests
#------------------------------------------------------------------------------
PERF_LOGS=$(ls logs/test_stream_performance*.log 2>/dev/null | sort)

if [ -n "$PERF_LOGS" ]; then
    PERF_COUNT=$(echo "$PERF_LOGS" | wc -l)
    echo "Found $PERF_COUNT performance test log(s)"
    echo ""

    for LOG_FILE in $PERF_LOGS; do
        process_log "$LOG_FILE" "perf"
        ((TOTAL_PROCESSED++))
    done
fi

#------------------------------------------------------------------------------
# Process Multi-Channel Tests
#------------------------------------------------------------------------------
MULTI_LOGS=$(ls logs/test_stream_core_multi*.log 2>/dev/null | sort)

if [ -n "$MULTI_LOGS" ]; then
    MULTI_COUNT=$(echo "$MULTI_LOGS" | wc -l)
    echo "Found $MULTI_COUNT multi-channel test log(s)"
    echo ""

    for LOG_FILE in $MULTI_LOGS; do
        process_log "$LOG_FILE" "multi"
        ((TOTAL_PROCESSED++))
    done
fi

#------------------------------------------------------------------------------
# Check if any logs were found
#------------------------------------------------------------------------------
if [ $TOTAL_PROCESSED -eq 0 ]; then
    echo "ERROR: No test logs found in logs/"
    echo ""
    echo "Expected log patterns:"
    echo "  - Burst matrix: *burst_rd*_wr*.log"
    echo "  - Performance: test_stream_performance*.log"
    echo "  - Multi-channel: test_stream_core_multi*.log"
    echo ""
    exit 1
fi

#==============================================================================
# Show Summaries
#==============================================================================

echo ""
echo "=========================================="
echo "Analysis Complete!"
echo "=========================================="
echo "Total logs processed: $TOTAL_PROCESSED"
echo ""
echo "Output organized by test type:"
echo "  - Burst matrix:  $ANALYSIS_BASE/burst/"
echo "  - Performance:   $ANALYSIS_BASE/perf/"
echo "  - Multi-channel: $ANALYSIS_BASE/multi/"
echo ""

# Show summaries for each test type
show_summary "$ANALYSIS_BASE/burst" "Burst Matrix"
show_summary "$ANALYSIS_BASE/perf" "Performance"
show_summary "$ANALYSIS_BASE/multi" "Multi-Channel"

echo ""
