#!/bin/bash
#
# STREAM Core Performance Profiling Script
#
# Runs stream_core tests with 'fast' (no-stress) timing profile to collect
# baseline performance metrics across various configurations.
#
# Usage:
#   ./run_performance_profile.sh [output_dir]
#
# Output:
#   - Individual test logs in perf_results/
#   - Consolidated performance report: perf_results/performance_report.txt
#

set -euo pipefail

# Configuration
OUTPUT_DIR="${1:-perf_results_realistic_sram}"
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
REPORT_FILE="${OUTPUT_DIR}/performance_report_${TIMESTAMP}.txt"

# Test settings
export WAVES=0
export TEST_LEVEL=func  # Use func level for meaningful data (4 descriptors, 2 channels)

# Create output directory
mkdir -p "${OUTPUT_DIR}"

echo "╔═══════════════════════════════════════════════════════════════╗"
echo "║     STREAM Core Performance Profiling                        ║"
echo "╠═══════════════════════════════════════════════════════════════╣"
echo "║  Timing Profile: FAST (no-stress)                             ║"
echo "║  Test Level: ${TEST_LEVEL}                                          ║"
echo "║  Output: ${OUTPUT_DIR}/                          ║"
echo "╚═══════════════════════════════════════════════════════════════╝"
echo ""

# Performance test configurations
# Format: "test_name:description"
CONFIGS=(
    # Single channel tests - params0, params1, params2 are auto-generated based on TEST_LEVEL
    "params0:Single Channel Config 0 (128-bit)"
    "params1:Single Channel Config 1 (256-bit)"
    "params2:Single Channel Config 2 (512-bit)"
)

# Function to run a performance test
run_perf_test() {
    local config_str="$1"
    local test_name=$(echo "$config_str" | cut -d: -f1)
    local description=$(echo "$config_str" | cut -d: -f2)

    local log_file="${OUTPUT_DIR}/${test_name}.log"

    echo "─────────────────────────────────────────────────────────────"
    echo "Running: ${description}"
    echo "  Test: ${test_name}"
    echo "  Level: ${TEST_LEVEL}"
    echo "─────────────────────────────────────────────────────────────"

    # Run test and capture output
    if timeout 120 /mnt/data/github/rtldesignsherpa/venv/bin/python -m pytest \
        test_stream_core.py::test_stream_core_single_channel \
        -k "${test_name}" \
        -v \
        2>&1 | tee "${log_file}"; then
        echo "✓ Test PASSED"
    else
        local exit_code=$?
        if [ ${exit_code} -eq 124 ]; then
            echo "✗ Test TIMEOUT"
        else
            echo "✗ Test FAILED (exit code: ${exit_code})"
        fi
    fi

    echo ""
}

# Run all performance tests
echo "Running ${#CONFIGS[@]} performance test configurations..."
echo ""

for config in "${CONFIGS[@]}"; do
    run_perf_test "$config"
done

# Generate performance report
echo "╔═══════════════════════════════════════════════════════════════╗"
echo "║     Generating Performance Report                             ║"
echo "╚═══════════════════════════════════════════════════════════════╝"
echo ""

{
    echo "=============================================================================="
    echo " STREAM Core Performance Profiling Report"
    echo "=============================================================================="
    echo ""
    echo "Generated: $(date)"
    echo "Timing Profile: FAST (no-stress)"
    echo "Test Level: ${TEST_LEVEL}"
    echo ""
    echo "------------------------------------------------------------------------------"
    echo "Test Results"
    echo "------------------------------------------------------------------------------"
    echo ""
    printf "%-45s %-15s %-12s\n" "Configuration" "Status" "Duration (us)"
    echo "------------------------------------------------------------------------------"

    for config in "${CONFIGS[@]}"; do
        test_name=$(echo "$config" | cut -d: -f1)
        description=$(echo "$config" | cut -d: -f2)
        log_file="${OUTPUT_DIR}/${test_name}.log"

        if [ -f "${log_file}" ]; then
            # Extract status
            if grep -q "=== Test PASSED ===" "${log_file}"; then
                status="PASSED"
            elif grep -q "TIMEOUT" "${log_file}"; then
                status="TIMEOUT"
            else
                status="FAILED"
            fi

            # Extract duration (if available)
            duration=$(grep "Transfer completed in" "${log_file}" | tail -1 | sed 's/.*in \([0-9.]*\) us.*/\1/' || echo "N/A")
            if [ "${duration}" == "N/A" ]; then
                duration=$(grep "seconds" "${log_file}" | tail -1 | sed 's/.*in \([0-9.]*\) seconds.*/\1/' || echo "N/A")
            fi

            printf "%-45s %-15s %-12s\n" "${description}" "${status}" "${duration}"
        else
            printf "%-45s %-15s %-12s\n" "${description}" "NO LOG" "N/A"
        fi
    done

    echo "=============================================================================="
    echo ""

    # Performance metrics section
    echo "------------------------------------------------------------------------------"
    echo "Performance Metrics (Extracted from Logs)"
    echo "------------------------------------------------------------------------------"
    echo ""

    for config in "${CONFIGS[@]}"; do
        test_name=$(echo "$config" | cut -d: -f1)
        description=$(echo "$config" | cut -d: -f4)
        log_file="${OUTPUT_DIR}/${test_name}.log"

        if [ -f "${log_file}" ] && grep -q "Transfer completed" "${log_file}"; then
            echo "Configuration: ${description}"

            # Extract performance metrics from log
            grep "Transfer completed in" "${log_file}" | head -1 || echo "  Duration: N/A"

            # Look for throughput info (if testbench logs it)
            grep -i "throughput\|bandwidth\|beats.*cycle\|efficiency" "${log_file}" || echo "  (No detailed metrics in log)"

            echo ""
        fi
    done

    echo "=============================================================================="
    echo ""
    echo "Notes:"
    echo "  - 'fast' timing profile = no artificial delays (BFMs respond immediately)"
    echo "  - Metrics represent ideal performance under no-stress conditions"
    echo "  - Real-world performance depends on memory latency and system load"
    echo ""
    echo "=============================================================================="

} | tee "${REPORT_FILE}"

echo ""
echo "Performance profiling complete!"
echo "Report saved to: ${REPORT_FILE}"
echo ""
echo "Individual test logs:"
ls -lh "${OUTPUT_DIR}"/*.log 2>/dev/null || echo "  (none generated)"
echo ""
