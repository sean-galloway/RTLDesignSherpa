#!/bin/bash
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - RAPIDS RTL Comprehensive Lint Script
# Runs Verilator, Verible, and Yosys on all RAPIDS RTL modules
#
# Usage: ./bin/lint_rapids.sh

set -e  # Exit on error

REPO_ROOT="/mnt/data/github/rtldesignsherpa"
RAPIDS_RTL="$REPO_ROOT/projects/components/rapids/rtl"
RAPIDS_REPORTS="$REPO_ROOT/projects/components/rapids/reports/lint"

# Tool paths
VERILATOR="verilator"
VERIBLE="verible-verilog-lint"
YOSYS="${REPO_ROOT}/venv/bin/yowasp-yosys"

# Common include paths for all tools
INCLUDES="-I$RAPIDS_RTL/includes \
          -I$REPO_ROOT/rtl/amba/includes \
          -I$REPO_ROOT/rtl/amba/gaxi \
          -I$REPO_ROOT/rtl/common \
          -I$RAPIDS_RTL/rapids_fub"

# Package files (needed for most modules)
MON_PKG="$REPO_ROOT/rtl/amba/includes/monitor_pkg.sv"
RAPIDS_PKG="$RAPIDS_RTL/includes/rapids_pkg.sv"
PACKAGES="$MON_PKG $RAPIDS_PKG"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

echo -e "${BLUE}========================================${NC}"
echo -e "${BLUE}RAPIDS RTL Comprehensive Lint${NC}"
echo -e "${BLUE}========================================${NC}"
echo ""

# Clean up old reports
echo -e "${YELLOW}Cleaning up old reports...${NC}"
rm -rf "$RAPIDS_REPORTS"
mkdir -p "$RAPIDS_REPORTS/verilator"
mkdir -p "$RAPIDS_REPORTS/verible"
mkdir -p "$RAPIDS_REPORTS/yosys"
echo -e "${GREEN}✓ Reports directory cleaned: $RAPIDS_REPORTS${NC}"
echo ""

# Function to check if tool exists
check_tool() {
    local tool=$1
    local name=$2
    if [ -x "$tool" ] || command -v "$tool" &> /dev/null; then
        echo -e "${GREEN}✓ $name found${NC}"
        return 0
    else
        echo -e "${RED}✗ $name not found${NC}"
        return 1
    fi
}

# Check all tools
echo -e "${BLUE}Checking lint tools...${NC}"
VERILATOR_AVAILABLE=0
VERIBLE_AVAILABLE=0
YOSYS_AVAILABLE=0

check_tool "$VERILATOR" "Verilator" && VERILATOR_AVAILABLE=1 || true
check_tool "$VERIBLE" "Verible" && VERIBLE_AVAILABLE=1 || true
check_tool "$YOSYS" "Yosys" && YOSYS_AVAILABLE=1 || true
echo ""

if [ $VERILATOR_AVAILABLE -eq 0 ] && [ $VERIBLE_AVAILABLE -eq 0 ] && [ $YOSYS_AVAILABLE -eq 0 ]; then
    echo -e "${RED}ERROR: No lint tools found!${NC}"
    exit 1
fi

# Function to lint a single module with Verilator
lint_verilator() {
    local module_path=$1
    local module_name=$(basename "$module_path" .sv)
    local report_file="$RAPIDS_REPORTS/verilator/${module_name}.txt"

    # Check if module needs packages
    local cmd="$VERILATOR --lint-only -Wall $INCLUDES"

    if grep -q "rapids_imports.svh" "$module_path" 2>/dev/null; then
        cmd="$cmd $PACKAGES"
    elif grep -q "import monitor_pkg" "$module_path" 2>/dev/null; then
        cmd="$cmd $MON_PKG"
    fi

    cmd="$cmd $module_path"

    # Run verilator
    $cmd 2>&1 > "$report_file" || true

    # Count warnings and errors
    local warnings=$(grep -c "^%Warning" "$report_file" 2>/dev/null || echo "0")
    local errors=$(grep -c "^%Error" "$report_file" 2>/dev/null || echo "0")

    if [ "$errors" -gt 0 ]; then
        echo -e "  ${RED}✗${NC} $module_name - Errors: $errors, Warnings: $warnings"
        return 1
    elif [ "$warnings" -gt 0 ]; then
        echo -e "  ${YELLOW}⚠${NC} $module_name - Warnings: $warnings"
        return 0
    else
        echo -e "  ${GREEN}✓${NC} $module_name - Clean"
        return 0
    fi
}

# Function to lint a single module with Verible
lint_verible() {
    local module_path=$1
    local module_name=$(basename "$module_path" .sv)
    local report_file="$RAPIDS_REPORTS/verible/${module_name}.txt"

    # Run verible
    $VERIBLE "$module_path" 2>&1 > "$report_file" || true

    # Count issues (any line that contains file:line:col pattern)
    local issues=0
    if [ -s "$report_file" ]; then
        issues=$(grep -c "^.*:[0-9]" "$report_file" 2>/dev/null || echo "0")
    fi

    if [ "$issues" -gt 0 ]; then
        echo -e "  ${YELLOW}⚠${NC} $module_name - Style issues: $issues"
        return 0
    else
        echo -e "  ${GREEN}✓${NC} $module_name - Clean"
        return 0
    fi
}

# Function to lint a single module with Yosys
lint_yosys() {
    local module_path=$1
    local module_name=$(basename "$module_path" .sv)
    local report_file="$RAPIDS_REPORTS/yosys/${module_name}.txt"

    # Yosys needs include paths specified differently
    local yosys_includes="-I$RAPIDS_RTL/includes -I$REPO_ROOT/rtl/amba/includes"

    # Run yosys with include paths
    $YOSYS -Q $yosys_includes -p "read_verilog -sv $module_path; proc;" 2>&1 > "$report_file" || true

    # Check for errors (only real errors, not warnings about includes)
    local errors=0
    if grep -q "ERROR:" "$report_file" 2>/dev/null; then
        # Filter out "Can't open include file" errors (false positives due to Yosys limitations)
        errors=$(grep "ERROR:" "$report_file" | grep -v "Can't open include file" | wc -l || echo "0")
    fi

    if [ "$errors" -gt 0 ]; then
        echo -e "  ${RED}✗${NC} $module_name - Syntax errors: $errors"
        return 1
    else
        echo -e "  ${GREEN}✓${NC} $module_name - Clean"
        return 0
    fi
}

# Counters
total_modules=0
verilator_errors=0
verible_issues=0
yosys_errors=0

# Get all RAPIDS modules
rapids_modules=($(find "$RAPIDS_RTL/rapids_fub" "$RAPIDS_RTL/rapids_macro" -name "*.sv" -type f | sort))
total_modules=${#rapids_modules[@]}

echo -e "${BLUE}Found $total_modules RAPIDS modules${NC}"
echo ""

# Run Verilator
if [ $VERILATOR_AVAILABLE -eq 1 ]; then
    echo -e "${BLUE}=== Running Verilator ===${NC}"
    for module in "${rapids_modules[@]}"; do
        lint_verilator "$module" || ((verilator_errors++))
    done
    echo ""
fi

# Run Verible
if [ $VERIBLE_AVAILABLE -eq 1 ]; then
    echo -e "${BLUE}=== Running Verible ===${NC}"
    for module in "${rapids_modules[@]}"; do
        lint_verible "$module"
    done
    echo ""
fi

# Run Yosys
if [ $YOSYS_AVAILABLE -eq 1 ]; then
    echo -e "${BLUE}=== Running Yosys ===${NC}"
    for module in "${rapids_modules[@]}"; do
        lint_yosys "$module" || ((yosys_errors++))
    done
    echo ""
fi

# Generate summary report
SUMMARY_FILE="$RAPIDS_REPORTS/SUMMARY.txt"
{
    echo "RAPIDS RTL Lint Summary"
    echo "======================="
    echo "Date: $(date)"
    echo "Total modules: $total_modules"
    echo ""
    echo "Results:"
    echo "--------"

    if [ $VERILATOR_AVAILABLE -eq 1 ]; then
        echo "Verilator - Modules with errors: $verilator_errors"
    fi

    if [ $VERIBLE_AVAILABLE -eq 1 ]; then
        echo "Verible   - Modules with style issues: (see individual reports)"
    fi

    if [ $YOSYS_AVAILABLE -eq 1 ]; then
        echo "Yosys     - Modules with syntax errors: $yosys_errors"
    fi

    echo ""
    echo "Reports Location:"
    echo "----------------"
    echo "Verilator: $RAPIDS_REPORTS/verilator/"
    echo "Verible:   $RAPIDS_REPORTS/verible/"
    echo "Yosys:     $RAPIDS_REPORTS/yosys/"
    echo ""
    echo "Module List:"
    echo "-----------"
    for module in "${rapids_modules[@]}"; do
        echo "  - $(basename "$module")"
    done
} > "$SUMMARY_FILE"

# Print summary
echo -e "${BLUE}========================================${NC}"
echo -e "${BLUE}Lint Summary${NC}"
echo -e "${BLUE}========================================${NC}"
echo -e "Total modules:              $total_modules"

if [ $VERILATOR_AVAILABLE -eq 1 ]; then
    if [ $verilator_errors -eq 0 ]; then
        echo -e "Verilator errors:           ${GREEN}0${NC}"
    else
        echo -e "Verilator errors:           ${RED}$verilator_errors${NC}"
    fi
fi

if [ $YOSYS_AVAILABLE -eq 1 ]; then
    if [ $yosys_errors -eq 0 ]; then
        echo -e "Yosys syntax errors:        ${GREEN}0${NC}"
    else
        echo -e "Yosys syntax errors:        ${RED}$yosys_errors${NC}"
    fi
fi

echo ""
echo -e "${GREEN}Reports saved to:${NC} $RAPIDS_REPORTS"
echo -e "${GREEN}Summary:${NC} $SUMMARY_FILE"
echo ""

# Exit with error if any critical issues found
if [ $verilator_errors -gt 0 ] || [ $yosys_errors -gt 0 ]; then
    echo -e "${RED}⚠ Critical issues found - see reports for details${NC}"
    exit 1
else
    echo -e "${GREEN}✓ No critical errors found${NC}"
    exit 0
fi
