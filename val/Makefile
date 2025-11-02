# ==============================================================================
# RTL Design Sherpa - Master Validation Makefile
# ==============================================================================
#
# PREREQUISITES:
#   Must be run with sourced environment:
#     source $REPO_ROOT/env_python  # Sets $REPO_ROOT and activates venv
#     cd $REPO_ROOT/val
#     make <target>
#
# Quick start:
#   make help           - Show all available targets
#   make run-all        - Run ALL validation tests (all 4 areas)
#   make run-amba       - Run all AMBA tests
#   make run-common     - Run all COMMON tests
#   make clean-all      - Clean all validation artifacts
#
# Advanced:
#   make status         - Show test counts for all areas
#   make collect-all    - Collect all tests (verify imports)
#
# ==============================================================================

# Force bash shell (required for source command)
SHELL := /bin/bash

# Check if REPO_ROOT is set (from env_python)
ifndef REPO_ROOT
$(error REPO_ROOT is not set. Please run: source $$REPO_ROOT/env_python)
endif

# Repository root comes from environment (set by env_python)
# No path calculation needed - works from any project location!

# Test area directories
AMBA_DIR = amba
COMMON_DIR = common
INTEG_AMBA_DIR = integ_amba
INTEG_COMMON_DIR = integ_common

# Pytest options
PYTEST = python3 -m pytest
PYTEST_VERBOSE = -v
PYTEST_QUIET = -q
PYTEST_XDIST = -n logical # parallel workers
PYTEST_TBSTYLE = --tb=short

# Default target - show help
.DEFAULT_GOAL := help

# ==============================================================================
# Help Target
# ==============================================================================

.PHONY: help
help:
	@echo "================================================================================"
	@echo "RTL Design Sherpa - Master Validation Makefile"
	@echo "================================================================================"
	@echo ""
	@echo "RUN TARGETS (All Tests):"
	@echo "  make run-all              Run ALL validation tests (all 4 areas)"
	@echo "  make run-all-parallel     Run ALL tests in parallel"
	@echo ""
	@echo "RUN TARGETS (By Area):"
	@echo "  make run-amba                      Run all AMBA tests"
	@echo "  make run-common                    Run all COMMON tests"
	@echo "  make run-integ-amba                Run AMBA integration tests"
	@echo "  make run-integ-common              Run COMMON integration tests"
	@echo ""
	@echo "  make run-amba-parallel             Run all AMBA tests, parallel"
	@echo "  make run-common-parallel           Run all COMMON tests, parallel"
	@echo "  make run-integ-amba-parallel       Run AMBA integration tests, parallel"
	@echo "  make run-integ-common-parallel     Run COMMON integration tests, parallel"
	@echo ""
	@echo "CLEAN TARGETS (All Areas):"
	@echo "  make clean-all            Clean all validation artifacts"
	@echo "  make clean-logs           Clean all log files"
	@echo "  make clean-build          Clean all build directories"
	@echo "  make clean-vcd            Clean all waveform files"
	@echo ""
	@echo "CLEAN TARGETS (By Area):"
	@echo "  make clean-amba           Clean AMBA test artifacts"
	@echo "  make clean-common         Clean COMMON test artifacts"
	@echo "  make clean-integ-amba     Clean AMBA integration artifacts"
	@echo "  make clean-integ-common   Clean COMMON integration artifacts"
	@echo ""
	@echo "COLLECTION TARGETS (verify tests, don't run):"
	@echo "  make collect-all          Collect all tests (all 4 areas)"
	@echo "  make collect-amba         Collect AMBA tests"
	@echo "  make collect-common       Collect COMMON tests"
	@echo ""
	@echo "UTILITY TARGETS:"
	@echo "  make status               Show test status for all areas"
	@echo "  make list-all             List all test modules"
	@echo ""
	@echo "COMBINED TARGETS:"
	@echo "  make fresh-all            Clean + run all tests"
	@echo "  make fresh-amba           Clean + run AMBA tests"
	@echo "  make fresh-common         Clean + run COMMON tests"
	@echo ""
	@echo "================================================================================"
	@echo "Test Areas (4 total):"
	@echo "  1. amba/         - AMBA protocol tests (AXI4, APB, AXIS)"
	@echo "  2. common/       - Common building blocks (counters, FIFOs, arbiters)"
	@echo "  3. integ_amba/   - AMBA integration tests"
	@echo "  4. integ_common/ - COMMON integration tests"
	@echo "================================================================================"
	@echo "Prerequisites: source $(REPO_ROOT)/env_python"
	@echo "Current REPO_ROOT: $(REPO_ROOT)"
	@echo "================================================================================"

# ==============================================================================
# Run Targets - All Tests
# ==============================================================================

.PHONY: run-all
run-all:
	@echo "================================================================================"
	@echo "Running ALL Validation Tests (4 areas)"
	@echo "================================================================================"
	@echo ""
	@echo "=== Area 1/4: AMBA ==="
	@$(MAKE) -C $(AMBA_DIR) run-all || true
	@echo ""
	@echo "=== Area 2/4: COMMON ==="
	@$(MAKE) -C $(COMMON_DIR) run-all || true
	@echo ""
	@echo "=== Area 3/4: AMBA Integration ==="
	@$(MAKE) -C $(INTEG_AMBA_DIR) run-all || true
	@echo ""
	@echo "=== Area 4/4: COMMON Integration ==="
	@$(MAKE) -C $(INTEG_COMMON_DIR) run-all || true
	@echo ""
	@echo "================================================================================"
	@echo "✓ All validation test runs complete"
	@echo "================================================================================"

.PHONY: run-all-parallel
run-all-parallel:
	@echo "================================================================================"
	@echo "Running ALL Validation Tests (Parallel - 4 workers per area)"
	@echo "================================================================================"
	@echo ""
	@echo "=== Area 1/4: AMBA ==="
	@$(MAKE) -C $(AMBA_DIR) run-all-parallel || true
	@echo ""
	@echo "=== Area 2/4: COMMON ==="
	@$(MAKE) -C $(COMMON_DIR) run-all-parallel || true
	@echo ""
	@echo "=== Area 3/4: AMBA Integration ==="
	@$(MAKE) -C $(INTEG_AMBA_DIR) run-all-parallel || true
	@echo ""
	@echo "=== Area 4/4: COMMON Integration ==="
	@$(MAKE) -C $(INTEG_COMMON_DIR) run-all-parallel || true
	@echo ""
	@echo "================================================================================"
	@echo "✓ All parallel validation test runs complete"
	@echo "================================================================================"

# ==============================================================================
# Run Targets - By Area
# ==============================================================================

.PHONY: run-amba
run-amba:
	@echo "Running AMBA tests..."
	@$(MAKE) -C $(AMBA_DIR) run-all

.PHONY: run-common
run-common:
	@echo "Running COMMON tests..."
	@$(MAKE) -C $(COMMON_DIR) run-all

.PHONY: run-integ-amba
run-integ-amba:
	@echo "Running AMBA integration tests..."
	@$(MAKE) -C $(INTEG_AMBA_DIR) run-all

.PHONY: run-integ-common
run-integ-common:
	@echo "Running COMMON integration tests..."
	@$(MAKE) -C $(INTEG_COMMON_DIR) run-all

.PHONY: run-amba-parallel
run-amba:
	@echo "Running AMBA tests..."
	@$(MAKE) -C $(AMBA_DIR) run-all-parallel

.PHONY: run-common-parallel
run-common:
	@echo "Running COMMON tests..."
	@$(MAKE) -C $(COMMON_DIR) run-all-parallel

.PHONY: run-integ-amba-parallel
run-integ-amba:
	@echo "Running AMBA integration tests..."
	@$(MAKE) -C $(INTEG_AMBA_DIR) run-all-parallel

.PHONY: run-integ-common-parallel
run-integ-common:
	@echo "Running COMMON integration tests..."
	@$(MAKE) -C $(INTEG_COMMON_DIR) run-all-parallel

# ==============================================================================
# Clean Targets - All Areas
# ==============================================================================

.PHONY: clean-all
clean-all:
	@echo "================================================================================"
	@echo "Cleaning ALL Validation Artifacts (4 areas)"
	@echo "================================================================================"
	@echo ""
	@echo "=== Cleaning AMBA ==="
	@$(MAKE) -C $(AMBA_DIR) clean-all || true
	@echo ""
	@echo "=== Cleaning COMMON ==="
	@$(MAKE) -C $(COMMON_DIR) clean-all || true
	@echo ""
	@echo "=== Cleaning AMBA Integration ==="
	@$(MAKE) -C $(INTEG_AMBA_DIR) clean-all || true
	@echo ""
	@echo "=== Cleaning COMMON Integration ==="
	@$(MAKE) -C $(INTEG_COMMON_DIR) clean-all || true
	@echo ""
	@echo "================================================================================"
	@echo "✓ All validation artifacts cleaned"
	@echo "================================================================================"

.PHONY: clean-logs
clean-logs:
	@echo "Cleaning all log files..."
	@$(MAKE) -C $(AMBA_DIR) clean-logs || true
	@$(MAKE) -C $(COMMON_DIR) clean-logs || true
	@$(MAKE) -C $(INTEG_AMBA_DIR) clean-logs || true
	@$(MAKE) -C $(INTEG_COMMON_DIR) clean-logs || true
	@echo "✓ All log files cleaned"

.PHONY: clean-build
clean-build:
	@echo "Cleaning all build directories..."
	@$(MAKE) -C $(AMBA_DIR) clean-build || true
	@$(MAKE) -C $(COMMON_DIR) clean-build || true
	@$(MAKE) -C $(INTEG_AMBA_DIR) clean-build || true
	@$(MAKE) -C $(INTEG_COMMON_DIR) clean-build || true
	@echo "✓ All build directories cleaned"

.PHONY: clean-vcd
clean-vcd:
	@echo "Cleaning all waveform files..."
	@$(MAKE) -C $(AMBA_DIR) clean-vcd || true
	@$(MAKE) -C $(COMMON_DIR) clean-vcd || true
	@$(MAKE) -C $(INTEG_AMBA_DIR) clean-vcd || true
	@$(MAKE) -C $(INTEG_COMMON_DIR) clean-vcd || true
	@echo "✓ All waveform files cleaned"

# ==============================================================================
# Clean Targets - By Area
# ==============================================================================

.PHONY: clean-amba
clean-amba:
	@echo "Cleaning AMBA test artifacts..."
	@$(MAKE) -C $(AMBA_DIR) clean-all

.PHONY: clean-common
clean-common:
	@echo "Cleaning COMMON test artifacts..."
	@$(MAKE) -C $(COMMON_DIR) clean-all

.PHONY: clean-integ-amba
clean-integ-amba:
	@echo "Cleaning AMBA integration test artifacts..."
	@$(MAKE) -C $(INTEG_AMBA_DIR) clean-all

.PHONY: clean-integ-common
clean-integ-common:
	@echo "Cleaning COMMON integration test artifacts..."
	@$(MAKE) -C $(INTEG_COMMON_DIR) clean-all

# ==============================================================================
# Collection Targets (verify tests without running)
# ==============================================================================

.PHONY: collect-all
collect-all:
	@echo "================================================================================"
	@echo "Collecting ALL Validation Tests (4 areas)"
	@echo "================================================================================"
	@echo ""
	@echo "=== AMBA ==="
	@$(MAKE) -C $(AMBA_DIR) collect-all || true
	@echo ""
	@echo "=== COMMON ==="
	@$(MAKE) -C $(COMMON_DIR) collect-all || true
	@echo ""
	@echo "=== AMBA Integration ==="
	@$(MAKE) -C $(INTEG_AMBA_DIR) collect-all || true
	@echo ""
	@echo "=== COMMON Integration ==="
	@$(MAKE) -C $(INTEG_COMMON_DIR) collect-all || true
	@echo ""
	@echo "================================================================================"
	@echo "✓ All validation test collections complete"
	@echo "================================================================================"

.PHONY: collect-amba
collect-amba:
	@echo "Collecting AMBA tests..."
	@$(MAKE) -C $(AMBA_DIR) collect-all

.PHONY: collect-common
collect-common:
	@echo "Collecting COMMON tests..."
	@$(MAKE) -C $(COMMON_DIR) collect-all

# ==============================================================================
# Utility Targets
# ==============================================================================

.PHONY: status
status:
	@echo "================================================================================"
	@echo "RTL Design Sherpa - Validation Test Status"
	@echo "================================================================================"
	@echo ""
	@echo "=== AMBA Tests ==="
	@$(MAKE) -C $(AMBA_DIR) status 2>/dev/null | grep -A 20 "Test modules found:" || echo "  (Makefile not found)"
	@echo ""
	@echo "=== COMMON Tests ==="
	@$(MAKE) -C $(COMMON_DIR) status 2>/dev/null | grep -A 20 "Test modules found:" || echo "  (Makefile not found)"
	@echo ""
	@echo "=== AMBA Integration ==="
	@$(MAKE) -C $(INTEG_AMBA_DIR) status 2>/dev/null | grep -A 10 "Test modules found:" || echo "  (Makefile not found)"
	@echo ""
	@echo "=== COMMON Integration ==="
	@$(MAKE) -C $(INTEG_COMMON_DIR) status 2>/dev/null | grep -A 10 "Test modules found:" || echo "  (Makefile not found)"
	@echo ""
	@echo "================================================================================"
	@echo "Python environment:"
	@echo "  REPO_ROOT: $(REPO_ROOT)"
	@echo "  Virtual env: $(REPO_ROOT)/env_python"
	@echo "================================================================================"

.PHONY: list-all
list-all:
	@echo "================================================================================"
	@echo "All Validation Test Modules"
	@echo "================================================================================"
	@echo ""
	@echo "=== AMBA Tests ==="
	@$(MAKE) -C $(AMBA_DIR) list-all 2>/dev/null || echo "  (Makefile not found)"
	@echo ""
	@echo "=== COMMON Tests ==="
	@$(MAKE) -C $(COMMON_DIR) list-all 2>/dev/null || echo "  (Makefile not found)"
	@echo ""
	@echo "=== AMBA Integration ==="
	@$(MAKE) -C $(INTEG_AMBA_DIR) list-all 2>/dev/null || echo "  (Makefile not found)"
	@echo ""
	@echo "=== COMMON Integration ==="
	@$(MAKE) -C $(INTEG_COMMON_DIR) list-all 2>/dev/null || echo "  (Makefile not found)"
	@echo ""

# ==============================================================================
# Combined Targets (clean + run)
# ==============================================================================

.PHONY: fresh-all
fresh-all: clean-all run-all
	@echo "✓ Fresh all validation tests complete"

.PHONY: fresh-amba
fresh-amba: clean-amba run-amba
	@echo "✓ Fresh AMBA test run complete"

.PHONY: fresh-common
fresh-common: clean-common run-common
	@echo "✓ Fresh COMMON test run complete"

# ==============================================================================
# Quick Aliases
# ==============================================================================

.PHONY: amba
amba: run-amba

.PHONY: common
common: run-common

.PHONY: all
all: run-all

.PHONY: clean
clean: clean-all

.PHONY: collect
collect: collect-all

.PHONY: list
list: list-all

# ==============================================================================
# End of Makefile
# ==============================================================================
