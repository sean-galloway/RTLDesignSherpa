# ==============================================================================
# AXI4 Bridge Test Makefile
# ==============================================================================
#
# PREREQUISITES:
#   Must be run with sourced environment:
#     source $REPO_ROOT/env_python  # Sets $REPO_ROOT and activates venv
#     cd $REPO_ROOT/projects/components/bridge/dv/tests
#     make <target>
#
# Quick start:
#   make help           - Show all available targets
#   make run-all        - Run all AXI4 bridge tests (REG_LEVEL=FUNC)
#   make run-all-full   - Run comprehensive tests (REG_LEVEL=FULL)
#   make clean-all      - Clean all test artifacts
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

# Pytest options
PYTEST = python3 -m pytest
PYTEST_VERBOSE = -v
PYTEST_QUIET = -q
PYTEST_XDIST = -n 48  # 48 parallel workers (matching AMBA/STREAM/RAPIDS)
PYTEST_TBSTYLE = --tb=short
PYTEST_RERUNS = --reruns 3 --reruns-delay 1  # Retry failed tests up to 3 times

# Default target - show help
.DEFAULT_GOAL := help

# ==============================================================================
# Help Target
# ==============================================================================

.PHONY: help
help:
	@echo "================================================================================"
	@echo "AXI4 Bridge Test Makefile - Available Targets"
	@echo "================================================================================"
	@echo ""
	@echo "OVERVIEW:"
	@echo "  AXI4 Bridge - Configurable NxM crossbar for AXI4 interconnect"
	@echo "  Features: ID-based routing, round-robin arbitration, 5-channel"
	@echo ""
	@echo "REG_LEVEL CONTROL:"
	@echo "  REG_LEVEL environment variable controls test depth:"
	@echo "    GATE: Quick smoke test (~5 min)  - Basic connectivity"
	@echo "    FUNC: Functional coverage (~30 min, DEFAULT) - Full validation"
	@echo "    FULL: Comprehensive validation (~4 hr) - Stress tests, edge cases"
	@echo ""
	@echo "RUN TARGETS:"
	@echo "  make run-all              Run all tests (REG_LEVEL=FUNC, serial)"
	@echo "  make run-all-parallel     Run all tests (REG_LEVEL=FUNC, 48 workers)"
	@echo ""
	@echo "  make run-all-gate         Run gate level tests (quick smoke)"
	@echo "  make run-all-gate-parallel Run gate tests (parallel)"
	@echo ""
	@echo "  make run-all-func         Run functional tests (default level)"
	@echo "  make run-all-func-parallel Run functional tests (parallel)"
	@echo ""
	@echo "  make run-all-full         Run full tests (comprehensive)"
	@echo "  make run-all-full-parallel Run full tests (parallel)"
	@echo ""
	@echo "INDIVIDUAL TEST TARGETS:"
	@echo "  make run-bridge           Run bridge tests (REG_LEVEL=FUNC)"
	@echo "  make run-bridge-gate      Run bridge tests (REG_LEVEL=GATE)"
	@echo "  make run-bridge-func      Run bridge tests (REG_LEVEL=FUNC)"
	@echo "  make run-bridge-full      Run bridge tests (REG_LEVEL=FULL)"
	@echo ""
	@echo "COLLECTION TARGETS (verify tests, don't run):"
	@echo "  make collect-all          Collect all tests"
	@echo ""
	@echo "CLEAN TARGETS:"
	@echo "  make clean-all            Remove all test artifacts"
	@echo "  make clean-logs           Remove all log files"
	@echo "  make clean-pycache        Remove Python cache files"
	@echo "  make clean-build          Remove simulation build directories"
	@echo "  make clean-vcd            Remove VCD waveform files"
	@echo ""
	@echo "UTILITY TARGETS:"
	@echo "  make list-all             List all test modules"
	@echo "  make status               Show test status and coverage"
	@echo ""
	@echo "EXAMPLES:"
	@echo "  make run-all-parallel          # Default: FUNC level, 48 workers"
	@echo "  make run-all-gate-parallel     # Quick smoke test, 48 workers"
	@echo "  make run-all-full-parallel     # Comprehensive test, 48 workers"
	@echo "  make run-bridge-func           # Single test, FUNC level"
	@echo ""
	@echo "================================================================================"
	@echo "Prerequisites: source $(REPO_ROOT)/env_python"
	@echo "Current REPO_ROOT: $(REPO_ROOT)"
	@echo "================================================================================"

# ==============================================================================
# REG_LEVEL Control for All Tests
# ==============================================================================

.PHONY: run-all-gate
run-all-gate:
	@echo "================================================================================"
	@echo "Running AXI4 Bridge Tests - GATE level (quick smoke test)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-gate-parallel
run-all-gate-parallel:
	@echo "================================================================================"
	@echo "Running AXI4 Bridge Tests - GATE level (parallel, 48 workers)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_*.py

.PHONY: run-all-func
run-all-func:
	@echo "================================================================================"
	@echo "Running AXI4 Bridge Tests - FUNC level (functional coverage)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-func-parallel
run-all-func-parallel:
	@echo "================================================================================"
	@echo "Running AXI4 Bridge Tests - FUNC level (parallel, 48 workers)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_*.py

.PHONY: run-all-full
run-all-full:
	@echo "================================================================================"
	@echo "Running AXI4 Bridge Tests - FULL level (comprehensive validation)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-full-parallel
run-all-full-parallel:
	@echo "================================================================================"
	@echo "Running AXI4 Bridge Tests - FULL level (parallel, 48 workers)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_*.py

# ==============================================================================
# Individual Test Targets (Bridge)
# ==============================================================================

.PHONY: run-bridge
run-bridge:
	@echo "Running AXI4 bridge tests (REG_LEVEL=FUNC)..."
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-bridge-gate
run-bridge-gate:
	@echo "Running AXI4 bridge tests (REG_LEVEL=GATE)..."
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-bridge-func
run-bridge-func:
	@echo "Running AXI4 bridge tests (REG_LEVEL=FUNC)..."
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-bridge-full
run-bridge-full:
	@echo "Running AXI4 bridge tests (REG_LEVEL=FULL)..."
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

# ==============================================================================
# Legacy Run Targets (backwards compatibility)
# ==============================================================================

.PHONY: run-all
run-all:
	@echo "================================================================================"
	@echo "Running ALL AXI4 Bridge Tests (REG_LEVEL=FUNC, serial)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-parallel
run-all-parallel:
	@echo "================================================================================"
	@echo "Running ALL AXI4 Bridge Tests (REG_LEVEL=FUNC, parallel - 48 workers)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_*.py

# ==============================================================================
# Collection Targets (verify tests without running)
# ==============================================================================

.PHONY: collect-all
collect-all:
	@echo "Collecting ALL AXI4 bridge tests..."
	$(PYTEST) --collect-only test_*.py

# ==============================================================================
# Clean Targets
# ==============================================================================

.PHONY: clean-logs
clean-logs:
	@echo "Cleaning all log files..."
	rm -rf logs/
	find . -type f -name "*.log" -delete
	@echo "✓ Log files cleaned"

.PHONY: clean-pycache
clean-pycache:
	@echo "Cleaning Python cache files..."
	find . -type d -name "__pycache__" -exec rm -rf {} + 2>/dev/null || true
	find . -type f -name "*.pyc" -delete
	@echo "✓ Python cache cleaned"

.PHONY: clean-build
clean-build:
	@echo "Cleaning simulation build directories..."
	rm -rf local_sim_build/
	rm -rf sim_build/
	find . -type d -name "local_sim_build" -exec rm -rf {} + 2>/dev/null || true
	find . -type d -name "sim_build" -exec rm -rf {} + 2>/dev/null || true
	@echo "✓ Build directories cleaned"

.PHONY: clean-vcd
clean-vcd:
	@echo "Cleaning VCD waveform files..."
	find . -type f -name "*.vcd" -delete
	find . -type f -name "*.fst" -delete
	@echo "✓ Waveform files cleaned"

.PHONY: clean-all
clean-all: clean-logs clean-pycache clean-build clean-vcd
	@echo "================================================================================"
	@echo "✓ All AXI4 bridge test artifacts cleaned"
	@echo "================================================================================"

# ==============================================================================
# Utility Targets
# ==============================================================================

.PHONY: list-all
list-all:
	@echo "All AXI4 Bridge Test Modules:"
	@ls test_*.py 2>/dev/null | sort

.PHONY: status
status:
	@echo "================================================================================"
	@echo "AXI4 Bridge Test Status"
	@echo "================================================================================"
	@echo "Test directories:"
	@echo "  BRIDGE Tests:  $(REPO_ROOT)/projects/components/bridge/dv/tests/"
	@echo ""
	@echo "Test modules found:"
	@echo -n "  Total:       "
	@ls test_*.py 2>/dev/null | wc -l
	@echo ""
	@echo "Build artifacts:"
	@echo -n "  local_sim_build dirs: "
	@find . -type d -name "local_sim_build" 2>/dev/null | wc -l
	@echo -n "  Log files:            "
	@find . -type f -name "*.log" 2>/dev/null | wc -l
	@echo -n "  VCD files:            "
	@find . -type f -name "*.vcd" 2>/dev/null | wc -l
	@echo ""
	@echo "Python environment:"
	@echo "  REPO_ROOT: $(REPO_ROOT)"
	@echo "  Virtual env: $(REPO_ROOT)/env_python"
	@echo ""
	@echo "Test Coverage Summary:"
	@echo "  NxM crossbar validation with ID-based routing"
	@echo "  Round-robin arbitration per slave"
	@echo "================================================================================"

# ==============================================================================
# Combined Targets (clean + run)
# ==============================================================================

.PHONY: fresh-all
fresh-all: clean-all run-all
	@echo "✓ Fresh all tests run complete"

.PHONY: fresh-all-parallel
fresh-all-parallel: clean-all run-all-parallel
	@echo "✓ Fresh all tests (parallel) run complete"

# ==============================================================================
# Quick Aliases
# ==============================================================================

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
