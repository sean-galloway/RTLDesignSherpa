# ==============================================================================
# RAPIDS Subsystem Test Makefile
# ==============================================================================
#
# PREREQUISITES:
#   Must be run with sourced environment:
#     source $REPO_ROOT/env_python  # Sets $REPO_ROOT and activates venv
#     cd $REPO_ROOT/projects/components/rapids/dv/tests
#     make <target>
#
# Quick start:
#   make help           - Show all available targets
#   make run-fub        - Run all FUB tests
#   make run-macro      - Run all macro tests
#   make run-system     - Run all system tests
#   make run-all        - Run all tests
#   make clean-all      - Clean all test artifacts
#
# Advanced:
#   make run-fub-parallel   - Run FUB tests in parallel (48 workers)
#   make run-fub-gate       - Run FUB tests at GATE level
#   make run-fub-func       - Run FUB tests at FUNC level (default)
#   make run-fub-full       - Run FUB tests at FULL level
#   make collect-fub        - Collect (don't run) FUB tests
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

# Test directories (flattened structure - all tests at top level)
FUB_TESTS_DIR = fub_tests
MACRO_TESTS_DIR = macro_tests
SYSTEM_TESTS_DIR = system_tests

# Pytest options
PYTEST = python3 -m pytest
PYTEST_VERBOSE = -v
PYTEST_QUIET = -q
PYTEST_XDIST = -n 48  # 48 parallel workers (matching AMBA)
PYTEST_TBSTYLE = --tb=short
PYTEST_RERUNS = --reruns 3 --reruns-delay 1  # Retry failed tests

# Default target - show help
.DEFAULT_GOAL := help

# ==============================================================================
# Help Target
# ==============================================================================

.PHONY: help
help:
	@echo "================================================================================"
	@echo "RAPIDS Test Makefile - Available Targets"
	@echo "================================================================================"
	@echo ""
	@echo "RUN TARGETS (by Test Type):"
	@echo "  make run-fub              Run all FUB (Functional Unit Block) tests"
	@echo "  make run-fub-parallel     Run FUB tests in parallel (48 workers)"
	@echo "  make run-macro            Run all macro tests"
	@echo "  make run-macro-parallel   Run macro tests in parallel"
	@echo "  make run-system           Run all system tests"
	@echo "  make run-system-parallel  Run system tests in parallel"
	@echo "  make run-all              Run all tests (FUB + macro + system)"
	@echo "  make run-all-parallel     Run all tests in parallel"
	@echo ""
	@echo "REG_LEVEL TARGETS (configurable test depth):"
	@echo "  GATE = Quick smoke tests (~5 min), FUNC = Default (~30 min), FULL = Comprehensive (~4 hr)"
	@echo ""
	@echo "  FUB Tests:"
	@echo "    make run-fub-{gate|func|full}[-parallel]"
	@echo "  Macro Tests:"
	@echo "    make run-macro-{gate|func|full}[-parallel]"
	@echo "  System Tests:"
	@echo "    make run-system-{gate|func|full}[-parallel]"
	@echo "  ALL Tests:"
	@echo "    make run-all-{gate|func|full}[-parallel]"
	@echo ""
	@echo "DEVELOPMENT TARGETS (pytest-watch):"
	@echo "  make ptw-fub              Auto-rerun FUB tests on file changes"
	@echo "  make ptw-macro            Auto-rerun macro tests on file changes"
	@echo "  make ptw-system           Auto-rerun system tests on file changes"
	@echo ""
	@echo "COLLECTION TARGETS (verify tests, don't run):"
	@echo "  make collect-fub          Collect FUB tests (verify imports)"
	@echo "  make collect-macro        Collect macro tests"
	@echo "  make collect-system       Collect system tests"
	@echo "  make collect-all          Collect all tests"
	@echo ""
	@echo "CLEAN TARGETS:"
	@echo "  make clean-fub            Remove FUB test artifacts"
	@echo "  make clean-macro          Remove macro test artifacts"
	@echo "  make clean-system         Remove system test artifacts"
	@echo "  make clean-all            Remove all test artifacts"
	@echo "  make clean-logs           Remove all log files"
	@echo "  make clean-pycache        Remove Python cache files"
	@echo "  make clean-build          Remove simulation build directories"
	@echo "  make clean-vcd            Remove VCD waveform files"
	@echo ""
	@echo "UTILITY TARGETS:"
	@echo "  make list-fub             List all FUB test modules"
	@echo "  make list-macro           List all macro test modules"
	@echo "  make list-system          List all system test modules"
	@echo "  make status               Show test status and coverage"
	@echo ""
	@echo "================================================================================"
	@echo "Prerequisites: source $(REPO_ROOT)/env_python"
	@echo "Current REPO_ROOT: $(REPO_ROOT)"
	@echo "================================================================================"

# ==============================================================================
# Run Targets - FUB Tests
# ==============================================================================

.PHONY: run-fub
run-fub:
	@echo "================================================================================"
	@echo "Running RAPIDS FUB Tests (default FUNC level)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_*.py

.PHONY: run-fub-parallel
run-fub-parallel:
	@echo "================================================================================"
	@echo "Running RAPIDS FUB Tests (Parallel - 48 workers, default FUNC level)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(FUB_TESTS_DIR)/test_*.py

# REG_LEVEL Control for FUB Tests
.PHONY: run-fub-gate
run-fub-gate:
	@echo "================================================================================"
	@echo "Running RAPIDS FUB Tests - GATE level (quick smoke test)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_*.py

.PHONY: run-fub-func
run-fub-func:
	@echo "================================================================================"
	@echo "Running RAPIDS FUB Tests - FUNC level (functional coverage)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_*.py

.PHONY: run-fub-full
run-fub-full:
	@echo "================================================================================"
	@echo "Running RAPIDS FUB Tests - FULL level (comprehensive validation)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_*.py

# Parallel versions of REG_LEVEL targets
.PHONY: run-fub-gate-parallel
run-fub-gate-parallel:
	@echo "================================================================================"
	@echo "Running RAPIDS FUB Tests - GATE level PARALLEL (48 workers)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(FUB_TESTS_DIR)/test_*.py

.PHONY: run-fub-func-parallel
run-fub-func-parallel:
	@echo "================================================================================"
	@echo "Running RAPIDS FUB Tests - FUNC level PARALLEL (48 workers)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(FUB_TESTS_DIR)/test_*.py

.PHONY: run-fub-full-parallel
run-fub-full-parallel:
	@echo "================================================================================"
	@echo "Running RAPIDS FUB Tests - FULL level PARALLEL (48 workers)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(FUB_TESTS_DIR)/test_*.py

# ==============================================================================
# Run Targets - Macro Tests
# ==============================================================================

.PHONY: run-macro
run-macro:
	@echo "================================================================================"
	@echo "Running RAPIDS Macro Tests (default FUNC level)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(MACRO_TESTS_DIR)/test_*.py

.PHONY: run-macro-parallel
run-macro-parallel:
	@echo "================================================================================"
	@echo "Running RAPIDS Macro Tests (Parallel - 48 workers)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(MACRO_TESTS_DIR)/test_*.py

# REG_LEVEL Control for Macro Tests
.PHONY: run-macro-gate
run-macro-gate:
	@echo "================================================================================"
	@echo "Running RAPIDS Macro Tests - GATE level"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(MACRO_TESTS_DIR)/test_*.py

.PHONY: run-macro-func
run-macro-func:
	@echo "================================================================================"
	@echo "Running RAPIDS Macro Tests - FUNC level"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(MACRO_TESTS_DIR)/test_*.py

.PHONY: run-macro-full
run-macro-full:
	@echo "================================================================================"
	@echo "Running RAPIDS Macro Tests - FULL level"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(MACRO_TESTS_DIR)/test_*.py

# Parallel versions
.PHONY: run-macro-gate-parallel
run-macro-gate-parallel:
	@echo "================================================================================"
	@echo "Running RAPIDS Macro Tests - GATE level PARALLEL (48 workers)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(MACRO_TESTS_DIR)/test_*.py

.PHONY: run-macro-func-parallel
run-macro-func-parallel:
	@echo "================================================================================"
	@echo "Running RAPIDS Macro Tests - FUNC level PARALLEL (48 workers)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(MACRO_TESTS_DIR)/test_*.py

.PHONY: run-macro-full-parallel
run-macro-full-parallel:
	@echo "================================================================================"
	@echo "Running RAPIDS Macro Tests - FULL level PARALLEL (48 workers)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(MACRO_TESTS_DIR)/test_*.py

# ==============================================================================
# Run Targets - System Tests
# ==============================================================================

.PHONY: run-system
run-system:
	@echo "================================================================================"
	@echo "Running RAPIDS System Tests (default FUNC level)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(SYSTEM_TESTS_DIR)/test_*.py

.PHONY: run-system-parallel
run-system-parallel:
	@echo "================================================================================"
	@echo "Running RAPIDS System Tests (Parallel - 48 workers)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(SYSTEM_TESTS_DIR)/test_*.py

# REG_LEVEL Control for System Tests
.PHONY: run-system-gate
run-system-gate:
	@echo "================================================================================"
	@echo "Running RAPIDS System Tests - GATE level"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(SYSTEM_TESTS_DIR)/test_*.py

.PHONY: run-system-func
run-system-func:
	@echo "================================================================================"
	@echo "Running RAPIDS System Tests - FUNC level"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(SYSTEM_TESTS_DIR)/test_*.py

.PHONY: run-system-full
run-system-full:
	@echo "================================================================================"
	@echo "Running RAPIDS System Tests - FULL level"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(SYSTEM_TESTS_DIR)/test_*.py

# Parallel versions
.PHONY: run-system-gate-parallel
run-system-gate-parallel:
	@echo "================================================================================"
	@echo "Running RAPIDS System Tests - GATE level PARALLEL (48 workers)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(SYSTEM_TESTS_DIR)/test_*.py

.PHONY: run-system-func-parallel
run-system-func-parallel:
	@echo "================================================================================"
	@echo "Running RAPIDS System Tests - FUNC level PARALLEL (48 workers)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(SYSTEM_TESTS_DIR)/test_*.py

.PHONY: run-system-full-parallel
run-system-full-parallel:
	@echo "================================================================================"
	@echo "Running RAPIDS System Tests - FULL level PARALLEL (48 workers)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(SYSTEM_TESTS_DIR)/test_*.py

# ==============================================================================
# Run Targets - All Tests
# ==============================================================================

.PHONY: run-all
run-all:
	@echo "================================================================================"
	@echo "Running ALL RAPIDS Tests (FUB + Macro + System, default FUNC level)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_*.py $(MACRO_TESTS_DIR)/test_*.py $(SYSTEM_TESTS_DIR)/test_*.py

.PHONY: run-all-parallel
run-all-parallel:
	@echo "================================================================================"
	@echo "Running ALL RAPIDS Tests (Parallel - 48 workers)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(FUB_TESTS_DIR)/test_*.py $(MACRO_TESTS_DIR)/test_*.py $(SYSTEM_TESTS_DIR)/test_*.py

# REG_LEVEL Variants - Run all tests with specific regression levels
.PHONY: run-all-gate
run-all-gate:
	@echo "================================================================================"
	@echo "Running ALL RAPIDS Tests - GATE level (minimal params)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_*.py $(MACRO_TESTS_DIR)/test_*.py $(SYSTEM_TESTS_DIR)/test_*.py

.PHONY: run-all-func
run-all-func:
	@echo "================================================================================"
	@echo "Running ALL RAPIDS Tests - FUNC level (default params)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_*.py $(MACRO_TESTS_DIR)/test_*.py $(SYSTEM_TESTS_DIR)/test_*.py

.PHONY: run-all-full
run-all-full:
	@echo "================================================================================"
	@echo "Running ALL RAPIDS Tests - FULL level (comprehensive)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_*.py $(MACRO_TESTS_DIR)/test_*.py $(SYSTEM_TESTS_DIR)/test_*.py

.PHONY: run-all-gate-parallel
run-all-gate-parallel:
	@echo "================================================================================"
	@echo "Running ALL RAPIDS Tests - GATE level PARALLEL (48 workers)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(FUB_TESTS_DIR)/test_*.py $(MACRO_TESTS_DIR)/test_*.py $(SYSTEM_TESTS_DIR)/test_*.py

.PHONY: run-all-func-parallel
run-all-func-parallel:
	@echo "================================================================================"
	@echo "Running ALL RAPIDS Tests - FUNC level PARALLEL (48 workers)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(FUB_TESTS_DIR)/test_*.py $(MACRO_TESTS_DIR)/test_*.py $(SYSTEM_TESTS_DIR)/test_*.py

.PHONY: run-all-full-parallel
run-all-full-parallel:
	@echo "================================================================================"
	@echo "Running ALL RAPIDS Tests - FULL level PARALLEL (48 workers)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(FUB_TESTS_DIR)/test_*.py $(MACRO_TESTS_DIR)/test_*.py $(SYSTEM_TESTS_DIR)/test_*.py

# ==============================================================================
# Development Targets (pytest-watch)
# ==============================================================================

.PHONY: ptw-fub
ptw-fub:
	@echo "================================================================================"
	@echo "Starting pytest-watch for RAPIDS FUB tests"
	@echo "Tests will auto-rerun when files change. Press Ctrl+C to stop."
	@echo "================================================================================"
	@cd $(FUB_TESTS_DIR) && $(MAKE) ptw

.PHONY: ptw-macro
ptw-macro:
	@echo "================================================================================"
	@echo "Starting pytest-watch for RAPIDS macro tests"
	@echo "Tests will auto-rerun when files change. Press Ctrl+C to stop."
	@echo "================================================================================"
	@cd $(MACRO_TESTS_DIR) && $(MAKE) ptw

.PHONY: ptw-system
ptw-system:
	@echo "================================================================================"
	@echo "Starting pytest-watch for RAPIDS system tests"
	@echo "Tests will auto-rerun when files change. Press Ctrl+C to stop."
	@echo "================================================================================"
	@cd $(SYSTEM_TESTS_DIR) && $(MAKE) ptw

# ==============================================================================
# Collection Targets (verify tests without running)
# ==============================================================================

.PHONY: collect-fub
collect-fub:
	@echo "Collecting RAPIDS FUB tests (verifying imports)..."
	$(PYTEST) --collect-only $(FUB_TESTS_DIR)/test_*.py

.PHONY: collect-macro
collect-macro:
	@echo "Collecting RAPIDS macro tests..."
	$(PYTEST) --collect-only $(MACRO_TESTS_DIR)/test_*.py

.PHONY: collect-system
collect-system:
	@echo "Collecting RAPIDS system tests..."
	$(PYTEST) --collect-only $(SYSTEM_TESTS_DIR)/test_*.py

.PHONY: collect-all
collect-all:
	@echo "Collecting ALL RAPIDS tests..."
	$(PYTEST) --collect-only $(FUB_TESTS_DIR)/test_*.py $(MACRO_TESTS_DIR)/test_*.py $(SYSTEM_TESTS_DIR)/test_*.py

# ==============================================================================
# Clean Targets
# ==============================================================================

.PHONY: clean-fub
clean-fub:
	@echo "Cleaning FUB test artifacts..."
	rm -rf $(FUB_TESTS_DIR)/local_sim_build
	rm -rf $(FUB_TESTS_DIR)/sim_build
	find $(FUB_TESTS_DIR) -type f -name "*.log" -delete
	find $(FUB_TESTS_DIR) -type f -name "*.vcd" -delete
	find $(FUB_TESTS_DIR) -type f -name "dump.vcd" -delete
	@echo "✓ FUB test artifacts cleaned"

.PHONY: clean-macro
clean-macro:
	@echo "Cleaning macro test artifacts..."
	rm -rf $(MACRO_TESTS_DIR)/local_sim_build
	rm -rf $(MACRO_TESTS_DIR)/sim_build
	find $(MACRO_TESTS_DIR) -type f -name "*.log" -delete
	find $(MACRO_TESTS_DIR) -type f -name "*.vcd" -delete
	find $(MACRO_TESTS_DIR) -type f -name "dump.vcd" -delete
	@echo "✓ Macro test artifacts cleaned"

.PHONY: clean-system
clean-system:
	@echo "Cleaning system test artifacts..."
	rm -rf $(SYSTEM_TESTS_DIR)/local_sim_build
	rm -rf $(SYSTEM_TESTS_DIR)/sim_build
	find $(SYSTEM_TESTS_DIR) -type f -name "*.log" -delete
	find $(SYSTEM_TESTS_DIR) -type f -name "*.vcd" -delete
	find $(SYSTEM_TESTS_DIR) -type f -name "dump.vcd" -delete
	@echo "✓ System test artifacts cleaned"

.PHONY: clean-logs
clean-logs:
	@echo "Cleaning all log files..."
	find . -type f -name "*.log" -delete
	find . -type d -name "logs" -exec rm -rf {} + 2>/dev/null || true
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
clean-all: clean-fub clean-macro clean-system clean-logs clean-pycache clean-build clean-vcd
	@echo "================================================================================"
	@echo "✓ All RAPIDS test artifacts cleaned"
	@echo "================================================================================"

# ==============================================================================
# Utility Targets
# ==============================================================================

.PHONY: list-fub
list-fub:
	@echo "RAPIDS FUB Test Modules:"
	@find $(FUB_TESTS_DIR) -name "test_*.py" -type f | sort

.PHONY: list-macro
list-macro:
	@echo "RAPIDS Macro Test Modules:"
	@find $(MACRO_TESTS_DIR) -name "test_*.py" -type f | sort

.PHONY: list-system
list-system:
	@echo "RAPIDS System Test Modules:"
	@find $(SYSTEM_TESTS_DIR) -name "test_*.py" -type f | sort

.PHONY: list-all
list-all: list-fub list-macro list-system

.PHONY: status
status:
	@echo "================================================================================"
	@echo "RAPIDS Test Status"
	@echo "================================================================================"
	@echo "Test directories:"
	@echo "  FUB tests:    $(FUB_TESTS_DIR)/ (flattened structure)"
	@echo "  Macro tests:  $(MACRO_TESTS_DIR)/"
	@echo "  System tests: $(SYSTEM_TESTS_DIR)/"
	@echo ""
	@echo "Test modules found:"
	@echo -n "  FUB:    "
	@find $(FUB_TESTS_DIR) -name "test_*.py" -type f | wc -l
	@echo -n "  Macro:  "
	@find $(MACRO_TESTS_DIR) -name "test_*.py" -type f | wc -l
	@echo -n "  System: "
	@find $(SYSTEM_TESTS_DIR) -name "test_*.py" -type f | wc -l
	@echo ""
	@echo "Build artifacts:"
	@echo -n "  local_sim_build dirs: "
	@find . -type d -name "local_sim_build" | wc -l
	@echo -n "  Log files:            "
	@find . -type f -name "*.log" | wc -l
	@echo -n "  VCD files:            "
	@find . -type f -name "*.vcd" | wc -l
	@echo ""
	@echo "Python environment:"
	@echo "  REPO_ROOT: $(REPO_ROOT)"
	@echo "  Virtual env: $(REPO_ROOT)/env_python"
	@echo "================================================================================"

# ==============================================================================
# Combined Targets (clean + run)
# ==============================================================================

.PHONY: fresh-fub
fresh-fub: clean-fub run-fub
	@echo "✓ Fresh FUB test run complete"

.PHONY: fresh-macro
fresh-macro: clean-macro run-macro
	@echo "✓ Fresh macro test run complete"

.PHONY: fresh-system
fresh-system: clean-system run-system
	@echo "✓ Fresh system test run complete"

.PHONY: fresh-all
fresh-all: clean-all run-all
	@echo "✓ Fresh all tests run complete"

# ==============================================================================
# Quick Aliases
# ==============================================================================

.PHONY: fub
fub: run-fub

.PHONY: macro
macro: run-macro

.PHONY: system
system: run-system

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
