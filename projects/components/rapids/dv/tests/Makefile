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
#   make run-all        - Run all tests
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

# Test directories
FUB_TESTS_DIR = fub_tests
MACRO_TESTS_DIR = macro_tests
SYSTEM_TESTS_DIR = system_tests

# Pytest options
PYTEST = python3 -m pytest
PYTEST_VERBOSE = -v
PYTEST_QUIET = -q
PYTEST_XDIST = -n 4  # 4 parallel workers
PYTEST_TBSTYLE = --tb=short

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
	@echo "RUN TARGETS:"
	@echo "  make run-fub              Run all FUB (Functional Unit Block) tests"
	@echo "  make run-fub-parallel     Run FUB tests in parallel (4 workers)"
	@echo "  make run-macro            Run all macro tests"
	@echo "  make run-system           Run all system tests"
	@echo "  make run-all              Run all tests (FUB + macro + system)"
	@echo "  make run-all-parallel     Run all tests in parallel"
	@echo ""
	@echo "COLLECTION TARGETS (verify tests, don't run):"
	@echo "  make collect-fub          Collect FUB tests (verify imports)"
	@echo "  make collect-macro        Collect macro tests"
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
	@echo ""
	@echo "UTILITY TARGETS:"
	@echo "  make list-fub             List all FUB test modules"
	@echo "  make list-macro           List all macro test modules"
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
	@echo "Running RAPIDS FUB Tests (Sequential)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)

.PHONY: run-fub-parallel
run-fub-parallel:
	@echo "================================================================================"
	@echo "Running RAPIDS FUB Tests (Parallel - 4 workers)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(FUB_TESTS_DIR)

# ==============================================================================
# Run Targets - Macro Tests
# ==============================================================================

.PHONY: run-macro
run-macro:
	@echo "================================================================================"
	@echo "Running RAPIDS Macro Tests"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(MACRO_TESTS_DIR)

.PHONY: run-macro-parallel
run-macro-parallel:
	@echo "================================================================================"
	@echo "Running RAPIDS Macro Tests (Parallel - 4 workers)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(MACRO_TESTS_DIR)

# ==============================================================================
# Run Targets - System Tests
# ==============================================================================

.PHONY: run-system
run-system:
	@echo "================================================================================"
	@echo "Running RAPIDS System Tests"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(SYSTEM_TESTS_DIR)

# ==============================================================================
# Run Targets - All Tests
# ==============================================================================

.PHONY: run-all
run-all:
	@echo "================================================================================"
	@echo "Running ALL RAPIDS Tests (FUB + Macro + System)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR) $(MACRO_TESTS_DIR) $(SYSTEM_TESTS_DIR)

.PHONY: run-all-parallel
run-all-parallel:
	@echo "================================================================================"
	@echo "Running ALL RAPIDS Tests (Parallel - 4 workers)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(FUB_TESTS_DIR) $(MACRO_TESTS_DIR) $(SYSTEM_TESTS_DIR)

# ==============================================================================
# Collection Targets (verify tests without running)
# ==============================================================================

.PHONY: collect-fub
collect-fub:
	@echo "Collecting RAPIDS FUB tests (verifying imports)..."
	$(PYTEST) --collect-only $(FUB_TESTS_DIR)

.PHONY: collect-macro
collect-macro:
	@echo "Collecting RAPIDS macro tests..."
	$(PYTEST) --collect-only $(MACRO_TESTS_DIR)

.PHONY: collect-system
collect-system:
	@echo "Collecting RAPIDS system tests..."
	$(PYTEST) --collect-only $(SYSTEM_TESTS_DIR)

.PHONY: collect-all
collect-all:
	@echo "Collecting ALL RAPIDS tests..."
	$(PYTEST) --collect-only $(FUB_TESTS_DIR) $(MACRO_TESTS_DIR) $(SYSTEM_TESTS_DIR)

# ==============================================================================
# Clean Targets
# ==============================================================================

.PHONY: clean-fub
clean-fub:
	@echo "Cleaning FUB test artifacts..."
	rm -rf $(FUB_TESTS_DIR)/*/local_sim_build
	rm -rf $(FUB_TESTS_DIR)/*/logs/*.log
	rm -f $(FUB_TESTS_DIR)/*/*.vcd
	rm -f $(FUB_TESTS_DIR)/*/dump.vcd
	@echo "✓ FUB test artifacts cleaned"

.PHONY: clean-macro
clean-macro:
	@echo "Cleaning macro test artifacts..."
	rm -rf $(MACRO_TESTS_DIR)/local_sim_build
	rm -rf $(MACRO_TESTS_DIR)/logs/*.log
	rm -f $(MACRO_TESTS_DIR)/*.vcd
	rm -f $(MACRO_TESTS_DIR)/dump.vcd
	@echo "✓ Macro test artifacts cleaned"

.PHONY: clean-system
clean-system:
	@echo "Cleaning system test artifacts..."
	rm -rf $(SYSTEM_TESTS_DIR)/local_sim_build
	rm -rf $(SYSTEM_TESTS_DIR)/logs/*.log
	rm -f $(SYSTEM_TESTS_DIR)/*.vcd
	rm -f $(SYSTEM_TESTS_DIR)/dump.vcd
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
	@echo "  FUB tests:    $(FUB_TESTS_DIR)/"
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
