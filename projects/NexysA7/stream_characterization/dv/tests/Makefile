# ==============================================================================
# Stream Characterization Harness Test Makefile
# ==============================================================================
#
# PREREQUISITES:
#   Must be run with sourced environment:
#     source $REPO_ROOT/env_python
#     cd $REPO_ROOT/projects/NexysA7/stream_characterization/dv/tests
#     make <target>
#
# Quick start:
#   make help           - Show all available targets
#   make run-all        - Run all tests (TEST_LEVEL=func by default)
#   make run-all-gate   - Run quick smoke tests
#   make clean-all      - Clean all test artifacts
#
# Test Levels (TEST_LEVEL environment variable):
#   gate = Quick smoke tests - ping only (~90s compile, ~3s sim)
#   func = Functional coverage - ping + desc + csr + apb (~90s compile, ~30s sim)
#   full = Comprehensive validation (same as func, expandable with DMA ops)
#
# NOTE: First run compiles the full STREAM + harness RTL (~90s). Subsequent
# runs with the same parameters reuse the compiled model and are much faster.
#
# All test_*.py files in this directory are automatically included.
# ==============================================================================

SHELL := /bin/bash

ifndef REPO_ROOT
$(error REPO_ROOT is not set. Please run: source $$REPO_ROOT/env_python)
endif

# Pytest options
PYTEST = python3 -m pytest
PYTEST_VERBOSE = -v
PYTEST_QUIET = -q
PYTEST_XDIST = -n 4
PYTEST_TBSTYLE = --tb=short
PYTEST_RERUNS = --reruns 3 --reruns-delay 1

# Default test level
TEST_LEVEL ?= func

.DEFAULT_GOAL := help

# ==============================================================================
# Help Target
# ==============================================================================

.PHONY: help
help:
	@echo "================================================================================"
	@echo "Stream Characterization Harness Test Makefile"
	@echo "================================================================================"
	@echo ""
	@echo "All test_*.py files in this directory are auto-discovered."
	@echo ""
	@echo "TEST LEVELS (set via TEST_LEVEL=gate|func|full):"
	@echo "  gate = Quick smoke tests - ping only (~90s compile, ~3s sim)"
	@echo "  func = Functional coverage (~90s compile, ~30s sim) [default]"
	@echo "  full = Comprehensive validation (expandable with DMA ops)"
	@echo ""
	@echo "RUN ALL TESTS:"
	@echo "  make run-all              Run all tests (TEST_LEVEL=$(TEST_LEVEL))"
	@echo "  make run-all-gate         Run all tests at GATE level"
	@echo "  make run-all-func         Run all tests at FUNC level"
	@echo "  make run-all-full         Run all tests at FULL level"
	@echo ""
	@echo "PARALLEL (4 workers -- limited due to large compile):"
	@echo "  make run-all-parallel           All tests in parallel"
	@echo "  make run-all-gate-parallel      GATE level parallel"
	@echo "  make run-all-func-parallel      FUNC level parallel"
	@echo "  make run-all-full-parallel      FULL level parallel"
	@echo ""
	@echo "INDIVIDUAL MODULES:"
	@echo "  make run-stream-char      Run stream_char harness tests only"
	@echo ""
	@echo "COLLECTION (verify tests, don't run):"
	@echo "  make collect-all          Collect all tests (verify imports)"
	@echo ""
	@echo "CLEAN:"
	@echo "  make clean-all            Remove all test artifacts"
	@echo "  make clean-logs           Remove all log files"
	@echo "  make clean-build          Remove simulation build directories"
	@echo ""
	@echo "================================================================================"
	@echo "Prerequisites: source $(REPO_ROOT)/env_python"
	@echo "Current REPO_ROOT: $(REPO_ROOT)"
	@echo "Current TEST_LEVEL: $(TEST_LEVEL)"
	@echo ""
	@echo "Available test modules:"
	@ls -1 test_*.py 2>/dev/null | sed 's/^/  /' || echo "  (none found)"
	@echo "================================================================================"

# ==============================================================================
# Run All Tests
# ==============================================================================

.PHONY: run-all
run-all:
	@echo "================================================================================"
	@echo "Running Stream Char Tests (TEST_LEVEL=$(TEST_LEVEL))"
	@echo "================================================================================"
	TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-parallel
run-all-parallel:
	@echo "================================================================================"
	@echo "Running Stream Char Tests (Parallel, TEST_LEVEL=$(TEST_LEVEL))"
	@echo "================================================================================"
	TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_*.py

.PHONY: run-all-gate
run-all-gate:
	@echo "================================================================================"
	@echo "Running Stream Char Tests - GATE level (quick smoke test)"
	@echo "================================================================================"
	TEST_LEVEL=gate $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-func
run-all-func:
	@echo "================================================================================"
	@echo "Running Stream Char Tests - FUNC level (functional coverage)"
	@echo "================================================================================"
	TEST_LEVEL=func $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-full
run-all-full:
	@echo "================================================================================"
	@echo "Running Stream Char Tests - FULL level (comprehensive validation)"
	@echo "================================================================================"
	TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-gate-parallel
run-all-gate-parallel:
	@echo "================================================================================"
	@echo "Running Stream Char Tests - GATE level PARALLEL"
	@echo "================================================================================"
	TEST_LEVEL=gate $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_*.py

.PHONY: run-all-func-parallel
run-all-func-parallel:
	@echo "================================================================================"
	@echo "Running Stream Char Tests - FUNC level PARALLEL"
	@echo "================================================================================"
	TEST_LEVEL=func $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_*.py

.PHONY: run-all-full-parallel
run-all-full-parallel:
	@echo "================================================================================"
	@echo "Running Stream Char Tests - FULL level PARALLEL"
	@echo "================================================================================"
	TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_*.py

# ==============================================================================
# Individual Test Modules
# ==============================================================================

.PHONY: run-stream-char
run-stream-char:
	@echo "Running stream_char harness tests..."
	TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_stream_char.py

# ==============================================================================
# Collection Targets (verify tests without running)
# ==============================================================================

.PHONY: collect-all
collect-all:
	@echo "Collecting all stream char tests (verifying imports)..."
	$(PYTEST) --collect-only test_*.py

# ==============================================================================
# Clean Targets
# ==============================================================================

.PHONY: clean-build
clean-build:
	@echo "Cleaning simulation build directories..."
	rm -rf local_sim_build
	rm -rf sim_build
	@echo "Build directories cleaned"

.PHONY: clean-logs
clean-logs:
	@echo "Cleaning log files..."
	rm -rf logs
	find . -type f -name "*.log" -delete 2>/dev/null || true
	@echo "Log files cleaned"

.PHONY: clean-pycache
clean-pycache:
	@echo "Cleaning Python cache files..."
	find . -type d -name "__pycache__" -exec rm -rf {} + 2>/dev/null || true
	find . -type f -name "*.pyc" -delete 2>/dev/null || true
	@echo "Python cache cleaned"

.PHONY: clean-vcd
clean-vcd:
	@echo "Cleaning VCD trace files..."
	find . -type f -name "*.vcd" -delete 2>/dev/null || true
	find . -type f -name "*.fst" -delete 2>/dev/null || true
	@echo "Trace files cleaned"

.PHONY: clean-all
clean-all: clean-build clean-logs clean-pycache clean-vcd
	@echo "All test artifacts cleaned"
