# ==============================================================================
# RAPIDS FUB Tests Makefile
# ==============================================================================
#
# Local test runner for FUB (Functional Unit Block) tests
#
# Usage:
#   cd $REPO_ROOT/projects/components/rapids/dv/tests/fub_tests
#   make <target>
#
# Quick start:
#   make help           - Show available targets
#   make run            - Run all FUB tests
#   make ptw            - Run pytest-watch (auto-rerun on file changes)
#   make clean          - Clean local artifacts
#
# ==============================================================================

# Force bash shell
SHELL := /bin/bash

# Check if REPO_ROOT is set (from env_python)
ifndef REPO_ROOT
$(error REPO_ROOT is not set. Please run: source $$REPO_ROOT/env_python)
endif

# Pytest options
PYTEST = python3 -m pytest
PYTEST_VERBOSE = -v
PYTEST_QUIET = -q
PYTEST_XDIST = -n 48
PYTEST_TBSTYLE = --tb=short
PYTEST_RERUNS = --reruns 3 --reruns-delay 1

# Pytest-watch options
PTW = ptw
PTW_FLAGS = --runner "pytest --maxfail=1"

# Default target
.DEFAULT_GOAL := help

# ==============================================================================
# Help Target
# ==============================================================================

.PHONY: help
help:
	@echo "================================================================================"
	@echo "RAPIDS FUB Tests Makefile"
	@echo "================================================================================"
	@echo ""
	@echo "RUN TARGETS:"
	@echo "  make run                  Run all FUB tests"
	@echo "  make run-parallel         Run FUB tests in parallel (48 workers)"
	@echo "  make ptw                  Run pytest-watch (auto-rerun on changes)"
	@echo ""
	@echo "REG_LEVEL TARGETS:"
	@echo "  make run-gate             Run FUB tests at GATE level (quick)"
	@echo "  make run-func             Run FUB tests at FUNC level (default)"
	@echo "  make run-full             Run FUB tests at FULL level (comprehensive)"
	@echo ""
	@echo "UTILITY TARGETS:"
	@echo "  make collect              Collect (don't run) tests"
	@echo "  make clean                Clean local artifacts"
	@echo "  make clean-all            Clean all test artifacts"
	@echo ""
	@echo "================================================================================"

# ==============================================================================
# Run Targets
# ==============================================================================

.PHONY: run
run:
	@echo "Running RAPIDS FUB tests..."
	$(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-parallel
run-parallel:
	@echo "Running RAPIDS FUB tests in parallel..."
	$(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# REG_LEVEL Targets
# ==============================================================================

.PHONY: run-gate
run-gate:
	@echo "Running RAPIDS FUB tests at GATE level..."
	export REG_LEVEL=GATE && $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-func
run-func:
	@echo "Running RAPIDS FUB tests at FUNC level..."
	export REG_LEVEL=FUNC && $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-full
run-full:
	@echo "Running RAPIDS FUB tests at FULL level..."
	export REG_LEVEL=FULL && $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

# ==============================================================================
# Development Targets
# ==============================================================================

.PHONY: ptw
ptw:
	@echo "Starting pytest-watch for RAPIDS FUB tests..."
	@echo "Tests will auto-rerun when files change. Press Ctrl+C to stop."
	@echo ""
	$(PTW) $(PTW_FLAGS) -- test_*.py $(PYTEST_VERBOSE)

# ==============================================================================
# Utility Targets
# ==============================================================================

.PHONY: collect
collect:
	@echo "Collecting RAPIDS FUB tests..."
	$(PYTEST) test_*.py --collect-only

.PHONY: clean
clean:
	@echo "Cleaning local artifacts..."
	rm -rf __pycache__ .pytest_cache *.pyc

.PHONY: clean-all
clean-all: clean
	@echo "Cleaning all test artifacts..."
	rm -rf local_sim_build ../../../log
	find . -name "*.vcd" -delete
	find . -name "*.log" -delete

