# ==============================================================================
# STREAM Subsystem Test Makefile
# ==============================================================================
#
# PREREQUISITES:
#   Must be run with sourced environment:
#     source $REPO_ROOT/env_python  # Sets $REPO_ROOT and activates venv
#     cd $REPO_ROOT/projects/components/stream/dv/tests
#     make <target>
#
# Quick start:
#   make help           - Show all available targets
#   make run-fub        - Run all FUB tests
#   make run-macro      - Run all macro tests
#   make run-top        - Run all top tests
#   make run-all        - Run all tests
#   make clean-all      - Clean all test artifacts
#
# Test Levels (TEST_LEVEL environment variable):
#   gate = Quick smoke tests (~5 min)
#   func = Functional coverage (~30 min)
#   full = Comprehensive validation (~4 hr)
#
# Coverage:
#   make coverage-all           - Run all tests with coverage
#   make coverage-report        - Generate merged coverage report
#   make coverage-full-report   - Clean, run all, and generate report
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
FUB_TESTS_DIR = fub
MACRO_TESTS_DIR = macro
TOP_TESTS_DIR = top

# Coverage output directory (for merged reports)
COVERAGE_REPORTS_DIR = coverage_reports

# Pytest options
PYTEST = python3 -m pytest
PYTEST_VERBOSE = -v
PYTEST_QUIET = -q
PYTEST_XDIST = -n 48  # 48 parallel workers (matching AMBA)
PYTEST_XDIST_COV = -n 24  # Reduced workers for coverage (less contention)
PYTEST_TBSTYLE = --tb=short
PYTEST_RERUNS = --reruns 3 --reruns-delay 1  # Retry failed tests

# Coverage environment variables
# Coverage instrumentation adds ~2-3x slowdown
COVERAGE_ENV = SIM=verilator WAVES=0 COVERAGE=1 COVERAGE_LEGAL=1

# More retries for coverage (coverage adds overhead that can cause timeouts)
PYTEST_RERUNS_COV = --reruns 5 --reruns-delay 2

# Default test level (can be overridden: make run-fub TEST_LEVEL=full)
TEST_LEVEL ?= func

# Default target - show help
.DEFAULT_GOAL := help

# ==============================================================================
# Help Target
# ==============================================================================

.PHONY: help
help:
	@echo "================================================================================"
	@echo "STREAM Test Makefile - Available Targets"
	@echo "================================================================================"
	@echo ""
	@echo "TEST LEVEL HIERARCHY:"
	@echo "  FUB   = Functional Unit Block tests (individual modules)"
	@echo "  Macro = Integration tests (combined modules)"
	@echo "  Top   = Full system tests (complete STREAM with APB config)"
	@echo ""
	@echo "TEST LEVELS (set via TEST_LEVEL=gate|func|full):"
	@echo "  gate = Quick smoke tests (~5 min)"
	@echo "  func = Functional coverage (~30 min) [default]"
	@echo "  full = Comprehensive validation (~4 hr)"
	@echo ""
	@echo "RUN TARGETS (by Test Hierarchy):"
	@echo "  make run-fub              Run all FUB tests (TEST_LEVEL=$(TEST_LEVEL))"
	@echo "  make run-macro            Run all macro tests"
	@echo "  make run-top              Run all top-level tests"
	@echo "  make run-all              Run all tests (FUB + Macro + Top)"
	@echo ""
	@echo "RUN TARGETS WITH EXPLICIT TEST LEVEL:"
	@echo "  make run-fub-gate         Run FUB tests at GATE level"
	@echo "  make run-fub-func         Run FUB tests at FUNC level"
	@echo "  make run-fub-full         Run FUB tests at FULL level"
	@echo "  make run-macro-gate       Run macro tests at GATE level"
	@echo "  make run-macro-func       Run macro tests at FUNC level"
	@echo "  make run-macro-full       Run macro tests at FULL level"
	@echo "  make run-top-gate         Run top tests at GATE level"
	@echo "  make run-top-func         Run top tests at FUNC level"
	@echo "  make run-top-full         Run top tests at FULL level"
	@echo "  make run-all-gate         Run all tests at GATE level"
	@echo "  make run-all-func         Run all tests at FUNC level"
	@echo "  make run-all-full         Run all tests at FULL level"
	@echo ""
	@echo "PARALLEL TARGETS (48 workers, with retries):"
	@echo "  make run-fub-parallel           Run FUB tests in parallel"
	@echo "  make run-macro-parallel         Run macro tests in parallel"
	@echo "  make run-top-parallel           Run top tests in parallel"
	@echo "  make run-all-parallel           Run all tests in parallel"
	@echo "  make run-all-gate-parallel      Run all tests at GATE level (parallel)"
	@echo "  make run-all-func-parallel      Run all tests at FUNC level (parallel)"
	@echo "  make run-all-full-parallel      Run all tests at FULL level (parallel)"
	@echo ""
	@echo "COVERAGE TARGETS:"
	@echo "  make coverage-fub               Run FUB tests with coverage"
	@echo "  make coverage-macro             Run macro tests with coverage"
	@echo "  make coverage-top               Run top tests with coverage"
	@echo "  make coverage-all               Run all tests with coverage"
	@echo "  make coverage-fub-gate          Run FUB tests with coverage (GATE)"
	@echo "  make coverage-fub-func          Run FUB tests with coverage (FUNC)"
	@echo "  make coverage-fub-full          Run FUB tests with coverage (FULL)"
	@echo "  make coverage-all-gate          Run all tests with coverage (GATE)"
	@echo "  make coverage-all-func          Run all tests with coverage (FUNC)"
	@echo "  make coverage-all-full          Run all tests with coverage (FULL)"
	@echo "  make coverage-report            Generate merged coverage report"
	@echo "  make coverage-combined          Generate combined coverage report (deduplicated)"
	@echo "  make coverage-per-file          Generate per-file line coverage breakdown"
	@echo "  make coverage-full-report       Clean + run all + generate report"
	@echo "  make coverage-full-combined     Clean + run all FULL + combined report"
	@echo ""
	@echo "PARALLEL COVERAGE TARGETS (24 workers, 5 retries for coverage overhead):"
	@echo "  make coverage-fub-parallel             Run FUB tests with coverage (parallel)"
	@echo "  make coverage-macro-parallel           Run macro tests with coverage (parallel)"
	@echo "  make coverage-top-parallel             Run top tests with coverage (parallel)"
	@echo "  make coverage-all-parallel             Run all tests with coverage (parallel)"
	@echo "  make coverage-fub-gate-parallel        FUB coverage GATE level (parallel)"
	@echo "  make coverage-fub-func-parallel        FUB coverage FUNC level (parallel)"
	@echo "  make coverage-fub-full-parallel        FUB coverage FULL level (parallel)"
	@echo "  make coverage-macro-gate-parallel      Macro coverage GATE level (parallel)"
	@echo "  make coverage-macro-func-parallel      Macro coverage FUNC level (parallel)"
	@echo "  make coverage-macro-full-parallel      Macro coverage FULL level (parallel)"
	@echo "  make coverage-top-gate-parallel        Top coverage GATE level (parallel)"
	@echo "  make coverage-top-func-parallel        Top coverage FUNC level (parallel)"
	@echo "  make coverage-top-full-parallel        Top coverage FULL level (parallel)"
	@echo "  make coverage-all-gate-parallel        All coverage GATE level (parallel)"
	@echo "  make coverage-all-func-parallel        All coverage FUNC level (parallel)"
	@echo "  make coverage-all-full-parallel        All coverage FULL level (parallel)"
	@echo ""
	@echo "COLLECTION TARGETS (verify tests, don't run):"
	@echo "  make collect-fub          Collect FUB tests (verify imports)"
	@echo "  make collect-macro        Collect macro tests"
	@echo "  make collect-top          Collect top tests"
	@echo "  make collect-all          Collect all tests"
	@echo ""
	@echo "CLEAN TARGETS:"
	@echo "  make clean-fub            Remove FUB test artifacts"
	@echo "  make clean-macro          Remove macro test artifacts"
	@echo "  make clean-top            Remove top test artifacts"
	@echo "  make clean-all            Remove all test artifacts"
	@echo "  make clean-coverage       Clean all coverage data"
	@echo "  make clean-logs           Remove all log files"
	@echo "  make clean-build          Remove simulation build directories"
	@echo ""
	@echo "UTILITY TARGETS:"
	@echo "  make list-fub             List all FUB test modules"
	@echo "  make list-macro           List all macro test modules"
	@echo "  make list-top             List all top test modules"
	@echo "  make status               Show test status and coverage"
	@echo "  make coverage-status      Show coverage data status"
	@echo ""
	@echo "INDIVIDUAL TEST MODULES:"
	@echo "  make run-scheduler        Run scheduler tests only"
	@echo "  make run-perf             Run perf_profiler tests only"
	@echo "  make run-stream-core      Run stream_core tests only"
	@echo "  make run-stream-top       Run stream_top tests only"
	@echo ""
	@echo "================================================================================"
	@echo "Prerequisites: source $(REPO_ROOT)/env_python"
	@echo "Current REPO_ROOT: $(REPO_ROOT)"
	@echo "Current TEST_LEVEL: $(TEST_LEVEL)"
	@echo "================================================================================"

# ==============================================================================
# Run Targets - FUB Tests
# ==============================================================================

.PHONY: run-fub
run-fub:
	@echo "================================================================================"
	@echo "Running STREAM FUB Tests (TEST_LEVEL=$(TEST_LEVEL))"
	@echo "================================================================================"
	TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_*.py

.PHONY: run-fub-parallel
run-fub-parallel:
	@echo "================================================================================"
	@echo "Running STREAM FUB Tests (Parallel - 48 workers, TEST_LEVEL=$(TEST_LEVEL))"
	@echo "================================================================================"
	TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(FUB_TESTS_DIR)/test_*.py

# Explicit TEST_LEVEL variants for FUB Tests
.PHONY: run-fub-gate
run-fub-gate:
	@echo "================================================================================"
	@echo "Running STREAM FUB Tests - GATE level (quick smoke test)"
	@echo "================================================================================"
	TEST_LEVEL=gate $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_*.py

.PHONY: run-fub-func
run-fub-func:
	@echo "================================================================================"
	@echo "Running STREAM FUB Tests - FUNC level (functional coverage)"
	@echo "================================================================================"
	TEST_LEVEL=func $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_*.py

.PHONY: run-fub-full
run-fub-full:
	@echo "================================================================================"
	@echo "Running STREAM FUB Tests - FULL level (comprehensive validation)"
	@echo "================================================================================"
	TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_*.py

# Parallel versions with explicit TEST_LEVEL
.PHONY: run-fub-gate-parallel
run-fub-gate-parallel:
	@echo "================================================================================"
	@echo "Running STREAM FUB Tests - GATE level PARALLEL (48 workers)"
	@echo "================================================================================"
	TEST_LEVEL=gate $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(FUB_TESTS_DIR)/test_*.py

.PHONY: run-fub-func-parallel
run-fub-func-parallel:
	@echo "================================================================================"
	@echo "Running STREAM FUB Tests - FUNC level PARALLEL (48 workers)"
	@echo "================================================================================"
	TEST_LEVEL=func $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(FUB_TESTS_DIR)/test_*.py

.PHONY: run-fub-full-parallel
run-fub-full-parallel:
	@echo "================================================================================"
	@echo "Running STREAM FUB Tests - FULL level PARALLEL (48 workers)"
	@echo "================================================================================"
	TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(FUB_TESTS_DIR)/test_*.py

# ==============================================================================
# Run Targets - Macro Tests
# ==============================================================================

.PHONY: run-macro
run-macro:
	@echo "================================================================================"
	@echo "Running STREAM Macro Tests (TEST_LEVEL=$(TEST_LEVEL))"
	@echo "================================================================================"
	TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(MACRO_TESTS_DIR)/test_*.py

.PHONY: run-macro-parallel
run-macro-parallel:
	@echo "================================================================================"
	@echo "Running STREAM Macro Tests (Parallel - 48 workers)"
	@echo "================================================================================"
	TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(MACRO_TESTS_DIR)/test_*.py

# Explicit TEST_LEVEL variants for Macro Tests
.PHONY: run-macro-gate
run-macro-gate:
	@echo "================================================================================"
	@echo "Running STREAM Macro Tests - GATE level"
	@echo "================================================================================"
	TEST_LEVEL=gate $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(MACRO_TESTS_DIR)/test_*.py

.PHONY: run-macro-func
run-macro-func:
	@echo "================================================================================"
	@echo "Running STREAM Macro Tests - FUNC level"
	@echo "================================================================================"
	TEST_LEVEL=func $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(MACRO_TESTS_DIR)/test_*.py

.PHONY: run-macro-full
run-macro-full:
	@echo "================================================================================"
	@echo "Running STREAM Macro Tests - FULL level"
	@echo "================================================================================"
	TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(MACRO_TESTS_DIR)/test_*.py

# Parallel versions
.PHONY: run-macro-gate-parallel
run-macro-gate-parallel:
	@echo "================================================================================"
	@echo "Running STREAM Macro Tests - GATE level PARALLEL (48 workers)"
	@echo "================================================================================"
	TEST_LEVEL=gate $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(MACRO_TESTS_DIR)/test_*.py

.PHONY: run-macro-func-parallel
run-macro-func-parallel:
	@echo "================================================================================"
	@echo "Running STREAM Macro Tests - FUNC level PARALLEL (48 workers)"
	@echo "================================================================================"
	TEST_LEVEL=func $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(MACRO_TESTS_DIR)/test_*.py

.PHONY: run-macro-full-parallel
run-macro-full-parallel:
	@echo "================================================================================"
	@echo "Running STREAM Macro Tests - FULL level PARALLEL (48 workers)"
	@echo "================================================================================"
	TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(MACRO_TESTS_DIR)/test_*.py

# ==============================================================================
# Run Targets - Top Tests
# ==============================================================================

.PHONY: run-top
run-top:
	@echo "================================================================================"
	@echo "Running STREAM Top Tests (TEST_LEVEL=$(TEST_LEVEL))"
	@echo "================================================================================"
	TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(TOP_TESTS_DIR)/test_*.py

.PHONY: run-top-parallel
run-top-parallel:
	@echo "================================================================================"
	@echo "Running STREAM Top Tests (Parallel - 48 workers)"
	@echo "================================================================================"
	TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(TOP_TESTS_DIR)/test_*.py

# Explicit TEST_LEVEL variants for Top Tests
.PHONY: run-top-gate
run-top-gate:
	@echo "================================================================================"
	@echo "Running STREAM Top Tests - GATE level"
	@echo "================================================================================"
	TEST_LEVEL=gate $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(TOP_TESTS_DIR)/test_*.py

.PHONY: run-top-func
run-top-func:
	@echo "================================================================================"
	@echo "Running STREAM Top Tests - FUNC level"
	@echo "================================================================================"
	TEST_LEVEL=func $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(TOP_TESTS_DIR)/test_*.py

.PHONY: run-top-full
run-top-full:
	@echo "================================================================================"
	@echo "Running STREAM Top Tests - FULL level"
	@echo "================================================================================"
	TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(TOP_TESTS_DIR)/test_*.py

# Parallel versions
.PHONY: run-top-gate-parallel
run-top-gate-parallel:
	@echo "================================================================================"
	@echo "Running STREAM Top Tests - GATE level PARALLEL (48 workers)"
	@echo "================================================================================"
	TEST_LEVEL=gate $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(TOP_TESTS_DIR)/test_*.py

.PHONY: run-top-func-parallel
run-top-func-parallel:
	@echo "================================================================================"
	@echo "Running STREAM Top Tests - FUNC level PARALLEL (48 workers)"
	@echo "================================================================================"
	TEST_LEVEL=func $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(TOP_TESTS_DIR)/test_*.py

.PHONY: run-top-full-parallel
run-top-full-parallel:
	@echo "================================================================================"
	@echo "Running STREAM Top Tests - FULL level PARALLEL (48 workers)"
	@echo "================================================================================"
	TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(TOP_TESTS_DIR)/test_*.py

# ==============================================================================
# Run Targets - All Tests
# ==============================================================================

.PHONY: run-all
run-all:
	@echo "================================================================================"
	@echo "Running ALL STREAM Tests (FUB + Macro + Top, TEST_LEVEL=$(TEST_LEVEL))"
	@echo "================================================================================"
	TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
		$(FUB_TESTS_DIR)/test_*.py \
		$(MACRO_TESTS_DIR)/test_*.py \
		$(TOP_TESTS_DIR)/test_*.py

.PHONY: run-all-parallel
run-all-parallel:
	@echo "================================================================================"
	@echo "Running ALL STREAM Tests (Parallel - 48 workers)"
	@echo "================================================================================"
	TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) \
		$(FUB_TESTS_DIR)/test_*.py \
		$(MACRO_TESTS_DIR)/test_*.py \
		$(TOP_TESTS_DIR)/test_*.py

# Explicit TEST_LEVEL variants - All tests
.PHONY: run-all-gate
run-all-gate:
	@echo "================================================================================"
	@echo "Running ALL STREAM Tests - GATE level (quick smoke test)"
	@echo "================================================================================"
	TEST_LEVEL=gate $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
		$(FUB_TESTS_DIR)/test_*.py \
		$(MACRO_TESTS_DIR)/test_*.py \
		$(TOP_TESTS_DIR)/test_*.py

.PHONY: run-all-func
run-all-func:
	@echo "================================================================================"
	@echo "Running ALL STREAM Tests - FUNC level (functional coverage)"
	@echo "================================================================================"
	TEST_LEVEL=func $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
		$(FUB_TESTS_DIR)/test_*.py \
		$(MACRO_TESTS_DIR)/test_*.py \
		$(TOP_TESTS_DIR)/test_*.py

.PHONY: run-all-full
run-all-full:
	@echo "================================================================================"
	@echo "Running ALL STREAM Tests - FULL level (comprehensive)"
	@echo "================================================================================"
	TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
		$(FUB_TESTS_DIR)/test_*.py \
		$(MACRO_TESTS_DIR)/test_*.py \
		$(TOP_TESTS_DIR)/test_*.py

.PHONY: run-all-gate-parallel
run-all-gate-parallel:
	@echo "================================================================================"
	@echo "Running ALL STREAM Tests - GATE level PARALLEL (48 workers)"
	@echo "================================================================================"
	TEST_LEVEL=gate $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) \
		$(FUB_TESTS_DIR)/test_*.py \
		$(MACRO_TESTS_DIR)/test_*.py \
		$(TOP_TESTS_DIR)/test_*.py

.PHONY: run-all-func-parallel
run-all-func-parallel:
	@echo "================================================================================"
	@echo "Running ALL STREAM Tests - FUNC level PARALLEL (48 workers)"
	@echo "================================================================================"
	TEST_LEVEL=func $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) \
		$(FUB_TESTS_DIR)/test_*.py \
		$(MACRO_TESTS_DIR)/test_*.py \
		$(TOP_TESTS_DIR)/test_*.py

.PHONY: run-all-full-parallel
run-all-full-parallel:
	@echo "================================================================================"
	@echo "Running ALL STREAM Tests - FULL level PARALLEL (48 workers)"
	@echo "================================================================================"
	TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) \
		$(FUB_TESTS_DIR)/test_*.py \
		$(MACRO_TESTS_DIR)/test_*.py \
		$(TOP_TESTS_DIR)/test_*.py

# ==============================================================================
# Coverage Targets - Individual Test Levels
# ==============================================================================

.PHONY: coverage-fub
coverage-fub:
	@echo "================================================================================"
	@echo "Running STREAM FUB Tests with Coverage (TEST_LEVEL=$(TEST_LEVEL))"
	@echo "================================================================================"
	$(COVERAGE_ENV) TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_*.py

.PHONY: coverage-fub-parallel
coverage-fub-parallel:
	@echo "================================================================================"
	@echo "Running STREAM FUB Tests with Coverage (Parallel - 24 workers, 5 retries)"
	@echo "================================================================================"
	$(COVERAGE_ENV) TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST_COV) $(PYTEST_RERUNS_COV) $(FUB_TESTS_DIR)/test_*.py

.PHONY: coverage-macro
coverage-macro:
	@echo "================================================================================"
	@echo "Running STREAM Macro Tests with Coverage (TEST_LEVEL=$(TEST_LEVEL))"
	@echo "================================================================================"
	$(COVERAGE_ENV) TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(MACRO_TESTS_DIR)/test_*.py

.PHONY: coverage-macro-parallel
coverage-macro-parallel:
	@echo "================================================================================"
	@echo "Running STREAM Macro Tests with Coverage (Parallel - 24 workers, 5 retries)"
	@echo "================================================================================"
	$(COVERAGE_ENV) TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST_COV) $(PYTEST_RERUNS_COV) $(MACRO_TESTS_DIR)/test_*.py

.PHONY: coverage-top
coverage-top:
	@echo "================================================================================"
	@echo "Running STREAM Top Tests with Coverage (TEST_LEVEL=$(TEST_LEVEL))"
	@echo "================================================================================"
	$(COVERAGE_ENV) TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(TOP_TESTS_DIR)/test_*.py

.PHONY: coverage-top-parallel
coverage-top-parallel:
	@echo "================================================================================"
	@echo "Running STREAM Top Tests with Coverage (Parallel - 24 workers, 5 retries)"
	@echo "================================================================================"
	$(COVERAGE_ENV) TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST_COV) $(PYTEST_RERUNS_COV) $(TOP_TESTS_DIR)/test_*.py

.PHONY: coverage-all
coverage-all:
	@echo "================================================================================"
	@echo "Running ALL STREAM Tests with Coverage (TEST_LEVEL=$(TEST_LEVEL))"
	@echo "================================================================================"
	$(COVERAGE_ENV) TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
		$(FUB_TESTS_DIR)/test_*.py \
		$(MACRO_TESTS_DIR)/test_*.py \
		$(TOP_TESTS_DIR)/test_*.py

.PHONY: coverage-all-parallel
coverage-all-parallel:
	@echo "================================================================================"
	@echo "Running ALL STREAM Tests with Coverage (Parallel - 24 workers, 5 retries)"
	@echo "================================================================================"
	$(COVERAGE_ENV) TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST_COV) $(PYTEST_RERUNS_COV) \
		$(FUB_TESTS_DIR)/test_*.py \
		$(MACRO_TESTS_DIR)/test_*.py \
		$(TOP_TESTS_DIR)/test_*.py

# Coverage with explicit TEST_LEVEL - FUB
.PHONY: coverage-fub-gate
coverage-fub-gate:
	@echo "================================================================================"
	@echo "Running STREAM FUB Tests with Coverage - GATE level"
	@echo "================================================================================"
	$(COVERAGE_ENV) TEST_LEVEL=gate $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_*.py

.PHONY: coverage-fub-gate-parallel
coverage-fub-gate-parallel:
	@echo "================================================================================"
	@echo "Running STREAM FUB Tests with Coverage - GATE level PARALLEL"
	@echo "================================================================================"
	$(COVERAGE_ENV) TEST_LEVEL=gate $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST_COV) $(PYTEST_RERUNS_COV) $(FUB_TESTS_DIR)/test_*.py

.PHONY: coverage-fub-func
coverage-fub-func:
	@echo "================================================================================"
	@echo "Running STREAM FUB Tests with Coverage - FUNC level"
	@echo "================================================================================"
	$(COVERAGE_ENV) TEST_LEVEL=func $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_*.py

.PHONY: coverage-fub-func-parallel
coverage-fub-func-parallel:
	@echo "================================================================================"
	@echo "Running STREAM FUB Tests with Coverage - FUNC level PARALLEL"
	@echo "================================================================================"
	$(COVERAGE_ENV) TEST_LEVEL=func $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST_COV) $(PYTEST_RERUNS_COV) $(FUB_TESTS_DIR)/test_*.py

.PHONY: coverage-fub-full
coverage-fub-full:
	@echo "================================================================================"
	@echo "Running STREAM FUB Tests with Coverage - FULL level"
	@echo "================================================================================"
	$(COVERAGE_ENV) TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_*.py

.PHONY: coverage-fub-full-parallel
coverage-fub-full-parallel:
	@echo "================================================================================"
	@echo "Running STREAM FUB Tests with Coverage - FULL level PARALLEL"
	@echo "================================================================================"
	$(COVERAGE_ENV) TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST_COV) $(PYTEST_RERUNS_COV) $(FUB_TESTS_DIR)/test_*.py

# Coverage with explicit TEST_LEVEL - Macro
.PHONY: coverage-macro-gate
coverage-macro-gate:
	@echo "================================================================================"
	@echo "Running STREAM Macro Tests with Coverage - GATE level"
	@echo "================================================================================"
	$(COVERAGE_ENV) TEST_LEVEL=gate $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(MACRO_TESTS_DIR)/test_*.py

.PHONY: coverage-macro-gate-parallel
coverage-macro-gate-parallel:
	@echo "================================================================================"
	@echo "Running STREAM Macro Tests with Coverage - GATE level PARALLEL"
	@echo "================================================================================"
	$(COVERAGE_ENV) TEST_LEVEL=gate $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST_COV) $(PYTEST_RERUNS_COV) $(MACRO_TESTS_DIR)/test_*.py

.PHONY: coverage-macro-func
coverage-macro-func:
	@echo "================================================================================"
	@echo "Running STREAM Macro Tests with Coverage - FUNC level"
	@echo "================================================================================"
	$(COVERAGE_ENV) TEST_LEVEL=func $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(MACRO_TESTS_DIR)/test_*.py

.PHONY: coverage-macro-func-parallel
coverage-macro-func-parallel:
	@echo "================================================================================"
	@echo "Running STREAM Macro Tests with Coverage - FUNC level PARALLEL"
	@echo "================================================================================"
	$(COVERAGE_ENV) TEST_LEVEL=func $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST_COV) $(PYTEST_RERUNS_COV) $(MACRO_TESTS_DIR)/test_*.py

.PHONY: coverage-macro-full
coverage-macro-full:
	@echo "================================================================================"
	@echo "Running STREAM Macro Tests with Coverage - FULL level"
	@echo "================================================================================"
	$(COVERAGE_ENV) TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(MACRO_TESTS_DIR)/test_*.py

.PHONY: coverage-macro-full-parallel
coverage-macro-full-parallel:
	@echo "================================================================================"
	@echo "Running STREAM Macro Tests with Coverage - FULL level PARALLEL"
	@echo "================================================================================"
	$(COVERAGE_ENV) TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST_COV) $(PYTEST_RERUNS_COV) $(MACRO_TESTS_DIR)/test_*.py

# Coverage with explicit TEST_LEVEL - Top
.PHONY: coverage-top-gate
coverage-top-gate:
	@echo "================================================================================"
	@echo "Running STREAM Top Tests with Coverage - GATE level"
	@echo "================================================================================"
	$(COVERAGE_ENV) TEST_LEVEL=gate $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(TOP_TESTS_DIR)/test_*.py

.PHONY: coverage-top-gate-parallel
coverage-top-gate-parallel:
	@echo "================================================================================"
	@echo "Running STREAM Top Tests with Coverage - GATE level PARALLEL"
	@echo "================================================================================"
	$(COVERAGE_ENV) TEST_LEVEL=gate $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST_COV) $(PYTEST_RERUNS_COV) $(TOP_TESTS_DIR)/test_*.py

.PHONY: coverage-top-func
coverage-top-func:
	@echo "================================================================================"
	@echo "Running STREAM Top Tests with Coverage - FUNC level"
	@echo "================================================================================"
	$(COVERAGE_ENV) TEST_LEVEL=func $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(TOP_TESTS_DIR)/test_*.py

.PHONY: coverage-top-func-parallel
coverage-top-func-parallel:
	@echo "================================================================================"
	@echo "Running STREAM Top Tests with Coverage - FUNC level PARALLEL"
	@echo "================================================================================"
	$(COVERAGE_ENV) TEST_LEVEL=func $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST_COV) $(PYTEST_RERUNS_COV) $(TOP_TESTS_DIR)/test_*.py

.PHONY: coverage-top-full
coverage-top-full:
	@echo "================================================================================"
	@echo "Running STREAM Top Tests with Coverage - FULL level"
	@echo "================================================================================"
	$(COVERAGE_ENV) TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(TOP_TESTS_DIR)/test_*.py

.PHONY: coverage-top-full-parallel
coverage-top-full-parallel:
	@echo "================================================================================"
	@echo "Running STREAM Top Tests with Coverage - FULL level PARALLEL"
	@echo "================================================================================"
	$(COVERAGE_ENV) TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST_COV) $(PYTEST_RERUNS_COV) $(TOP_TESTS_DIR)/test_*.py

# Coverage with explicit TEST_LEVEL - All
.PHONY: coverage-all-gate
coverage-all-gate:
	@echo "================================================================================"
	@echo "Running ALL STREAM Tests with Coverage - GATE level"
	@echo "================================================================================"
	$(COVERAGE_ENV) TEST_LEVEL=gate $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
		$(FUB_TESTS_DIR)/test_*.py \
		$(MACRO_TESTS_DIR)/test_*.py \
		$(TOP_TESTS_DIR)/test_*.py

.PHONY: coverage-all-gate-parallel
coverage-all-gate-parallel:
	@echo "================================================================================"
	@echo "Running ALL STREAM Tests with Coverage - GATE level PARALLEL"
	@echo "================================================================================"
	$(COVERAGE_ENV) TEST_LEVEL=gate $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST_COV) $(PYTEST_RERUNS_COV) \
		$(FUB_TESTS_DIR)/test_*.py \
		$(MACRO_TESTS_DIR)/test_*.py \
		$(TOP_TESTS_DIR)/test_*.py

.PHONY: coverage-all-func
coverage-all-func:
	@echo "================================================================================"
	@echo "Running ALL STREAM Tests with Coverage - FUNC level"
	@echo "================================================================================"
	$(COVERAGE_ENV) TEST_LEVEL=func $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
		$(FUB_TESTS_DIR)/test_*.py \
		$(MACRO_TESTS_DIR)/test_*.py \
		$(TOP_TESTS_DIR)/test_*.py

.PHONY: coverage-all-func-parallel
coverage-all-func-parallel:
	@echo "================================================================================"
	@echo "Running ALL STREAM Tests with Coverage - FUNC level PARALLEL"
	@echo "================================================================================"
	$(COVERAGE_ENV) TEST_LEVEL=func $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST_COV) $(PYTEST_RERUNS_COV) \
		$(FUB_TESTS_DIR)/test_*.py \
		$(MACRO_TESTS_DIR)/test_*.py \
		$(TOP_TESTS_DIR)/test_*.py

.PHONY: coverage-all-full
coverage-all-full:
	@echo "================================================================================"
	@echo "Running ALL STREAM Tests with Coverage - FULL level"
	@echo "================================================================================"
	$(COVERAGE_ENV) TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
		$(FUB_TESTS_DIR)/test_*.py \
		$(MACRO_TESTS_DIR)/test_*.py \
		$(TOP_TESTS_DIR)/test_*.py

.PHONY: coverage-all-full-parallel
coverage-all-full-parallel:
	@echo "================================================================================"
	@echo "Running ALL STREAM Tests with Coverage - FULL level PARALLEL"
	@echo "================================================================================"
	$(COVERAGE_ENV) TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST_COV) $(PYTEST_RERUNS_COV) \
		$(FUB_TESTS_DIR)/test_*.py \
		$(MACRO_TESTS_DIR)/test_*.py \
		$(TOP_TESTS_DIR)/test_*.py

# ==============================================================================
# Coverage Report Generation
# ==============================================================================

.PHONY: coverage-report
coverage-report:
	@echo "================================================================================"
	@echo "Generating Merged Coverage Report"
	@echo "================================================================================"
	@mkdir -p $(COVERAGE_REPORTS_DIR)
	@echo "Merging coverage from all test levels..."
	@python3 -c "\
import json, glob, os; \
from datetime import datetime; \
\
merged = {'test_count': 0, 'tests': [], 'groups': {}, 'overall_protocol_pct': 0.0, 'overall_line_pct': 0.0}; \
total_proto, total_line = 0.0, 0.0; \
\
for level in ['fub', 'macro', 'top']: \
    pattern = f'{level}/coverage_data/per_test/*_summary.json'; \
    for f in glob.glob(pattern): \
        try: \
            data = json.load(open(f)); \
            merged['tests'].append({'name': data.get('test_name', f), 'level': level, 'protocol_pct': data.get('overall', {}).get('protocol_pct', 0), 'line_pct': data.get('overall', {}).get('line_pct', 0)}); \
            total_proto += data.get('overall', {}).get('protocol_pct', 0); \
            total_line += data.get('overall', {}).get('line_pct', 0); \
            merged['test_count'] += 1; \
            for gn, gd in data.get('protocol_coverage', {}).get('groups', {}).items(): \
                if gn not in merged['groups']: merged['groups'][gn] = {'covered': 0, 'total': 0, 'points': {}}; \
                for pn, pd in gd.get('points', {}).items(): \
                    if pn not in merged['groups'][gn]['points']: merged['groups'][gn]['points'][pn] = {'hits': 0, 'goal': pd.get('goal', 1)}; \
                    merged['groups'][gn]['points'][pn]['hits'] += pd.get('hits', 0); \
        except: pass; \
\
if merged['test_count'] > 0: \
    merged['overall_protocol_pct'] = total_proto / merged['test_count']; \
    merged['overall_line_pct'] = total_line / merged['test_count']; \
\
for gn, gd in merged['groups'].items(): \
    covered = sum(1 for p in gd['points'].values() if p['hits'] >= p['goal']); \
    gd['covered'], gd['total'] = covered, len(gd['points']); \
    gd['coverage_pct'] = (covered / len(gd['points']) * 100) if gd['points'] else 0; \
\
ts = datetime.now().strftime('%Y%m%d_%H%M%S'); \
json.dump(merged, open(f'$(COVERAGE_REPORTS_DIR)/merged_coverage_{ts}.json', 'w'), indent=2); \
json.dump(merged, open(f'$(COVERAGE_REPORTS_DIR)/latest_merged_coverage.json', 'w'), indent=2); \
\
report = ['# STREAM Combined Coverage Report', '', f'**Generated:** {datetime.now().strftime(\"%Y-%m-%d %H:%M:%S\")}', f'**Tests Run:** {merged[\"test_count\"]}', '', '## Summary', '', '| Metric | Coverage | Target | Status |', '|--------|----------|--------|--------|']; \
pstatus = 'PASS' if merged['overall_protocol_pct'] >= 80 else 'FAIL'; \
lstatus = 'PASS' if merged['overall_line_pct'] >= 80 else 'FAIL'; \
report.extend([f'| Protocol Coverage | {merged[\"overall_protocol_pct\"]:.1f}% | 80% | {pstatus} |', f'| Line Coverage | {merged[\"overall_line_pct\"]:.1f}% | 80% | {lstatus} |', '', '## Tests by Level', '', '| Level | Test Count |', '|-------|------------|']); \
for lvl in ['fub', 'macro', 'top']: \
    cnt = sum(1 for t in merged['tests'] if t.get('level') == lvl); \
    report.append(f'| {lvl.upper()} | {cnt} |'); \
report.extend(['', '## Protocol Coverage by Group', '', '| Group | Covered | Total | Percentage |', '|-------|---------|-------|------------|']); \
for gn, gd in sorted(merged['groups'].items()): \
    report.append(f'| {gn} | {gd[\"covered\"]} | {gd[\"total\"]} | {gd.get(\"coverage_pct\", 0):.1f}% |'); \
report.extend(['', '## Coverage Gaps', '']); \
gaps = [f'- **{gn}**: {pn} (0 hits)' for gn, gd in merged['groups'].items() for pn, pd in gd.get('points', {}).items() if pd['hits'] < pd['goal']]; \
if gaps: report.extend(['The following coverage points were NOT hit:', ''] + gaps[:50]); \
else: report.append('All coverage points were hit!'); \
report.extend(['', '---', '*Report generated by STREAM coverage infrastructure*']); \
open(f'$(COVERAGE_REPORTS_DIR)/coverage_report_{ts}.md', 'w').write('\\n'.join(report)); \
open(f'$(COVERAGE_REPORTS_DIR)/latest_coverage_report.md', 'w').write('\\n'.join(report)); \
print(f'Coverage report generated: $(COVERAGE_REPORTS_DIR)/latest_coverage_report.md'); \
print(f'  Tests: {merged[\"test_count\"]}'); \
print(f'  Protocol: {merged[\"overall_protocol_pct\"]:.1f}%'); \
print(f'  Line: {merged[\"overall_line_pct\"]:.1f}%'); \
"

.PHONY: coverage-full-report
coverage-full-report: clean-coverage coverage-all-full coverage-report
	@echo "================================================================================"
	@echo "Full Coverage Run Complete"
	@echo "================================================================================"
	@echo "Report: $(COVERAGE_REPORTS_DIR)/latest_coverage_report.md"

.PHONY: coverage-status
coverage-status:
	@echo "================================================================================"
	@echo "STREAM Coverage Status"
	@echo "================================================================================"
	@echo ""
	@echo "Coverage data directories:"
	@for dir in fub macro top; do \
		if [ -d "$$dir/coverage_data" ]; then \
			echo "  $$dir/coverage_data/: EXISTS"; \
			echo -n "    Per-test files: "; \
			find $$dir/coverage_data/per_test -name "*_summary.json" 2>/dev/null | wc -l; \
		else \
			echo "  $$dir/coverage_data/: NOT FOUND"; \
		fi; \
	done
	@echo ""
	@echo "Merged reports:"
	@if [ -d "$(COVERAGE_REPORTS_DIR)" ]; then \
		echo "  $(COVERAGE_REPORTS_DIR)/: EXISTS"; \
		ls -la $(COVERAGE_REPORTS_DIR)/*.md 2>/dev/null || echo "    No reports found"; \
	else \
		echo "  $(COVERAGE_REPORTS_DIR)/: NOT FOUND"; \
	fi
	@echo ""
	@if [ -f "$(COVERAGE_REPORTS_DIR)/latest_coverage_report.md" ]; then \
		echo "Latest report summary:"; \
		head -20 $(COVERAGE_REPORTS_DIR)/latest_coverage_report.md; \
	fi

.PHONY: coverage-per-file
coverage-per-file:
	@echo "================================================================================"
	@echo "Generating Per-File Line Coverage Report"
	@echo "================================================================================"
	@mkdir -p $(COVERAGE_REPORTS_DIR)
	@python3 -c "\
import os, glob, subprocess, tempfile, json; \
from datetime import datetime; \
\
# Find all coverage.dat files \
dat_files = []; \
for level in ['fub', 'macro', 'top']: \
    sim_build = f'{level}/local_sim_build'; \
    if os.path.exists(sim_build): \
        for test_dir in glob.glob(os.path.join(sim_build, 'test_*')): \
            cov_dat = os.path.join(test_dir, 'coverage.dat'); \
            if os.path.exists(cov_dat): \
                dat_files.append(cov_dat); \
\
if not dat_files: \
    print('No coverage.dat files found. Run coverage tests first.'); \
    exit(1); \
\
print(f'Found {len(dat_files)} coverage.dat files'); \
\
# Merge all coverage data \
with tempfile.NamedTemporaryFile(suffix='.dat', delete=False) as tmp: \
    merged_dat = tmp.name; \
\
cmd = ['verilator_coverage', '--write', merged_dat] + dat_files; \
result = subprocess.run(cmd, capture_output=True, text=True); \
if result.returncode != 0: \
    print(f'Error merging coverage: {result.stderr}'); \
    exit(1); \
\
# Run verilator_coverage --annotate to get per-file stats \
with tempfile.TemporaryDirectory() as annotate_dir: \
    cmd = ['verilator_coverage', '--annotate', annotate_dir, merged_dat]; \
    result = subprocess.run(cmd, capture_output=True, text=True); \
\
    # Parse annotated files \
    file_stats = {}; \
    for annotated_file in glob.glob(os.path.join(annotate_dir, '*.v')): \
        filename = os.path.basename(annotated_file); \
        if filename.endswith('.v'): \
            original_name = filename[:-2]; \
        else: \
            original_name = filename; \
\
        line_covered = 0; \
        line_total = 0; \
\
        with open(annotated_file, 'r') as f: \
            for line in f: \
                if line.startswith('%'): \
                    count_str = line[1:7].strip(); \
                    line_total += 1; \
                    if count_str: \
                        try: \
                            if int(count_str) > 0: \
                                line_covered += 1; \
                        except ValueError: \
                            pass; \
\
        if line_total > 0: \
            pct = (line_covered / line_total * 100); \
            file_stats[original_name] = {'covered': line_covered, 'total': line_total, 'pct': pct}; \
\
# Sort by coverage percentage (ascending - worst first) \
sorted_files = sorted(file_stats.items(), key=lambda x: x[1]['pct']); \
\
# Calculate totals \
total_covered = sum(s['covered'] for s in file_stats.values()); \
total_lines = sum(s['total'] for s in file_stats.values()); \
overall_pct = (total_covered / total_lines * 100) if total_lines > 0 else 0; \
\
ts = datetime.now().strftime('%Y%m%d_%H%M%S'); \
\
# Generate markdown report \
report = ['# STREAM Per-File Line Coverage Report', ''];\
report.append(f'**Generated:** {datetime.now().strftime(\"%Y-%m-%d %H:%M:%S\")}'); \
report.append(f'**Total Files:** {len(file_stats)}'); \
report.append(f'**Overall Line Coverage:** {total_covered}/{total_lines} ({overall_pct:.1f}%)'); \
report.append(''); \
report.append('## Coverage by File (sorted by coverage %, lowest first)'); \
report.append(''); \
report.append('| File | Covered | Total | Coverage % | Status |'); \
report.append('|------|---------|-------|------------|--------|'); \
\
for filename, stats in sorted_files: \
    status = 'LOW' if stats['pct'] < 50 else ('MED' if stats['pct'] < 80 else 'OK'); \
    short_name = filename.split('/')[-1] if '/' in filename else filename; \
    report.append(f'| {short_name} | {stats[\"covered\"]} | {stats[\"total\"]} | {stats[\"pct\"]:.1f}% | {status} |'); \
\
report.append(''); \
report.append('## Summary by Coverage Level'); \
report.append(''); \
low_files = sum(1 for s in file_stats.values() if s['pct'] < 50); \
med_files = sum(1 for s in file_stats.values() if 50 <= s['pct'] < 80); \
ok_files = sum(1 for s in file_stats.values() if s['pct'] >= 80); \
report.append(f'- **LOW (<50%):** {low_files} files'); \
report.append(f'- **MED (50-79%):** {med_files} files'); \
report.append(f'- **OK (>=80%):** {ok_files} files'); \
report.append(''); \
report.append('---'); \
report.append('*Report generated by STREAM coverage infrastructure*'); \
\
open(f'$(COVERAGE_REPORTS_DIR)/per_file_coverage_{ts}.md', 'w').write('\\n'.join(report)); \
open(f'$(COVERAGE_REPORTS_DIR)/latest_per_file_coverage.md', 'w').write('\\n'.join(report)); \
\
# Also save JSON for programmatic access \
json_data = {'timestamp': ts, 'overall': {'covered': total_covered, 'total': total_lines, 'pct': overall_pct}, 'files': file_stats}; \
json.dump(json_data, open(f'$(COVERAGE_REPORTS_DIR)/per_file_coverage_{ts}.json', 'w'), indent=2); \
json.dump(json_data, open(f'$(COVERAGE_REPORTS_DIR)/latest_per_file_coverage.json', 'w'), indent=2); \
\
print(f''); \
print(f'Per-file coverage report generated:'); \
print(f'  Markdown: $(COVERAGE_REPORTS_DIR)/latest_per_file_coverage.md'); \
print(f'  JSON: $(COVERAGE_REPORTS_DIR)/latest_per_file_coverage.json'); \
print(f''); \
print(f'Overall: {total_covered}/{total_lines} lines ({overall_pct:.1f}%)'); \
print(f'  LOW (<50%%): {low_files} files'); \
print(f'  MED (50-79%%): {med_files} files'); \
print(f'  OK (>=80%%): {ok_files} files'); \
\
os.unlink(merged_dat); \
"

.PHONY: coverage-combined
coverage-combined:
	@echo "================================================================================"
	@echo "Generating Combined Coverage Report (Deduplicated)"
	@echo "================================================================================"
	@echo "This merges coverage from fub/macro/top with deduplication."
	@echo "A coverage point hit in ANY environment counts only once."
	@echo ""
	@python3 ../stream_coverage/combine_coverage.py

.PHONY: coverage-full-combined
coverage-full-combined: clean-coverage coverage-all-full-parallel coverage-combined
	@echo "================================================================================"
	@echo "Full Combined Coverage Run Complete"
	@echo "================================================================================"
	@echo "Report: combined_coverage/combined_report_latest.md"

# ==============================================================================
# Individual Test Modules
# ==============================================================================

.PHONY: run-scheduler
run-scheduler:
	@echo "Running scheduler tests..."
	TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_scheduler.py

.PHONY: run-perf
run-perf:
	@echo "Running perf_profiler tests..."
	TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_perf_profiler.py

.PHONY: run-stream-core
run-stream-core:
	@echo "Running stream_core tests..."
	TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(MACRO_TESTS_DIR)/test_stream_core.py

.PHONY: run-stream-top
run-stream-top:
	@echo "Running stream_top tests..."
	TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(TOP_TESTS_DIR)/test_stream_top.py

.PHONY: run-sram
run-sram:
	@echo "Running simple_sram tests..."
	TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_simple_sram.py

.PHONY: run-axi-rd
run-axi-rd:
	@echo "Running axi_read_engine tests..."
	TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_axi_read_engine.py

.PHONY: run-axi-wr
run-axi-wr:
	@echo "Running axi_write_engine tests..."
	TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_axi_write_engine.py

.PHONY: run-sram-ctrl
run-sram-ctrl:
	@echo "Running sram_controller tests..."
	TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_sram_controller.py

.PHONY: run-monbus
run-monbus:
	@echo "Running monbus_axil_group tests..."
	TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(MACRO_TESTS_DIR)/test_monbus_axil_group.py

# ==============================================================================
# Collection Targets (verify tests without running)
# ==============================================================================

.PHONY: collect-fub
collect-fub:
	@echo "Collecting STREAM FUB tests (verifying imports)..."
	$(PYTEST) --collect-only $(FUB_TESTS_DIR)/test_*.py

.PHONY: collect-macro
collect-macro:
	@echo "Collecting STREAM macro tests..."
	$(PYTEST) --collect-only $(MACRO_TESTS_DIR)/test_*.py

.PHONY: collect-top
collect-top:
	@echo "Collecting STREAM top tests..."
	$(PYTEST) --collect-only $(TOP_TESTS_DIR)/test_*.py

.PHONY: collect-all
collect-all:
	@echo "Collecting ALL STREAM tests..."
	$(PYTEST) --collect-only \
		$(FUB_TESTS_DIR)/test_*.py \
		$(MACRO_TESTS_DIR)/test_*.py \
		$(TOP_TESTS_DIR)/test_*.py

# ==============================================================================
# Clean Targets
# ==============================================================================

.PHONY: clean-fub
clean-fub:
	@echo "Cleaning FUB test artifacts..."
	rm -rf $(FUB_TESTS_DIR)/local_sim_build
	rm -rf $(FUB_TESTS_DIR)/sim_build
	find $(FUB_TESTS_DIR) -type f -name "*.log" -delete 2>/dev/null || true
	find $(FUB_TESTS_DIR) -type f -name "*.vcd" -delete 2>/dev/null || true
	@echo "FUB test artifacts cleaned"

.PHONY: clean-macro
clean-macro:
	@echo "Cleaning macro test artifacts..."
	rm -rf $(MACRO_TESTS_DIR)/local_sim_build
	rm -rf $(MACRO_TESTS_DIR)/sim_build
	find $(MACRO_TESTS_DIR) -type f -name "*.log" -delete 2>/dev/null || true
	find $(MACRO_TESTS_DIR) -type f -name "*.vcd" -delete 2>/dev/null || true
	@echo "Macro test artifacts cleaned"

.PHONY: clean-top
clean-top:
	@echo "Cleaning top test artifacts..."
	rm -rf $(TOP_TESTS_DIR)/local_sim_build
	rm -rf $(TOP_TESTS_DIR)/sim_build
	find $(TOP_TESTS_DIR) -type f -name "*.log" -delete 2>/dev/null || true
	find $(TOP_TESTS_DIR) -type f -name "*.vcd" -delete 2>/dev/null || true
	@echo "Top test artifacts cleaned"

.PHONY: clean-logs
clean-logs:
	@echo "Cleaning all log files..."
	find . -type f -name "*.log" -delete 2>/dev/null || true
	find . -type d -name "logs" -exec rm -rf {} + 2>/dev/null || true
	@echo "Log files cleaned"

.PHONY: clean-pycache
clean-pycache:
	@echo "Cleaning Python cache files..."
	find . -type d -name "__pycache__" -exec rm -rf {} + 2>/dev/null || true
	find . -type f -name "*.pyc" -delete 2>/dev/null || true
	@echo "Python cache cleaned"

.PHONY: clean-build
clean-build:
	@echo "Cleaning simulation build directories..."
	find . -type d -name "local_sim_build" -exec rm -rf {} + 2>/dev/null || true
	find . -type d -name "sim_build" -exec rm -rf {} + 2>/dev/null || true
	@echo "Build directories cleaned"

.PHONY: clean-vcd
clean-vcd:
	@echo "Cleaning VCD waveform files..."
	find . -type f -name "*.vcd" -delete 2>/dev/null || true
	find . -type f -name "*.fst" -delete 2>/dev/null || true
	@echo "Waveform files cleaned"

.PHONY: clean-coverage
clean-coverage:
	@echo "Cleaning coverage data..."
	rm -rf $(FUB_TESTS_DIR)/coverage_data
	rm -rf $(MACRO_TESTS_DIR)/coverage_data
	rm -rf $(TOP_TESTS_DIR)/coverage_data
	rm -rf $(COVERAGE_REPORTS_DIR)
	@echo "Coverage data cleaned"

.PHONY: clean-all
clean-all: clean-fub clean-macro clean-top clean-logs clean-pycache clean-build clean-vcd clean-coverage
	@echo "================================================================================"
	@echo "All STREAM test artifacts cleaned"
	@echo "================================================================================"

# ==============================================================================
# Utility Targets
# ==============================================================================

.PHONY: list-fub
list-fub:
	@echo "STREAM FUB Test Modules:"
	@find $(FUB_TESTS_DIR) -name "test_*.py" -type f | sort

.PHONY: list-macro
list-macro:
	@echo "STREAM Macro Test Modules:"
	@find $(MACRO_TESTS_DIR) -name "test_*.py" -type f | sort

.PHONY: list-top
list-top:
	@echo "STREAM Top Test Modules:"
	@find $(TOP_TESTS_DIR) -name "test_*.py" -type f | sort

.PHONY: list
list: list-fub list-macro list-top

.PHONY: status
status:
	@echo "================================================================================"
	@echo "STREAM Test Status"
	@echo "================================================================================"
	@echo "Test directories:"
	@echo "  FUB tests:   $(FUB_TESTS_DIR)/"
	@echo "  Macro tests: $(MACRO_TESTS_DIR)/"
	@echo "  Top tests:   $(TOP_TESTS_DIR)/"
	@echo ""
	@echo "Test modules found:"
	@echo -n "  FUB:   "
	@find $(FUB_TESTS_DIR) -name "test_*.py" -type f 2>/dev/null | wc -l
	@echo -n "  Macro: "
	@find $(MACRO_TESTS_DIR) -name "test_*.py" -type f 2>/dev/null | wc -l
	@echo -n "  Top:   "
	@find $(TOP_TESTS_DIR) -name "test_*.py" -type f 2>/dev/null | wc -l
	@echo ""
	@echo "Build artifacts:"
	@echo -n "  local_sim_build dirs: "
	@find . -type d -name "local_sim_build" 2>/dev/null | wc -l
	@echo -n "  Log files:            "
	@find . -type f -name "*.log" 2>/dev/null | wc -l
	@echo -n "  VCD files:            "
	@find . -type f -name "*.vcd" 2>/dev/null | wc -l
	@echo ""
	@echo "Environment:"
	@echo "  REPO_ROOT:   $(REPO_ROOT)"
	@echo "  TEST_LEVEL:  $(TEST_LEVEL)"
	@echo "================================================================================"

# ==============================================================================
# Combined Targets (clean + run)
# ==============================================================================

.PHONY: fresh-fub
fresh-fub: clean-fub run-fub
	@echo "Fresh FUB test run complete"

.PHONY: fresh-macro
fresh-macro: clean-macro run-macro
	@echo "Fresh macro test run complete"

.PHONY: fresh-top
fresh-top: clean-top run-top
	@echo "Fresh top test run complete"

.PHONY: fresh-all
fresh-all: clean-all run-all
	@echo "Fresh all tests run complete"

.PHONY: fresh-coverage
fresh-coverage: clean-coverage coverage-all coverage-report
	@echo "Fresh coverage run complete"

# ==============================================================================
# Quick Aliases
# ==============================================================================

.PHONY: fub
fub: run-fub

.PHONY: macro
macro: run-macro

.PHONY: top
top: run-top

.PHONY: all
all: run-all

.PHONY: clean
clean: clean-all

.PHONY: collect
collect: collect-all

.PHONY: cov
cov: coverage-all

.PHONY: report
report: coverage-report

# ==============================================================================
# End of Makefile
# ==============================================================================
