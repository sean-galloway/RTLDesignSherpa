# ==============================================================================
# STREAM Subsystem Test Makefile
# ==============================================================================
#
# PREREQUISITES:
#   Must be run with sourced environment:
#     source $REPO_ROOT/env_python  # Sets $REPO_ROOT and activates venv
#     cd $REPO_ROOT/projects/components/dmas/stream/dv/tests
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
	@echo "WITH WAVES (VCD dump):"
	@echo "  make run-all-wave              Waves (TEST_LEVEL=$(TEST_LEVEL))"
	@echo "  make run-all-gate-wave         GATE + waves"
	@echo "  make run-all-func-wave         FUNC + waves"
	@echo "  make run-all-full-wave         FULL + waves"
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

# run-all[-parallel] run the tiers SERIALLY (fub -> macro -> top).  Lumping all
# three dirs into one pytest pool let heavy top sims run alongside fub/macro and
# caused cross-tier interference; running one tier to completion before the next
# avoids it.  Delegates to the serial fan-out rules below.
.PHONY: run-all
run-all: run

.PHONY: run-all-parallel
run-all-parallel: run-parallel

# ==============================================================================
# Top-level "run everything" - fan out to every environment's parallel targets.
# One DRY rule defines run-parallel (=gate) + per-level, with/without waves;
# each fans the same-named target into every sub-environment.
# ==============================================================================
# performance_tests (throughput benchmarks) are intentionally excluded from the
# regression fan-out; run them on demand via 'make -C performance_tests run-parallel'.
PARALLEL_DIRS := $(FUB_TESTS_DIR) $(MACRO_TESTS_DIR) $(TOP_TESTS_DIR)

.PHONY: run-parallel run-parallel-waves \
        run-gate-parallel run-gate-parallel-waves \
        run-func-parallel run-func-parallel-waves \
        run-full-parallel run-full-parallel-waves
run-parallel run-parallel-waves \
run-gate-parallel run-gate-parallel-waves \
run-func-parallel run-func-parallel-waves \
run-full-parallel run-full-parallel-waves:
	@echo "STREAM aggregate '$@' across: $(PARALLEL_DIRS)"
	@for d in $(PARALLEL_DIRS); do echo "==> $$d ($@)"; $(MAKE) -C $$d $@ || exit 1; done

# Non-parallel companion (same serial fan-out, one tier at a time, no -n workers).
# All three tiers (fub/macro/top) now expose these non-parallel targets.
.PHONY: run run-gate run-func run-full
run run-gate run-func run-full:
	@echo "STREAM aggregate '$@' across: $(PARALLEL_DIRS)"
	@for d in $(PARALLEL_DIRS); do echo "==> $$d ($@)"; $(MAKE) -C $$d $@ || exit 1; done

# run-all-* run the tiers SERIALLY (fub -> macro -> top); the -parallel variants
# use 48 workers within each tier.  Serial-by-tier avoids the cross-tier
# interference that a single lumped pytest -n48 pool caused (heavy top sims
# running alongside fub/macro).
.PHONY: run-all-gate run-all-func run-all-full
run-all-gate: run-gate
run-all-func: run-func
run-all-full: run-full

.PHONY: run-all-gate-parallel run-all-func-parallel run-all-full-parallel
run-all-gate-parallel: run-gate-parallel
run-all-func-parallel: run-func-parallel
run-all-full-parallel: run-full-parallel

# ==============================================================================
# Wave-Enabled Targets (WAVES=1 enables VCD dump)
# ==============================================================================

.PHONY: run-all-wave
run-all-wave:
	WAVES=1 TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
		$(FUB_TESTS_DIR)/test_*.py \
		$(MACRO_TESTS_DIR)/test_*.py \
		$(TOP_TESTS_DIR)/test_*.py

.PHONY: run-all-gate-wave
run-all-gate-wave:
	WAVES=1 TEST_LEVEL=gate $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
		$(FUB_TESTS_DIR)/test_*.py \
		$(MACRO_TESTS_DIR)/test_*.py \
		$(TOP_TESTS_DIR)/test_*.py

.PHONY: run-all-func-wave
run-all-func-wave:
	WAVES=1 TEST_LEVEL=func $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
		$(FUB_TESTS_DIR)/test_*.py \
		$(MACRO_TESTS_DIR)/test_*.py \
		$(TOP_TESTS_DIR)/test_*.py

.PHONY: run-all-full-wave
run-all-full-wave:
	WAVES=1 TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
		$(FUB_TESTS_DIR)/test_*.py \
		$(MACRO_TESTS_DIR)/test_*.py \
		$(TOP_TESTS_DIR)/test_*.py

# ==============================================================================
# Parallel + Wave Targets
# ==============================================================================

.PHONY: run-all-parallel-wave
run-all-parallel-wave:
	WAVES=1 TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) \
		$(FUB_TESTS_DIR)/test_*.py \
		$(MACRO_TESTS_DIR)/test_*.py \
		$(TOP_TESTS_DIR)/test_*.py

.PHONY: run-all-gate-parallel-wave
run-all-gate-parallel-wave:
	WAVES=1 TEST_LEVEL=gate $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) \
		$(FUB_TESTS_DIR)/test_*.py \
		$(MACRO_TESTS_DIR)/test_*.py \
		$(TOP_TESTS_DIR)/test_*.py

.PHONY: run-all-func-parallel-wave
run-all-func-parallel-wave:
	WAVES=1 TEST_LEVEL=func $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) \
		$(FUB_TESTS_DIR)/test_*.py \
		$(MACRO_TESTS_DIR)/test_*.py \
		$(TOP_TESTS_DIR)/test_*.py

.PHONY: run-all-full-parallel-wave
run-all-full-parallel-wave:
	WAVES=1 TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) \
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
	@echo "Generating merged coverage report..."
	@mkdir -p $(COVERAGE_REPORTS_DIR)
	@python3 $(REPO_ROOT)/bin/cov_utils/merge_testlevel_coverage.py $(COVERAGE_REPORTS_DIR) stream
	@echo "Report: $(COVERAGE_REPORTS_DIR)/latest_coverage_report.md"