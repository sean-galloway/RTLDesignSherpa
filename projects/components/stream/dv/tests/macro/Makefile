# ==============================================================================
# STREAM Macro Tests Makefile
# ==============================================================================
#
# Local test runner for macro-level (integration) tests
#
# Usage:
#   cd $REPO_ROOT/projects/components/stream/dv/tests/macro
#   make <target>
#
# Quick start:
#   make help           - Show available targets
#   make run-rd         - Run all datapath_rd tests
#   make run-wr         - Run all datapath_wr tests
#   make run-all        - Run both rd and wr tests
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
PYTEST_RERUNS = --reruns 0 --reruns-delay 1

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
	@echo "STREAM Macro Tests Makefile - Datapath Read/Write Tests"
	@echo "================================================================================"
	@echo ""
	@echo "QUICK RUN TARGETS:"
	@echo "  make run-rd                     Run datapath_rd tests (FUNC level)"
	@echo "  make run-wr                     Run datapath_wr tests (FUNC level)"
	@echo "  make run-core                   Run stream_core tests (FUNC level)"
	@echo "  make run-core-mon               Run stream_core_mon tests (FUNC level)"
	@echo "  make run-all                    Run all tests (rd, wr, core)"
	@echo ""
	@echo "READ DATAPATH TARGETS (test_datapath_rd_test.py):"
	@echo "  make run-rd-gate                Run rd tests at GATE level"
	@echo "  make run-rd-gate-waves          Run rd tests at GATE level with waveforms"
	@echo "  make run-rd-gate-parallel       Run rd tests at GATE level in parallel"
	@echo "  make run-rd-gate-parallel-waves Run rd tests at GATE level parallel + waves"
	@echo "  make run-rd-func                Run rd tests at FUNC level (default)"
	@echo "  make run-rd-func-waves          Run rd tests at FUNC level with waveforms"
	@echo "  make run-rd-func-parallel       Run rd tests at FUNC level in parallel"
	@echo "  make run-rd-func-parallel-waves Run rd tests at FUNC level parallel + waves"
	@echo "  make run-rd-full                Run rd tests at FULL level"
	@echo "  make run-rd-full-waves          Run rd tests at FULL level with waveforms"
	@echo "  make run-rd-full-parallel       Run rd tests at FULL level in parallel"
	@echo "  make run-rd-full-parallel-waves Run rd tests at FULL level parallel + waves"
	@echo ""
	@echo "WRITE DATAPATH TARGETS (test_datapath_wr_test.py):"
	@echo "  make run-wr-gate                Run wr tests at GATE level"
	@echo "  make run-wr-gate-waves          Run wr tests at GATE level with waveforms"
	@echo "  make run-wr-gate-parallel       Run wr tests at GATE level in parallel"
	@echo "  make run-wr-gate-parallel-waves Run wr tests at GATE level parallel + waves"
	@echo "  make run-wr-func                Run wr tests at FUNC level (default)"
	@echo "  make run-wr-func-waves          Run wr tests at FUNC level with waveforms"
	@echo "  make run-wr-func-parallel       Run wr tests at FUNC level in parallel"
	@echo "  make run-wr-func-parallel-waves Run wr tests at FUNC level parallel + waves"
	@echo "  make run-wr-full                Run wr tests at FULL level"
	@echo "  make run-wr-full-waves          Run wr tests at FULL level with waveforms"
	@echo "  make run-wr-full-parallel       Run wr tests at FULL level in parallel"
	@echo "  make run-wr-full-parallel-waves Run wr tests at FULL level parallel + waves"
	@echo ""
	@echo "STREAM CORE TARGETS (test_stream_core.py):"
	@echo "  make run-core-gate                Run core tests at GATE level"
	@echo "  make run-core-gate-waves          Run core tests at GATE level with waveforms"
	@echo "  make run-core-gate-parallel       Run core tests at GATE level in parallel"
	@echo "  make run-core-gate-parallel-waves Run core tests at GATE level parallel + waves"
	@echo "  make run-core-func                Run core tests at FUNC level (default)"
	@echo "  make run-core-func-waves          Run core tests at FUNC level with waveforms"
	@echo "  make run-core-func-parallel       Run core tests at FUNC level in parallel"
	@echo "  make run-core-func-parallel-waves Run core tests at FUNC level parallel + waves"
	@echo "  make run-core-full                Run core tests at FULL level"
	@echo "  make run-core-full-waves          Run core tests at FULL level with waveforms"
	@echo "  make run-core-full-parallel       Run core tests at FULL level in parallel"
	@echo "  make run-core-full-parallel-waves Run core tests at FULL level parallel + waves"
	@echo ""
	@echo "STREAM CORE BURST MATRIX TARGETS (test_stream_core.py - burst level):"
	@echo "  Purpose: Validate SRAM sizing + verify perfect streaming (no bubbles/stalls)"
	@echo "  Tests: 25 tests covering all rd/wr burst sizes (8/16/32) × SRAM sizes (2KB/4KB)"
	@echo "  Goal: Prove MIN_SRAM = MAX(2KB, 2×burst_size) + continuous data flow"
	@echo "  Future: Will add reg_slices parameter to study latency effects"
	@echo ""
	@echo "  make run-core-burst                Run burst matrix tests (25 tests)"
	@echo "  make run-core-burst-waves          Run burst matrix tests with waveforms"
	@echo "  make run-core-burst-parallel       Run burst matrix tests in parallel"
	@echo "  make run-core-burst-parallel-waves Run burst matrix tests parallel + waves"
	@echo ""
	@echo "STREAM PERFORMANCE PROFILE TARGETS (test_stream_performance_profile.py):"
	@echo "  Purpose: Measure throughput and performance characteristics"
	@echo "  Tests: 10 tests covering single/dual/quad channels, FIFO depth comparison"
	@echo "  Goal: Performance benchmarking and throughput analysis"
	@echo ""
	@echo "  make run-perf                      Run performance profile tests (10 tests)"
	@echo "  make run-perf-waves                Run performance profile tests with waveforms"
	@echo "  make run-perf-parallel             Run performance profile tests in parallel"
	@echo "  make run-perf-parallel-waves       Run performance profile tests parallel + waves"
	@echo ""
	@echo "STREAM CORE MONITOR TARGETS (test_stream_core_mon.py):"
	@echo "  make run-core-mon-gate                Run monitor tests at GATE level"
	@echo "  make run-core-mon-gate-waves          Run monitor tests at GATE level with waveforms"
	@echo "  make run-core-mon-gate-parallel       Run monitor tests at GATE level in parallel"
	@echo "  make run-core-mon-gate-parallel-waves Run monitor tests at GATE level parallel + waves"
	@echo "  make run-core-mon-func                Run monitor tests at FUNC level (default)"
	@echo "  make run-core-mon-func-waves          Run monitor tests at FUNC level with waveforms"
	@echo "  make run-core-mon-func-parallel       Run monitor tests at FUNC level in parallel"
	@echo "  make run-core-mon-func-parallel-waves Run monitor tests at FUNC level parallel + waves"
	@echo "  make run-core-mon-full                Run monitor tests at FULL level"
	@echo "  make run-core-mon-full-waves          Run monitor tests at FULL level with waveforms"
	@echo "  make run-core-mon-full-parallel       Run monitor tests at FULL level in parallel"
	@echo "  make run-core-mon-full-parallel-waves Run monitor tests at FULL level parallel + waves"
	@echo ""
	@echo "COMBINED TARGETS (rd, wr, and core):"
	@echo "  make run-all-gate               Run all tests at GATE level"
	@echo "  make run-all-gate-waves         Run all tests at GATE level with waveforms"
	@echo "  make run-all-gate-parallel      Run all tests at GATE level in parallel"
	@echo "  make run-all-func               Run all tests at FUNC level"
	@echo "  make run-all-func-waves         Run all tests at FUNC level with waveforms"
	@echo "  make run-all-func-parallel      Run all tests at FUNC level in parallel"
	@echo "  make run-all-full               Run all tests at FULL level"
	@echo "  make run-all-full-waves         Run all tests at FULL level with waveforms"
	@echo "  make run-all-full-parallel      Run all tests at FULL level in parallel"
	@echo "  make run-all-full-parallel-waves Run all tests at FULL level parallel + waves"
	@echo ""
	@echo "UTILITY TARGETS:"
	@echo "  make collect-rd           Collect (don't run) rd tests"
	@echo "  make collect-wr           Collect (don't run) wr tests"
	@echo "  make collect-core         Collect (don't run) core tests"
	@echo "  make collect-core-mon     Collect (don't run) monitor tests"
	@echo "  make collect-perf         Collect (don't run) performance tests"
	@echo "  make clean                Clean local artifacts"
	@echo "  make clean-all            Clean all test artifacts"
	@echo ""
	@echo "================================================================================"

# ==============================================================================
# Quick Run Targets (Default FUNC level)
# ==============================================================================

.PHONY: run-rd
run-rd:
	@echo "Running datapath_rd tests (FUNC level)..."
	TEST_LEVEL=FUNC $(PYTEST) test_datapath_rd_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-wr
run-wr:
	@echo "Running datapath_wr tests (FUNC level)..."
	TEST_LEVEL=FUNC $(PYTEST) test_datapath_wr_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-core
run-core:
	@echo "Running stream_core tests (FUNC level)..."
	TEST_LEVEL=FUNC $(PYTEST) test_stream_core.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-all
run-all:
	@echo "Running all tests: datapath_rd, datapath_wr, and stream_core (FUNC level)..."
	TEST_LEVEL=FUNC $(PYTEST) test_datapath_rd_test.py test_datapath_wr_test.py test_stream_core.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

# ==============================================================================
# Read Datapath Targets (test_datapath_rd_test.py)
# ==============================================================================

# GATE level
.PHONY: run-rd-gate
run-rd-gate:
	@echo "Running datapath_rd tests at GATE level..."
	TEST_LEVEL=GATE $(PYTEST) test_datapath_rd_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-rd-gate-waves
run-rd-gate-waves:
	@echo "Running datapath_rd tests at GATE level with waveforms..."
	WAVES=1 TEST_LEVEL=GATE $(PYTEST) test_datapath_rd_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-rd-gate-parallel
run-rd-gate-parallel:
	@echo "Running datapath_rd tests at GATE level in parallel..."
	TEST_LEVEL=GATE $(PYTEST) test_datapath_rd_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-rd-gate-parallel-waves
run-rd-gate-parallel-waves:
	@echo "Running datapath_rd tests at GATE level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=GATE $(PYTEST) test_datapath_rd_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FUNC level
.PHONY: run-rd-func
run-rd-func:
	@echo "Running datapath_rd tests at FUNC level..."
	TEST_LEVEL=FUNC $(PYTEST) test_datapath_rd_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-rd-func-waves
run-rd-func-waves:
	@echo "Running datapath_rd tests at FUNC level with waveforms..."
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) test_datapath_rd_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-rd-func-parallel
run-rd-func-parallel:
	@echo "Running datapath_rd tests at FUNC level in parallel..."
	TEST_LEVEL=FUNC $(PYTEST) test_datapath_rd_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-rd-func-parallel-waves
run-rd-func-parallel-waves:
	@echo "Running datapath_rd tests at FUNC level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) test_datapath_rd_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FULL level
.PHONY: run-rd-full
run-rd-full:
	@echo "Running datapath_rd tests at FULL level..."
	TEST_LEVEL=FULL $(PYTEST) test_datapath_rd_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-rd-full-waves
run-rd-full-waves:
	@echo "Running datapath_rd tests at FULL level with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) test_datapath_rd_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-rd-full-parallel
run-rd-full-parallel:
	@echo "Running datapath_rd tests at FULL level in parallel..."
	TEST_LEVEL=FULL $(PYTEST) test_datapath_rd_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-rd-full-parallel-waves
run-rd-full-parallel-waves:
	@echo "Running datapath_rd tests at FULL level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) test_datapath_rd_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# Write Datapath Targets (test_datapath_wr_test.py)
# ==============================================================================

# GATE level
.PHONY: run-wr-gate
run-wr-gate:
	@echo "Running datapath_wr tests at GATE level..."
	TEST_LEVEL=GATE $(PYTEST) test_datapath_wr_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-wr-gate-waves
run-wr-gate-waves:
	@echo "Running datapath_wr tests at GATE level with waveforms..."
	WAVES=1 TEST_LEVEL=GATE $(PYTEST) test_datapath_wr_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-wr-gate-parallel
run-wr-gate-parallel:
	@echo "Running datapath_wr tests at GATE level in parallel..."
	TEST_LEVEL=GATE $(PYTEST) test_datapath_wr_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-wr-gate-parallel-waves
run-wr-gate-parallel-waves:
	@echo "Running datapath_wr tests at GATE level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=GATE $(PYTEST) test_datapath_wr_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FUNC level
.PHONY: run-wr-func
run-wr-func:
	@echo "Running datapath_wr tests at FUNC level..."
	TEST_LEVEL=FUNC $(PYTEST) test_datapath_wr_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-wr-func-waves
run-wr-func-waves:
	@echo "Running datapath_wr tests at FUNC level with waveforms..."
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) test_datapath_wr_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-wr-func-parallel
run-wr-func-parallel:
	@echo "Running datapath_wr tests at FUNC level in parallel..."
	TEST_LEVEL=FUNC $(PYTEST) test_datapath_wr_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-wr-func-parallel-waves
run-wr-func-parallel-waves:
	@echo "Running datapath_wr tests at FUNC level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) test_datapath_wr_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FULL level
.PHONY: run-wr-full
run-wr-full:
	@echo "Running datapath_wr tests at FULL level..."
	TEST_LEVEL=FULL $(PYTEST) test_datapath_wr_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-wr-full-waves
run-wr-full-waves:
	@echo "Running datapath_wr tests at FULL level with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) test_datapath_wr_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-wr-full-parallel
run-wr-full-parallel:
	@echo "Running datapath_wr tests at FULL level in parallel..."
	TEST_LEVEL=FULL $(PYTEST) test_datapath_wr_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-wr-full-parallel-waves
run-wr-full-parallel-waves:
	@echo "Running datapath_wr tests at FULL level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) test_datapath_wr_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# Stream Core Targets (test_stream_core.py)
# ==============================================================================

# GATE level
.PHONY: run-core-gate
run-core-gate:
	@echo "Running stream_core tests at GATE level..."
	TEST_LEVEL=GATE $(PYTEST) test_stream_core.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-core-gate-waves
run-core-gate-waves:
	@echo "Running stream_core tests at GATE level with waveforms..."
	WAVES=1 TEST_LEVEL=GATE $(PYTEST) test_stream_core.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-core-gate-parallel
run-core-gate-parallel:
	@echo "Running stream_core tests at GATE level in parallel..."
	TEST_LEVEL=GATE $(PYTEST) test_stream_core.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-core-gate-parallel-waves
run-core-gate-parallel-waves:
	@echo "Running stream_core tests at GATE level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=GATE $(PYTEST) test_stream_core.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FUNC level
.PHONY: run-core-func
run-core-func:
	@echo "Running stream_core tests at FUNC level..."
	TEST_LEVEL=FUNC $(PYTEST) test_stream_core.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-core-func-waves
run-core-func-waves:
	@echo "Running stream_core tests at FUNC level with waveforms..."
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) test_stream_core.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-core-func-parallel
run-core-func-parallel:
	@echo "Running stream_core tests at FUNC level in parallel..."
	TEST_LEVEL=FUNC $(PYTEST) test_stream_core.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-core-func-parallel-waves
run-core-func-parallel-waves:
	@echo "Running stream_core tests at FUNC level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) test_stream_core.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FULL level
.PHONY: run-core-full
run-core-full:
	@echo "Running stream_core tests at FULL level..."
	TEST_LEVEL=FULL $(PYTEST) test_stream_core.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-core-full-waves
run-core-full-waves:
	@echo "Running stream_core tests at FULL level with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) test_stream_core.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-core-full-parallel
run-core-full-parallel:
	@echo "Running stream_core tests at FULL level in parallel..."
	TEST_LEVEL=FULL $(PYTEST) test_stream_core.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-core-full-parallel-waves
run-core-full-parallel-waves:
	@echo "Running stream_core tests at FULL level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) test_stream_core.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# Stream Core Burst Matrix Targets (test_stream_core.py - BURST level)
# ==============================================================================

.PHONY: run-core-burst
run-core-burst:
	@echo "Running stream_core burst matrix tests (25 tests)..."
	TEST_LEVEL=burst $(PYTEST) test_stream_core.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-core-burst-waves
run-core-burst-waves:
	@echo "Running stream_core burst matrix tests with waveforms..."
	WAVES=1 TEST_LEVEL=burst $(PYTEST) test_stream_core.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-core-burst-parallel
run-core-burst-parallel:
	@echo "Running stream_core burst matrix tests in parallel..."
	TEST_LEVEL=burst $(PYTEST) test_stream_core.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-core-burst-parallel-waves
run-core-burst-parallel-waves:
	@echo "Running stream_core burst matrix tests in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=burst $(PYTEST) test_stream_core.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# Stream Performance Profile Targets (test_stream_performance_profile.py)
# ==============================================================================

.PHONY: run-perf
run-perf:
	@echo "Running stream performance profile tests (10 tests)..."
	$(PYTEST) test_stream_performance_profile.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-perf-waves
run-perf-waves:
	@echo "Running stream performance profile tests with waveforms..."
	WAVES=1 $(PYTEST) test_stream_performance_profile.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-perf-parallel
run-perf-parallel:
	@echo "Running stream performance profile tests in parallel..."
	$(PYTEST) test_stream_performance_profile.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-perf-parallel-waves
run-perf-parallel-waves:
	@echo "Running stream performance profile tests in parallel with waveforms..."
	WAVES=1 $(PYTEST) test_stream_performance_profile.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# Stream Core Monitor Targets (test_stream_core_mon.py)
# ==============================================================================

# Quick run target
.PHONY: run-core-mon
run-core-mon:
	@echo "Running stream_core_mon tests (FUNC level)..."
	TEST_LEVEL=FUNC $(PYTEST) test_stream_core_mon.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

# GATE level
.PHONY: run-core-mon-gate
run-core-mon-gate:
	@echo "Running stream_core_mon tests at GATE level..."
	TEST_LEVEL=GATE $(PYTEST) test_stream_core_mon.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-core-mon-gate-waves
run-core-mon-gate-waves:
	@echo "Running stream_core_mon tests at GATE level with waveforms..."
	WAVES=1 TEST_LEVEL=GATE $(PYTEST) test_stream_core_mon.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-core-mon-gate-parallel
run-core-mon-gate-parallel:
	@echo "Running stream_core_mon tests at GATE level in parallel..."
	TEST_LEVEL=GATE $(PYTEST) test_stream_core_mon.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-core-mon-gate-parallel-waves
run-core-mon-gate-parallel-waves:
	@echo "Running stream_core_mon tests at GATE level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=GATE $(PYTEST) test_stream_core_mon.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FUNC level
.PHONY: run-core-mon-func
run-core-mon-func:
	@echo "Running stream_core_mon tests at FUNC level..."
	TEST_LEVEL=FUNC $(PYTEST) test_stream_core_mon.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-core-mon-func-waves
run-core-mon-func-waves:
	@echo "Running stream_core_mon tests at FUNC level with waveforms..."
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) test_stream_core_mon.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-core-mon-func-parallel
run-core-mon-func-parallel:
	@echo "Running stream_core_mon tests at FUNC level in parallel..."
	TEST_LEVEL=FUNC $(PYTEST) test_stream_core_mon.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-core-mon-func-parallel-waves
run-core-mon-func-parallel-waves:
	@echo "Running stream_core_mon tests at FUNC level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) test_stream_core_mon.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FULL level
.PHONY: run-core-mon-full
run-core-mon-full:
	@echo "Running stream_core_mon tests at FULL level..."
	TEST_LEVEL=FULL $(PYTEST) test_stream_core_mon.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-core-mon-full-waves
run-core-mon-full-waves:
	@echo "Running stream_core_mon tests at FULL level with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) test_stream_core_mon.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-core-mon-full-parallel
run-core-mon-full-parallel:
	@echo "Running stream_core_mon tests at FULL level in parallel..."
	TEST_LEVEL=FULL $(PYTEST) test_stream_core_mon.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-core-mon-full-parallel-waves
run-core-mon-full-parallel-waves:
	@echo "Running stream_core_mon tests at FULL level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) test_stream_core_mon.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# Combined Targets (RD, WR, and Core)
# ==============================================================================

# GATE level
.PHONY: run-all-gate
run-all-gate:
	@echo "Running all tests at GATE level..."
	TEST_LEVEL=GATE $(PYTEST) test_datapath_rd_test.py test_datapath_wr_test.py test_stream_core.py test_stream_core_mon.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-all-gate-waves
run-all-gate-waves:
	@echo "Running all tests at GATE level with waveforms..."
	WAVES=1 TEST_LEVEL=GATE $(PYTEST) test_datapath_rd_test.py test_datapath_wr_test.py test_stream_core.py test_stream_core_mon.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-all-gate-parallel
run-all-gate-parallel:
	@echo "Running all tests at GATE level in parallel..."
	TEST_LEVEL=GATE $(PYTEST) test_datapath_rd_test.py test_datapath_wr_test.py test_stream_core.py test_stream_core_mon.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FUNC level
.PHONY: run-all-func
run-all-func:
	@echo "Running all tests at FUNC level..."
	TEST_LEVEL=FUNC $(PYTEST) test_datapath_rd_test.py test_datapath_wr_test.py test_stream_core.py test_stream_core_mon.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-all-func-waves
run-all-func-waves:
	@echo "Running all tests at FUNC level with waveforms..."
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) test_datapath_rd_test.py test_datapath_wr_test.py test_stream_core.py test_stream_core_mon.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-all-func-parallel
run-all-func-parallel:
	@echo "Running all tests at FUNC level in parallel..."
	TEST_LEVEL=FUNC $(PYTEST) test_datapath_rd_test.py test_datapath_wr_test.py test_stream_core.py test_stream_core_mon.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FULL level
.PHONY: run-all-full
run-all-full:
	@echo "Running ALL tests at FULL level..."
	TEST_LEVEL=FULL $(PYTEST) test_datapath_rd_test.py test_datapath_wr_test.py test_stream_core.py test_stream_core_mon.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-all-full-waves
run-all-full-waves:
	@echo "Running ALL tests at FULL level with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) test_datapath_rd_test.py test_datapath_wr_test.py test_stream_core.py test_stream_core_mon.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-all-full-parallel
run-all-full-parallel:
	@echo "Running ALL tests at FULL level in parallel..."
	TEST_LEVEL=FULL $(PYTEST) test_datapath_rd_test.py test_datapath_wr_test.py test_stream_core.py test_stream_core_mon.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-all-full-parallel-waves
run-all-full-parallel-waves:
	@echo "Running ALL tests at FULL level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) test_datapath_rd_test.py test_datapath_wr_test.py test_stream_core.py test_stream_core_mon.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# Utility Targets
# ==============================================================================

.PHONY: collect-rd
collect-rd:
	@echo "Collecting datapath_rd tests..."
	$(PYTEST) test_datapath_rd_test.py --collect-only

.PHONY: collect-wr
collect-wr:
	@echo "Collecting datapath_wr tests..."
	$(PYTEST) test_datapath_wr_test.py --collect-only

.PHONY: collect-core
collect-core:
	@echo "Collecting stream_core tests..."
	$(PYTEST) test_stream_core.py --collect-only

.PHONY: collect-core-mon
collect-core-mon:
	@echo "Collecting stream_core_mon tests..."
	$(PYTEST) test_stream_core_mon.py --collect-only

.PHONY: collect-perf
collect-perf:
	@echo "Collecting stream performance profile tests..."
	$(PYTEST) test_stream_performance_profile.py --collect-only

.PHONY: clean
clean:
	@echo "Cleaning local artifacts..."
	rm -rf __pycache__ .pytest_cache *.pyc

.PHONY: clean-all
clean-all: clean
	@echo "Cleaning all test artifacts..."
	rm -rf local_sim_build logs
	find . -name "*.vcd" -delete
	find . -name "*.log" -delete
