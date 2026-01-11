# ==============================================================================
# RAPIDS Macro-Beats (AXIS-Based) Tests Makefile
# ==============================================================================
#
# Local test runner for macro-level beats tests using AXIS-based interfaces:
# - beats_scheduler_group
# - beats_scheduler_group_array
# - sink_datapath (and sink_data_path_axis_test)
# - source_datapath (and source_data_path_axis_test)
# - snk_sram_controller
# - src_sram_controller
#
# Usage:
#   cd $REPO_ROOT/projects/components/rapids/dv/tests/macro_beats_tests
#   make <target>
#
# Quick start:
#   make help                   - Show available targets
#   make run                    - Run all macro-beats tests
#   make run-scheduler-group    - Run scheduler_group tests only
#   make run-sink               - Run sink datapath tests only
#   make run-source             - Run source datapath tests only
#   make ptw                    - Run pytest-watch (auto-rerun on file changes)
#   make clean                  - Clean local artifacts
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
	@echo "RAPIDS Macro-Beats (AXIS-Based) Tests Makefile"
	@echo "================================================================================"
	@echo ""
	@echo "RUN TARGETS (ALL TESTS):"
	@echo "  make run                  Run all macro-beats tests"
	@echo "  make run-waves            Run all macro-beats tests with waveforms"
	@echo "  make run-parallel         Run all macro-beats tests in parallel (48 workers)"
	@echo "  make run-parallel-waves   Run all macro-beats tests parallel with waveforms"
	@echo ""
	@echo "SCHEDULER GROUP TARGETS:"
	@echo "  make run-scheduler-group       Run beats_scheduler_group tests"
	@echo "  make run-scheduler-group-waves Run beats_scheduler_group tests with waveforms"
	@echo "  make run-scheduler-array       Run beats_scheduler_group_array tests"
	@echo "  make run-scheduler-array-waves Run beats_scheduler_group_array tests with waveforms"
	@echo ""
	@echo "SINK DATAPATH TARGETS:"
	@echo "  make run-sink             Run all sink datapath tests"
	@echo "  make run-sink-waves       Run all sink datapath tests with waveforms"
	@echo "  make run-snk-sram         Run snk_sram_controller tests"
	@echo "  make run-snk-sram-waves   Run snk_sram_controller tests with waveforms"
	@echo ""
	@echo "SOURCE DATAPATH TARGETS:"
	@echo "  make run-source           Run all source datapath tests"
	@echo "  make run-source-waves     Run all source datapath tests with waveforms"
	@echo "  make run-src-sram         Run src_sram_controller tests"
	@echo "  make run-src-sram-waves   Run src_sram_controller tests with waveforms"
	@echo ""
	@echo "REG_LEVEL TARGETS:"
	@echo "  make run-gate             Run tests at GATE level (quick)"
	@echo "  make run-gate-waves       Run tests at GATE level with waveforms"
	@echo "  make run-func             Run tests at FUNC level (default)"
	@echo "  make run-func-waves       Run tests at FUNC level with waveforms"
	@echo "  make run-full             Run tests at FULL level (comprehensive)"
	@echo "  make run-full-waves       Run tests at FULL level with waveforms"
	@echo ""
	@echo "UTILITY TARGETS:"
	@echo "  make ptw                  Run pytest-watch (auto-rerun on changes)"
	@echo "  make collect              Collect (don't run) tests"
	@echo "  make clean                Clean local artifacts"
	@echo "  make clean-all            Clean all test artifacts"
	@echo ""
	@echo "================================================================================"

# ==============================================================================
# Run Targets - All Tests
# ==============================================================================

.PHONY: run
run:
	@echo "Running RAPIDS macro-beats tests..."
	$(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-waves
run-waves:
	@echo "Running RAPIDS macro-beats tests with waveforms..."
	WAVES=1 $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-parallel
run-parallel:
	@echo "Running RAPIDS macro-beats tests in parallel..."
	$(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-parallel-waves
run-parallel-waves:
	@echo "Running RAPIDS macro-beats tests in parallel with waveforms..."
	WAVES=1 $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# Run Targets - Scheduler Group
# ==============================================================================

.PHONY: run-scheduler-group
run-scheduler-group:
	@echo "Running beats_scheduler_group tests..."
	$(PYTEST) test_beats_scheduler_group.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-scheduler-group-waves
run-scheduler-group-waves:
	@echo "Running beats_scheduler_group tests with waveforms..."
	WAVES=1 $(PYTEST) test_beats_scheduler_group.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-scheduler-array
run-scheduler-array:
	@echo "Running beats_scheduler_group_array tests..."
	$(PYTEST) test_beats_scheduler_group_array.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-scheduler-array-waves
run-scheduler-array-waves:
	@echo "Running beats_scheduler_group_array tests with waveforms..."
	WAVES=1 $(PYTEST) test_beats_scheduler_group_array.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

# ==============================================================================
# Run Targets - Sink Datapath
# ==============================================================================

.PHONY: run-sink
run-sink:
	@echo "Running sink datapath tests..."
	$(PYTEST) test_sink_datapath.py test_sink_data_path_axis_test.py test_snk_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sink-waves
run-sink-waves:
	@echo "Running sink datapath tests with waveforms..."
	WAVES=1 $(PYTEST) test_sink_datapath.py test_sink_data_path_axis_test.py test_snk_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-snk-sram
run-snk-sram:
	@echo "Running snk_sram_controller tests..."
	$(PYTEST) test_snk_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-snk-sram-waves
run-snk-sram-waves:
	@echo "Running snk_sram_controller tests with waveforms..."
	WAVES=1 $(PYTEST) test_snk_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

# ==============================================================================
# Run Targets - Source Datapath
# ==============================================================================

.PHONY: run-source
run-source:
	@echo "Running source datapath tests..."
	$(PYTEST) test_source_datapath.py test_source_data_path_axis_test.py test_src_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-source-waves
run-source-waves:
	@echo "Running source datapath tests with waveforms..."
	WAVES=1 $(PYTEST) test_source_datapath.py test_source_data_path_axis_test.py test_src_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-src-sram
run-src-sram:
	@echo "Running src_sram_controller tests..."
	$(PYTEST) test_src_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-src-sram-waves
run-src-sram-waves:
	@echo "Running src_sram_controller tests with waveforms..."
	WAVES=1 $(PYTEST) test_src_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

# ==============================================================================
# REG_LEVEL Targets
# ==============================================================================

.PHONY: run-gate
run-gate:
	@echo "Running RAPIDS macro-beats tests at GATE level..."
	REG_LEVEL=GATE $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-gate-waves
run-gate-waves:
	@echo "Running RAPIDS macro-beats tests at GATE level with waveforms..."
	WAVES=1 REG_LEVEL=GATE $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-func
run-func:
	@echo "Running RAPIDS macro-beats tests at FUNC level..."
	REG_LEVEL=FUNC $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-func-waves
run-func-waves:
	@echo "Running RAPIDS macro-beats tests at FUNC level with waveforms..."
	WAVES=1 REG_LEVEL=FUNC $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-full
run-full:
	@echo "Running RAPIDS macro-beats tests at FULL level..."
	REG_LEVEL=FULL $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-full-waves
run-full-waves:
	@echo "Running RAPIDS macro-beats tests at FULL level with waveforms..."
	WAVES=1 REG_LEVEL=FULL $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

# ==============================================================================
# Development Targets
# ==============================================================================

.PHONY: ptw
ptw:
	@echo "Starting pytest-watch for RAPIDS macro-beats tests..."
	@echo "Tests will auto-rerun when files change. Press Ctrl+C to stop."
	@echo ""
	$(PTW) $(PTW_FLAGS) -- test_*.py $(PYTEST_VERBOSE)

# ==============================================================================
# Utility Targets
# ==============================================================================

.PHONY: collect
collect:
	@echo "Collecting RAPIDS macro-beats tests..."
	$(PYTEST) test_*.py --collect-only

.PHONY: clean
clean:
	@echo "Cleaning local artifacts..."
	rm -rf __pycache__ .pytest_cache *.pyc

.PHONY: clean-all
clean-all: clean
	@echo "Cleaning all test artifacts..."
	rm -rf logs local_sim_build sim_build
	find . -name "*.vcd" -delete
	find . -name "*.fst" -delete
	find . -name "results_*.xml" -delete
	@echo "All test artifacts cleaned."
