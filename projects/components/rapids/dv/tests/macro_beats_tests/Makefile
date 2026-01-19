# ==============================================================================
# RAPIDS Macro-Beats Tests Makefile
# ==============================================================================
#
# Local test runner for macro-level beats tests (AXIS-based DMA architecture)
#
# RTL Modules Available:
#   - scheduler_group_beats          : Scheduler group for beats architecture
#   - scheduler_group_array_beats    : Array of scheduler groups
#   - snk_data_path_beats            : Sink datapath (network to memory)
#   - snk_data_path_axis_beats       : Sink datapath with AXIS interface
#   - snk_data_path_axis_test_beats  : Sink datapath AXIS test wrapper
#   - snk_sram_controller_beats      : Sink SRAM controller
#   - src_data_path_beats            : Source datapath (memory to network)
#   - src_data_path_axis_beats       : Source datapath with AXIS interface
#   - src_data_path_axis_test_beats  : Source datapath AXIS test wrapper
#   - src_sram_controller_beats      : Source SRAM controller
#   - rapids_core_beats              : Full RAPIDS core integration
#
# Usage:
#   cd $REPO_ROOT/projects/components/rapids/dv/tests/macro_beats_tests
#   make <target>
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
PYTEST_XDIST = -n auto
PYTEST_TBSTYLE = --tb=short
PYTEST_RERUNS = --reruns 3 --reruns-delay 1

# Simulator (verilator by default)
SIM ?= verilator

# Coverage options
COVERAGE ?= 0
COVERAGE_LEGAL ?= 0
COV_DIR = coverage_data
COV_REPORT_DIR = coverage_report

# Pytest-watch options
PTW = ptw
PTW_FLAGS = --runner "pytest --maxfail=1"

# Test files (matching actual RTL module names with _beats suffix)
TEST_SCHED_GROUP = test_scheduler_group_beats.py
TEST_SCHED_ARRAY = test_scheduler_group_array_beats.py
TEST_SNK_DATAPATH = test_snk_data_path_beats.py
TEST_SNK_AXIS = test_snk_data_path_axis_beats.py
TEST_SNK_SRAM = test_snk_sram_controller_beats.py
TEST_SRC_DATAPATH = test_src_data_path_beats.py
TEST_SRC_AXIS = test_src_data_path_axis_beats.py
TEST_SRC_SRAM = test_src_sram_controller_beats.py
TEST_CORE = test_rapids_core_beats.py

# All test files
ALL_TESTS = $(TEST_SCHED_GROUP) $(TEST_SCHED_ARRAY) \
            $(TEST_SNK_DATAPATH) $(TEST_SNK_AXIS) $(TEST_SNK_SRAM) \
            $(TEST_SRC_DATAPATH) $(TEST_SRC_AXIS) $(TEST_SRC_SRAM) \
            $(TEST_CORE)

# Default target
.DEFAULT_GOAL := help

# ==============================================================================
# Help Target
# ==============================================================================

.PHONY: help
help:
	@echo "================================================================================"
	@echo "RAPIDS Macro-Beats Tests Makefile"
	@echo "================================================================================"
	@echo ""
	@echo "QUICK RUN TARGETS:"
	@echo "  make run                        Run all available tests"
	@echo "  make run-waves                  Run all tests with waveforms"
	@echo "  make run-parallel               Run all tests in parallel"
	@echo "  make run-all                    Run all tests at FUNC level"
	@echo ""
	@echo "SCHEDULER GROUP TARGETS:"
	@echo "  make run-sched-group            Run scheduler_group_beats tests"
	@echo "  make run-sched-group-waves      Run scheduler_group_beats with waves"
	@echo "  make run-sched-array            Run scheduler_group_array_beats tests"
	@echo "  make run-sched-array-waves      Run scheduler_group_array_beats with waves"
	@echo ""
	@echo "SINK DATAPATH TARGETS:"
	@echo "  make run-snk                    Run all sink datapath tests"
	@echo "  make run-snk-waves              Run all sink tests with waves"
	@echo "  make run-snk-datapath           Run snk_data_path_beats tests"
	@echo "  make run-snk-axis               Run snk_data_path_axis_beats tests"
	@echo "  make run-snk-sram               Run snk_sram_controller_beats tests"
	@echo ""
	@echo "SOURCE DATAPATH TARGETS:"
	@echo "  make run-src                    Run all source datapath tests"
	@echo "  make run-src-waves              Run all source tests with waves"
	@echo "  make run-src-datapath           Run src_data_path_beats tests"
	@echo "  make run-src-axis               Run src_data_path_axis_beats tests"
	@echo "  make run-src-sram               Run src_sram_controller_beats tests"
	@echo ""
	@echo "RAPIDS CORE TARGETS:"
	@echo "  make run-core                   Run rapids_core_beats tests"
	@echo "  make run-core-waves             Run rapids_core_beats with waves"
	@echo "  make run-core-gate              Run core tests at GATE level"
	@echo "  make run-core-func              Run core tests at FUNC level"
	@echo "  make run-core-full              Run core tests at FULL level"
	@echo ""
	@echo "TEST_LEVEL TARGETS (applies to all tests):"
	@echo "  make run-gate                   Run all tests at GATE level (quick)"
	@echo "  make run-gate-waves             Run GATE level with waveforms"
	@echo "  make run-func                   Run all tests at FUNC level"
	@echo "  make run-func-waves             Run FUNC level with waveforms"
	@echo "  make run-full                   Run all tests at FULL level"
	@echo "  make run-full-waves             Run FULL level with waveforms"
	@echo "  make run-full-parallel          Run FULL level in parallel"
	@echo "  make run-full-parallel-waves    Run FULL level parallel with waves"
	@echo ""
	@echo "COVERAGE TARGETS:"
	@echo "  make run-coverage               Run tests with Verilator coverage"
	@echo "  make run-coverage-full          Run FULL tests with coverage"
	@echo "  make coverage-report            Generate coverage HTML report"
	@echo "  make coverage-annotate          Generate annotated source files"
	@echo "  make coverage-summary           Show coverage summary"
	@echo "  make clean-coverage             Clean coverage data"
	@echo ""
	@echo "UTILITY TARGETS:"
	@echo "  make collect                    Collect (don't run) all tests"
	@echo "  make list-tests                 List available test files"
	@echo "  make ptw                        Run pytest-watch (auto-rerun)"
	@echo "  make clean                      Clean local artifacts"
	@echo "  make clean-all                  Clean all test artifacts"
	@echo ""
	@echo "ENVIRONMENT VARIABLES:"
	@echo "  SIM=verilator|icarus            Simulator (default: verilator)"
	@echo "  WAVES=1                         Enable waveform generation"
	@echo "  TEST_LEVEL=gate|func|full       Test intensity level"
	@echo "  COVERAGE=1                      Enable Verilator coverage"
	@echo "  COVERAGE_LEGAL=1                Enable legal-point coverage"
	@echo ""
	@echo "================================================================================"

# ==============================================================================
# Quick Run Targets
# ==============================================================================

.PHONY: run
run:
	@echo "Running all RAPIDS macro-beats tests..."
	@if ls test_*.py 1> /dev/null 2>&1; then \
		SIM=$(SIM) TEST_LEVEL=func $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE); \
	else \
		echo "No test files found. Create test_*.py files to run tests."; \
	fi

.PHONY: run-waves
run-waves:
	@echo "Running all RAPIDS macro-beats tests with waveforms..."
	@if ls test_*.py 1> /dev/null 2>&1; then \
		SIM=$(SIM) WAVES=1 TEST_LEVEL=func $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE); \
	else \
		echo "No test files found."; \
	fi

.PHONY: run-parallel
run-parallel:
	@echo "Running all RAPIDS macro-beats tests in parallel..."
	@if ls test_*.py 1> /dev/null 2>&1; then \
		SIM=$(SIM) TEST_LEVEL=func $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS); \
	else \
		echo "No test files found."; \
	fi

.PHONY: run-all
run-all: run

# ==============================================================================
# Scheduler Group Targets
# ==============================================================================

.PHONY: run-sched-group
run-sched-group:
	@echo "Running scheduler_group_beats tests..."
	@if [ -f $(TEST_SCHED_GROUP) ]; then \
		SIM=$(SIM) TEST_LEVEL=func $(PYTEST) $(TEST_SCHED_GROUP) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE); \
	else \
		echo "Test file $(TEST_SCHED_GROUP) not found."; \
	fi

.PHONY: run-sched-group-waves
run-sched-group-waves:
	@echo "Running scheduler_group_beats tests with waveforms..."
	@if [ -f $(TEST_SCHED_GROUP) ]; then \
		SIM=$(SIM) WAVES=1 TEST_LEVEL=func $(PYTEST) $(TEST_SCHED_GROUP) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE); \
	else \
		echo "Test file $(TEST_SCHED_GROUP) not found."; \
	fi

.PHONY: run-sched-array
run-sched-array:
	@echo "Running scheduler_group_array_beats tests..."
	@if [ -f $(TEST_SCHED_ARRAY) ]; then \
		SIM=$(SIM) TEST_LEVEL=func $(PYTEST) $(TEST_SCHED_ARRAY) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE); \
	else \
		echo "Test file $(TEST_SCHED_ARRAY) not found."; \
	fi

.PHONY: run-sched-array-waves
run-sched-array-waves:
	@echo "Running scheduler_group_array_beats tests with waveforms..."
	@if [ -f $(TEST_SCHED_ARRAY) ]; then \
		SIM=$(SIM) WAVES=1 TEST_LEVEL=func $(PYTEST) $(TEST_SCHED_ARRAY) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE); \
	else \
		echo "Test file $(TEST_SCHED_ARRAY) not found."; \
	fi

# ==============================================================================
# Sink Datapath Targets
# ==============================================================================

.PHONY: run-snk
run-snk:
	@echo "Running all sink datapath tests..."
	@tests=""; \
	for f in $(TEST_SNK_DATAPATH) $(TEST_SNK_AXIS) $(TEST_SNK_SRAM); do \
		[ -f "$$f" ] && tests="$$tests $$f"; \
	done; \
	if [ -n "$$tests" ]; then \
		SIM=$(SIM) TEST_LEVEL=func $(PYTEST) $$tests $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE); \
	else \
		echo "No sink test files found."; \
	fi

.PHONY: run-snk-waves
run-snk-waves:
	@echo "Running all sink datapath tests with waveforms..."
	@tests=""; \
	for f in $(TEST_SNK_DATAPATH) $(TEST_SNK_AXIS) $(TEST_SNK_SRAM); do \
		[ -f "$$f" ] && tests="$$tests $$f"; \
	done; \
	if [ -n "$$tests" ]; then \
		SIM=$(SIM) WAVES=1 TEST_LEVEL=func $(PYTEST) $$tests $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE); \
	else \
		echo "No sink test files found."; \
	fi

.PHONY: run-snk-datapath
run-snk-datapath:
	@echo "Running snk_data_path_beats tests..."
	@if [ -f $(TEST_SNK_DATAPATH) ]; then \
		SIM=$(SIM) TEST_LEVEL=func $(PYTEST) $(TEST_SNK_DATAPATH) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE); \
	else \
		echo "Test file $(TEST_SNK_DATAPATH) not found."; \
	fi

.PHONY: run-snk-axis
run-snk-axis:
	@echo "Running snk_data_path_axis_beats tests..."
	@if [ -f $(TEST_SNK_AXIS) ]; then \
		SIM=$(SIM) TEST_LEVEL=func $(PYTEST) $(TEST_SNK_AXIS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE); \
	else \
		echo "Test file $(TEST_SNK_AXIS) not found."; \
	fi

.PHONY: run-snk-sram
run-snk-sram:
	@echo "Running snk_sram_controller_beats tests..."
	@if [ -f $(TEST_SNK_SRAM) ]; then \
		SIM=$(SIM) TEST_LEVEL=func $(PYTEST) $(TEST_SNK_SRAM) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE); \
	else \
		echo "Test file $(TEST_SNK_SRAM) not found."; \
	fi

# ==============================================================================
# Source Datapath Targets
# ==============================================================================

.PHONY: run-src
run-src:
	@echo "Running all source datapath tests..."
	@tests=""; \
	for f in $(TEST_SRC_DATAPATH) $(TEST_SRC_AXIS) $(TEST_SRC_SRAM); do \
		[ -f "$$f" ] && tests="$$tests $$f"; \
	done; \
	if [ -n "$$tests" ]; then \
		SIM=$(SIM) TEST_LEVEL=func $(PYTEST) $$tests $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE); \
	else \
		echo "No source test files found."; \
	fi

.PHONY: run-src-waves
run-src-waves:
	@echo "Running all source datapath tests with waveforms..."
	@tests=""; \
	for f in $(TEST_SRC_DATAPATH) $(TEST_SRC_AXIS) $(TEST_SRC_SRAM); do \
		[ -f "$$f" ] && tests="$$tests $$f"; \
	done; \
	if [ -n "$$tests" ]; then \
		SIM=$(SIM) WAVES=1 TEST_LEVEL=func $(PYTEST) $$tests $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE); \
	else \
		echo "No source test files found."; \
	fi

.PHONY: run-src-datapath
run-src-datapath:
	@echo "Running src_data_path_beats tests..."
	@if [ -f $(TEST_SRC_DATAPATH) ]; then \
		SIM=$(SIM) TEST_LEVEL=func $(PYTEST) $(TEST_SRC_DATAPATH) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE); \
	else \
		echo "Test file $(TEST_SRC_DATAPATH) not found."; \
	fi

.PHONY: run-src-axis
run-src-axis:
	@echo "Running src_data_path_axis_beats tests..."
	@if [ -f $(TEST_SRC_AXIS) ]; then \
		SIM=$(SIM) TEST_LEVEL=func $(PYTEST) $(TEST_SRC_AXIS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE); \
	else \
		echo "Test file $(TEST_SRC_AXIS) not found."; \
	fi

.PHONY: run-src-sram
run-src-sram:
	@echo "Running src_sram_controller_beats tests..."
	@if [ -f $(TEST_SRC_SRAM) ]; then \
		SIM=$(SIM) TEST_LEVEL=func $(PYTEST) $(TEST_SRC_SRAM) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE); \
	else \
		echo "Test file $(TEST_SRC_SRAM) not found."; \
	fi

# ==============================================================================
# RAPIDS Core Targets
# ==============================================================================

.PHONY: run-core
run-core:
	@echo "Running rapids_core_beats tests..."
	@if [ -f $(TEST_CORE) ]; then \
		SIM=$(SIM) TEST_LEVEL=func $(PYTEST) $(TEST_CORE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE); \
	else \
		echo "Test file $(TEST_CORE) not found."; \
	fi

.PHONY: run-core-waves
run-core-waves:
	@echo "Running rapids_core_beats tests with waveforms..."
	@if [ -f $(TEST_CORE) ]; then \
		SIM=$(SIM) WAVES=1 TEST_LEVEL=func $(PYTEST) $(TEST_CORE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE); \
	else \
		echo "Test file $(TEST_CORE) not found."; \
	fi

.PHONY: run-core-gate
run-core-gate:
	@echo "Running rapids_core_beats tests at GATE level..."
	@if [ -f $(TEST_CORE) ]; then \
		SIM=$(SIM) TEST_LEVEL=gate $(PYTEST) $(TEST_CORE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE); \
	else \
		echo "Test file $(TEST_CORE) not found."; \
	fi

.PHONY: run-core-func
run-core-func:
	@echo "Running rapids_core_beats tests at FUNC level..."
	@if [ -f $(TEST_CORE) ]; then \
		SIM=$(SIM) TEST_LEVEL=func $(PYTEST) $(TEST_CORE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE); \
	else \
		echo "Test file $(TEST_CORE) not found."; \
	fi

.PHONY: run-core-full
run-core-full:
	@echo "Running rapids_core_beats tests at FULL level..."
	@if [ -f $(TEST_CORE) ]; then \
		SIM=$(SIM) TEST_LEVEL=full $(PYTEST) $(TEST_CORE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE); \
	else \
		echo "Test file $(TEST_CORE) not found."; \
	fi

# ==============================================================================
# TEST_LEVEL Targets (All Tests)
# ==============================================================================

.PHONY: run-gate
run-gate:
	@echo "Running all tests at GATE level..."
	@if ls test_*.py 1> /dev/null 2>&1; then \
		SIM=$(SIM) TEST_LEVEL=gate $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE); \
	else \
		echo "No test files found."; \
	fi

.PHONY: run-gate-waves
run-gate-waves:
	@echo "Running all tests at GATE level with waveforms..."
	@if ls test_*.py 1> /dev/null 2>&1; then \
		SIM=$(SIM) WAVES=1 TEST_LEVEL=gate $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE); \
	else \
		echo "No test files found."; \
	fi

.PHONY: run-func
run-func:
	@echo "Running all tests at FUNC level..."
	@if ls test_*.py 1> /dev/null 2>&1; then \
		SIM=$(SIM) TEST_LEVEL=func $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE); \
	else \
		echo "No test files found."; \
	fi

.PHONY: run-func-waves
run-func-waves:
	@echo "Running all tests at FUNC level with waveforms..."
	@if ls test_*.py 1> /dev/null 2>&1; then \
		SIM=$(SIM) WAVES=1 TEST_LEVEL=func $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE); \
	else \
		echo "No test files found."; \
	fi

.PHONY: run-full
run-full:
	@echo "Running all tests at FULL level..."
	@if ls test_*.py 1> /dev/null 2>&1; then \
		SIM=$(SIM) TEST_LEVEL=full $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE); \
	else \
		echo "No test files found."; \
	fi

.PHONY: run-full-waves
run-full-waves:
	@echo "Running all tests at FULL level with waveforms..."
	@if ls test_*.py 1> /dev/null 2>&1; then \
		SIM=$(SIM) WAVES=1 TEST_LEVEL=full $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE); \
	else \
		echo "No test files found."; \
	fi

.PHONY: run-full-parallel
run-full-parallel:
	@echo "Running all tests at FULL level in parallel..."
	@if ls test_*.py 1> /dev/null 2>&1; then \
		SIM=$(SIM) TEST_LEVEL=full $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS); \
	else \
		echo "No test files found."; \
	fi

.PHONY: run-full-parallel-waves
run-full-parallel-waves:
	@echo "Running all tests at FULL level in parallel with waveforms..."
	@if ls test_*.py 1> /dev/null 2>&1; then \
		SIM=$(SIM) WAVES=1 TEST_LEVEL=full $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS); \
	else \
		echo "No test files found."; \
	fi

# ==============================================================================
# Coverage Targets (Verilator)
# ==============================================================================

.PHONY: run-coverage
run-coverage:
	@echo "Running tests with Verilator coverage..."
	@if ls test_*.py 1> /dev/null 2>&1; then \
		SIM=verilator COVERAGE=1 TEST_LEVEL=func $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE); \
	else \
		echo "No test files found."; \
	fi

.PHONY: run-coverage-full
run-coverage-full:
	@echo "Running FULL tests with Verilator coverage..."
	@if ls test_*.py 1> /dev/null 2>&1; then \
		SIM=verilator COVERAGE=1 COVERAGE_LEGAL=1 TEST_LEVEL=full $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE); \
	else \
		echo "No test files found."; \
	fi

.PHONY: coverage-report
coverage-report:
	@echo "Generating coverage HTML report..."
	@mkdir -p $(COV_REPORT_DIR)
	@if ls local_sim_build/*/coverage.dat 1> /dev/null 2>&1; then \
		verilator_coverage --write-info $(COV_DIR)/merged.info local_sim_build/*/coverage.dat; \
		genhtml $(COV_DIR)/merged.info -o $(COV_REPORT_DIR) --title "RAPIDS Beats Coverage"; \
		echo "Coverage report generated in $(COV_REPORT_DIR)/index.html"; \
	else \
		echo "No coverage data found. Run tests with COVERAGE=1 first."; \
	fi

.PHONY: coverage-annotate
coverage-annotate:
	@echo "Generating annotated source files..."
	@mkdir -p $(COV_DIR)/annotate
	@if ls local_sim_build/*/coverage.dat 1> /dev/null 2>&1; then \
		verilator_coverage --annotate $(COV_DIR)/annotate local_sim_build/*/coverage.dat; \
		echo "Annotated files in $(COV_DIR)/annotate/"; \
	else \
		echo "No coverage data found. Run tests with COVERAGE=1 first."; \
	fi

.PHONY: coverage-summary
coverage-summary:
	@echo "Coverage summary:"
	@if ls local_sim_build/*/coverage.dat 1> /dev/null 2>&1; then \
		verilator_coverage --rank local_sim_build/*/coverage.dat | head -50; \
	else \
		echo "No coverage data found. Run tests with COVERAGE=1 first."; \
	fi

.PHONY: clean-coverage
clean-coverage:
	@echo "Cleaning coverage data..."
	rm -rf $(COV_DIR) $(COV_REPORT_DIR)
	find . -name "coverage.dat" -delete

# ==============================================================================
# Utility Targets
# ==============================================================================

.PHONY: collect
collect:
	@echo "Collecting all RAPIDS macro-beats tests..."
	@if ls test_*.py 1> /dev/null 2>&1; then \
		$(PYTEST) test_*.py --collect-only; \
	else \
		echo "No test files found."; \
	fi

.PHONY: list-tests
list-tests:
	@echo "Test files in this directory:"
	@echo "-----------------------------"
	@ls -1 test_*.py 2>/dev/null || echo "  (no test files found)"
	@echo ""
	@echo "Expected test files (based on RTL modules):"
	@echo "--------------------------------------------"
	@for f in $(ALL_TESTS); do \
		if [ -f "$$f" ]; then \
			echo "  [EXISTS] $$f"; \
		else \
			echo "  [MISSING] $$f"; \
		fi; \
	done

.PHONY: ptw
ptw:
	@echo "Starting pytest-watch for RAPIDS macro-beats tests..."
	@echo "Tests will auto-rerun when files change. Press Ctrl+C to stop."
	@if ls test_*.py 1> /dev/null 2>&1; then \
		$(PTW) $(PTW_FLAGS) -- test_*.py $(PYTEST_VERBOSE); \
	else \
		echo "No test files found."; \
	fi

.PHONY: clean
clean:
	@echo "Cleaning local artifacts..."
	rm -rf __pycache__ .pytest_cache *.pyc

.PHONY: clean-all
clean-all: clean clean-coverage
	@echo "Cleaning all test artifacts..."
	rm -rf logs local_sim_build sim_build
	find . -name "*.vcd" -delete
	find . -name "*.fst" -delete
	find . -name "results_*.xml" -delete
	@echo "All test artifacts cleaned."
