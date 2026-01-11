# ==============================================================================
# STREAM FUB Tests Makefile
# ==============================================================================
#
# Local test runner for FUB (Functional Unit Block) tests
#
# Usage:
#   cd $REPO_ROOT/projects/components/stream/dv/tests/fub
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
	@echo "STREAM FUB Tests Makefile"
	@echo "================================================================================"
	@echo ""
	@echo "RUN TARGETS (ALL TESTS):"
	@echo "  make run                  Run all FUB tests"
	@echo "  make run-waves            Run all FUB tests with waveforms"
	@echo "  make run-parallel         Run all FUB tests in parallel (48 workers)"
	@echo "  make run-parallel-waves   Run all FUB tests parallel with waveforms"
	@echo ""
	@echo "INDIVIDUAL MODULE TARGETS:"
	@echo "  make run-apb              Run APB to descriptor tests"
	@echo "  make run-apb-parallel     Run APB to descriptor tests in parallel"
	@echo "  make run-apb-parallel-waves  Run APB parallel with waveforms"
	@echo "  make run-sram             Run SRAM controller tests"
	@echo "  make run-sram-waves       Run SRAM controller tests with waveforms"
	@echo "  make run-sram-alloc       Run SRAM allocation tests"
	@echo "  make run-scheduler        Run scheduler tests (default: func level, parallel)"
	@echo "  make run-descriptor       Run descriptor engine tests"
	@echo "  make run-latency-bridge   Run stream latency bridge tests"
	@echo "  make run-perf             Run performance profiler tests"
	@echo ""
	@echo "SCHEDULER TARGETS (gate/func/full - always parallel, waves optional):"
	@echo "  make run-scheduler-gate        Run scheduler at GATE level (parallel, 7 tests)"
	@echo "  make run-scheduler-gate-waves  Run scheduler at GATE with waveforms"
	@echo "  make run-scheduler-func        Run scheduler at FUNC level (parallel, 7 tests)"
	@echo "  make run-scheduler-func-waves  Run scheduler at FUNC with waveforms"
	@echo "  make run-scheduler-full        Run scheduler at FULL level (parallel, 7 tests)"
	@echo "  make run-scheduler-full-waves  Run scheduler at FULL with waveforms"
	@echo ""
	@echo "TEST_LEVEL TARGETS (SRAM Controller - gate/func/full):"
	@echo "  make run-sram-gate        Run SRAM at GATE level (quick, 16 beats)"
	@echo "  make run-sram-gate-waves  Run SRAM at GATE with waveforms"
	@echo "  make run-sram-func        Run SRAM at FUNC level (64 beats)"
	@echo "  make run-sram-func-waves  Run SRAM at FUNC with waveforms"
	@echo "  make run-sram-full        Run SRAM at FULL level (256 beats)"
	@echo "  make run-sram-full-waves  Run SRAM at FULL with waveforms"
	@echo ""
	@echo "REG_LEVEL TARGETS:"
	@echo "  make run-gate                   Run FUB tests at GATE level (quick)"
	@echo "  make run-gate-waves             Run FUB tests at GATE level with waveforms"
	@echo "  make run-gate-parallel          Run FUB tests at GATE level in parallel"
	@echo "  make run-gate-parallel-waves    Run FUB tests at GATE level parallel + waves"
	@echo "  make run-func                   Run FUB tests at FUNC level (default)"
	@echo "  make run-func-waves             Run FUB tests at FUNC level with waveforms"
	@echo "  make run-func-parallel          Run FUB tests at FUNC level in parallel"
	@echo "  make run-func-parallel-waves    Run FUB tests at FUNC level parallel + waves"
	@echo "  make run-full                   Run FUB tests at FULL level (comprehensive)"
	@echo "  make run-full-waves             Run FUB tests at FULL level with waveforms"
	@echo "  make run-full-parallel          Run FUB tests at FULL level in parallel"
	@echo "  make run-full-parallel-waves    Run FUB tests at FULL level parallel + waves"
	@echo ""
	@echo "COVERAGE TARGETS:"
	@echo "  make run-coverage           Run all FUB tests with coverage"
	@echo "  make run-coverage-parallel  Run FUB tests with coverage (parallel)"
	@echo "  make run-coverage-full      Run FUB tests at FULL level with coverage (parallel)"
	@echo "  make coverage-report        Generate report with legal coverage filtering"
	@echo "  make clean-coverage         Clean coverage data"
	@echo "  make fresh-coverage         Clean + run + report (default level)"
	@echo "  make fresh-coverage-full    Clean + run FULL + report (recommended)"
	@echo ""
	@echo "UTILITY TARGETS:"
	@echo "  make ptw                  Run pytest-watch (auto-rerun on changes)"
	@echo "  make collect              Collect (don't run) tests"
	@echo "  make clean                Clean local artifacts"
	@echo "  make clean-all            Clean all test artifacts"
	@echo "  make clean-logs           Clean stale log files only"
	@echo ""
	@echo "================================================================================"

# ==============================================================================
# Run Targets - All Tests
# ==============================================================================

.PHONY: run
run:
	@echo "Running STREAM FUB tests..."
	$(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-waves
run-waves:
	@echo "Running STREAM FUB tests with waveforms..."
	WAVES=1 $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-parallel
run-parallel:
	@echo "Running STREAM FUB tests in parallel..."
	$(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-parallel-waves
run-parallel-waves:
	@echo "Running STREAM FUB tests in parallel with waveforms..."
	WAVES=1 $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# Run Targets - SRAM Controller
# ==============================================================================

.PHONY: run-sram
run-sram:
	@echo "Running SRAM controller tests..."
	$(PYTEST) test_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sram-waves
run-sram-waves:
	@echo "Running SRAM controller tests with waveforms..."
	WAVES=1 $(PYTEST) test_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sram-parallel
run-sram-parallel:
	@echo "Running SRAM controller tests in parallel (48 workers)..."
	$(PYTEST) test_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-sram-parallel-waves
run-sram-parallel-waves:
	@echo "Running SRAM controller tests in parallel with waveforms..."
	WAVES=1 $(PYTEST) test_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# TEST_LEVEL Targets - SRAM Controller (gate/func/full)
# ==============================================================================

.PHONY: run-sram-gate
run-sram-gate:
	@echo "Running SRAM controller at GATE level (16 beats, 2 channels)..."
	TEST_LEVEL=gate $(PYTEST) test_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sram-gate-waves
run-sram-gate-waves:
	@echo "Running SRAM controller at GATE level with waveforms..."
	WAVES=1 TEST_LEVEL=gate $(PYTEST) test_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sram-gate-parallel
run-sram-gate-parallel:
	@echo "Running SRAM controller at GATE level in parallel..."
	TEST_LEVEL=gate $(PYTEST) test_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-sram-func
run-sram-func:
	@echo "Running SRAM controller at FUNC level (64 beats, 4 channels)..."
	TEST_LEVEL=func $(PYTEST) test_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sram-func-waves
run-sram-func-waves:
	@echo "Running SRAM controller at FUNC level with waveforms..."
	WAVES=1 TEST_LEVEL=func $(PYTEST) test_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sram-func-parallel
run-sram-func-parallel:
	@echo "Running SRAM controller at FUNC level in parallel..."
	TEST_LEVEL=func $(PYTEST) test_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-sram-full
run-sram-full:
	@echo "Running SRAM controller at FULL level (256 beats, 8 channels)..."
	TEST_LEVEL=full $(PYTEST) test_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sram-full-waves
run-sram-full-waves:
	@echo "Running SRAM controller at FULL level with waveforms..."
	WAVES=1 TEST_LEVEL=full $(PYTEST) test_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sram-full-parallel
run-sram-full-parallel:
	@echo "Running SRAM controller at FULL level in parallel..."
	TEST_LEVEL=full $(PYTEST) test_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# Run Targets - Individual Modules
# ==============================================================================

.PHONY: run-sram-alloc
run-sram-alloc:
	@echo "Running SRAM allocation tests..."
	$(PYTEST) test_sram_controller_alloc.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

# ==============================================================================
# Scheduler Test Targets (gate/func/full with parallel execution)
# ==============================================================================

.PHONY: run-scheduler
run-scheduler: run-scheduler-func
	@echo "✓ Scheduler tests completed (default: func level)"

# Gate Level - Quick regression (7 tests, parallel)
.PHONY: run-scheduler-gate
run-scheduler-gate:
	@echo "Running scheduler tests at GATE level (parallel)..."
	TEST_LEVEL=gate $(PYTEST) test_scheduler.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-scheduler-gate-waves
run-scheduler-gate-waves:
	@echo "Running scheduler tests at GATE level (parallel + waves)..."
	WAVES=1 TEST_LEVEL=gate $(PYTEST) test_scheduler.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# Func Level - Functional validation (7 tests, parallel)
.PHONY: run-scheduler-func
run-scheduler-func:
	@echo "Running scheduler tests at FUNC level (parallel)..."
	TEST_LEVEL=func $(PYTEST) test_scheduler.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-scheduler-func-waves
run-scheduler-func-waves:
	@echo "Running scheduler tests at FUNC level (parallel + waves)..."
	WAVES=1 TEST_LEVEL=func $(PYTEST) test_scheduler.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# Full Level - Comprehensive coverage (7 tests, parallel)
.PHONY: run-scheduler-full
run-scheduler-full:
	@echo "Running scheduler tests at FULL level (parallel)..."
	TEST_LEVEL=full $(PYTEST) test_scheduler.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-scheduler-full-waves
run-scheduler-full-waves:
	@echo "Running scheduler tests at FULL level (parallel + waves)..."
	WAVES=1 TEST_LEVEL=full $(PYTEST) test_scheduler.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-descriptor
run-descriptor:
	@echo "Running descriptor engine tests..."
	$(PYTEST) test_descriptor_engine.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-latency-bridge
run-latency-bridge:
	@echo "Running stream latency bridge tests..."
	$(PYTEST) test_stream_latency_bridge.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-perf
run-perf:
	@echo "Running performance profiler tests..."
	$(PYTEST) test_perf_profiler.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-apb
run-apb:
	@echo "Running APB to descriptor tests..."
	$(PYTEST) test_apbtodescr.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-apb-parallel
run-apb-parallel:
	@echo "Running APB to descriptor tests in parallel..."
	$(PYTEST) test_apbtodescr.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST)

.PHONY: run-apb-parallel-waves
run-apb-parallel-waves:
	@echo "Running APB to descriptor tests in parallel with waveforms..."
	WAVES=1 $(PYTEST) test_apbtodescr.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST)

# ==============================================================================
# REG_LEVEL Targets
# ==============================================================================

.PHONY: run-gate
run-gate:
	@echo "Running STREAM FUB tests at GATE level..."
	REG_LEVEL=GATE $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-gate-waves
run-gate-waves:
	@echo "Running STREAM FUB tests at GATE level with waveforms..."
	WAVES=1 REG_LEVEL=GATE $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-gate-parallel
run-gate-parallel:
	@echo "Running STREAM FUB tests at GATE level in parallel..."
	REG_LEVEL=GATE $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-gate-parallel-waves
run-gate-parallel-waves:
	@echo "Running STREAM FUB tests at GATE level in parallel with waveforms..."
	WAVES=1 REG_LEVEL=GATE $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-func
run-func:
	@echo "Running STREAM FUB tests at FUNC level..."
	REG_LEVEL=FUNC $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-func-waves
run-func-waves:
	@echo "Running STREAM FUB tests at FUNC level with waveforms..."
	WAVES=1 REG_LEVEL=FUNC $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-func-parallel
run-func-parallel:
	@echo "Running STREAM FUB tests at FUNC level in parallel..."
	REG_LEVEL=FUNC $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-func-parallel-waves
run-func-parallel-waves:
	@echo "Running STREAM FUB tests at FUNC level in parallel with waveforms..."
	WAVES=1 REG_LEVEL=FUNC $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-full
run-full:
	@echo "Running STREAM FUB tests at FULL level..."
	REG_LEVEL=FULL $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-full-waves
run-full-waves:
	@echo "Running STREAM FUB tests at FULL level with waveforms..."
	WAVES=1 REG_LEVEL=FULL $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-full-parallel
run-full-parallel:
	@echo "Running STREAM FUB tests at FULL level in parallel..."
	REG_LEVEL=FULL $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-full-parallel-waves
run-full-parallel-waves:
	@echo "Running STREAM FUB tests at FULL level in parallel with waveforms..."
	WAVES=1 REG_LEVEL=FULL $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# Development Targets
# ==============================================================================

.PHONY: ptw
ptw:
	@echo "Starting pytest-watch for STREAM FUB tests..."
	@echo "Tests will auto-rerun when files change. Press Ctrl+C to stop."
	@echo ""
	$(PTW) $(PTW_FLAGS) -- test_*.py $(PYTEST_VERBOSE)

# ==============================================================================
# Utility Targets
# ==============================================================================

.PHONY: collect
collect:
	@echo "Collecting STREAM FUB tests..."
	$(PYTEST) test_*.py --collect-only

.PHONY: clean
clean:
	@echo "Cleaning local artifacts..."
	rm -rf __pycache__ .pytest_cache *.pyc

.PHONY: clean-logs
clean-logs:
	@echo "Cleaning stale log files..."
	@echo "Removing old test_datapath*.log files (tests moved to macro/ directory)..."
	rm -f logs/test_datapath*.log
	@echo "Stale logs cleaned."

.PHONY: clean-all
clean-all: clean
	@echo "Cleaning all test artifacts..."
	rm -rf logs local_sim_build sim_build
	find . -name "*.vcd" -delete
	find . -name "*.fst" -delete
	find . -name "results_*.xml" -delete
	@echo "All test artifacts cleaned (GTKW preserved)."

# ==============================================================================
# Coverage Targets
# ==============================================================================

.PHONY: run-coverage
run-coverage:
	@echo "Running STREAM FUB tests with coverage..."
	SIM=verilator COVERAGE=1 $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-coverage-parallel
run-coverage-parallel:
	@echo "Running STREAM FUB tests with coverage (parallel)..."
	SIM=verilator COVERAGE=1 $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-coverage-full
run-coverage-full:
	@echo "Running STREAM FUB tests with coverage at FULL level (parallel)..."
	SIM=verilator COVERAGE=1 TEST_LEVEL=full $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: coverage-report
coverage-report:
	@echo "Generating coverage report (with legal coverage analysis)..."
	python3 $(REPO_ROOT)/projects/components/stream/bin/generate_coverage_report.py --coverage-dir coverage_data --legal

.PHONY: clean-coverage
clean-coverage:
	@echo "Cleaning coverage data..."
	rm -rf coverage_data
	@echo "Coverage data cleaned."

.PHONY: fresh-coverage
fresh-coverage: clean-coverage run-coverage coverage-report
	@echo "Fresh coverage run complete."

.PHONY: fresh-coverage-full
fresh-coverage-full: clean-coverage run-coverage-full coverage-report
	@echo "Fresh full coverage run complete."
