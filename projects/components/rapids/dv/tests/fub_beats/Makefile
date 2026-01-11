# ==============================================================================
# RAPIDS FUB-Beats (AXIS-Based) Tests Makefile
# ==============================================================================
#
# Local test runner for FUB-Beats tests using AXIS-based interfaces:
# - scheduler
# - descriptor_engine
# - beats_alloc_ctrl
# - beats_drain_ctrl
# - beats_latency_bridge
#
# Usage:
#   cd $REPO_ROOT/projects/components/rapids/dv/tests/fub_beats
#   make <target>
#
# Quick start:
#   make help           - Show available targets
#   make run            - Run all FUB-Beats tests
#   make run-scheduler  - Run scheduler tests only
#   make run-desc       - Run descriptor_engine tests only
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
	@echo "RAPIDS FUB-Beats (AXIS-Based) Tests Makefile"
	@echo "================================================================================"
	@echo ""
	@echo "RUN TARGETS (ALL TESTS):"
	@echo "  make run                  Run all FUB-Beats tests"
	@echo "  make run-waves            Run all FUB-Beats tests with waveforms"
	@echo "  make run-parallel         Run all FUB-Beats tests in parallel (48 workers)"
	@echo "  make run-parallel-waves   Run all FUB-Beats tests parallel with waveforms"
	@echo ""
	@echo "INDIVIDUAL MODULE TARGETS:"
	@echo "  make run-scheduler        Run scheduler tests"
	@echo "  make run-scheduler-waves  Run scheduler tests with waveforms"
	@echo "  make run-desc             Run descriptor_engine tests"
	@echo "  make run-desc-waves       Run descriptor_engine tests with waveforms"
	@echo "  make run-alloc            Run beats_alloc_ctrl tests"
	@echo "  make run-drain            Run beats_drain_ctrl tests"
	@echo "  make run-bridge           Run beats_latency_bridge tests"
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
	@echo "Running RAPIDS FUB-Beats tests..."
	$(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-waves
run-waves:
	@echo "Running RAPIDS FUB-Beats tests with waveforms..."
	WAVES=1 $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-parallel
run-parallel:
	@echo "Running RAPIDS FUB-Beats tests in parallel..."
	$(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-parallel-waves
run-parallel-waves:
	@echo "Running RAPIDS FUB-Beats tests in parallel with waveforms..."
	WAVES=1 $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# Run Targets - Scheduler
# ==============================================================================

.PHONY: run-scheduler
run-scheduler:
	@echo "Running scheduler tests..."
	$(PYTEST) test_scheduler.py test_scheduler_timeout.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-scheduler-waves
run-scheduler-waves:
	@echo "Running scheduler tests with waveforms..."
	WAVES=1 $(PYTEST) test_scheduler.py test_scheduler_timeout.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

# ==============================================================================
# Run Targets - Descriptor Engine
# ==============================================================================

.PHONY: run-desc
run-desc:
	@echo "Running descriptor_engine tests..."
	$(PYTEST) test_descriptor_engine.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-desc-waves
run-desc-waves:
	@echo "Running descriptor_engine tests with waveforms..."
	WAVES=1 $(PYTEST) test_descriptor_engine.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

# ==============================================================================
# Run Targets - Beats Modules
# ==============================================================================

.PHONY: run-alloc
run-alloc:
	@echo "Running beats_alloc_ctrl tests..."
	$(PYTEST) test_beats_alloc_ctrl.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-drain
run-drain:
	@echo "Running beats_drain_ctrl tests..."
	$(PYTEST) test_beats_drain_ctrl.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-bridge
run-bridge:
	@echo "Running beats_latency_bridge tests..."
	$(PYTEST) test_beats_latency_bridge.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

# ==============================================================================
# REG_LEVEL Targets
# ==============================================================================

.PHONY: run-gate
run-gate:
	@echo "Running RAPIDS FUB-Beats tests at GATE level..."
	REG_LEVEL=GATE $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-gate-waves
run-gate-waves:
	@echo "Running RAPIDS FUB-Beats tests at GATE level with waveforms..."
	WAVES=1 REG_LEVEL=GATE $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-func
run-func:
	@echo "Running RAPIDS FUB-Beats tests at FUNC level..."
	REG_LEVEL=FUNC $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-func-waves
run-func-waves:
	@echo "Running RAPIDS FUB-Beats tests at FUNC level with waveforms..."
	WAVES=1 REG_LEVEL=FUNC $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-full
run-full:
	@echo "Running RAPIDS FUB-Beats tests at FULL level..."
	REG_LEVEL=FULL $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-full-waves
run-full-waves:
	@echo "Running RAPIDS FUB-Beats tests at FULL level with waveforms..."
	WAVES=1 REG_LEVEL=FULL $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

# ==============================================================================
# Development Targets
# ==============================================================================

.PHONY: ptw
ptw:
	@echo "Starting pytest-watch for RAPIDS FUB-Beats tests..."
	@echo "Tests will auto-rerun when files change. Press Ctrl+C to stop."
	@echo ""
	$(PTW) $(PTW_FLAGS) -- test_*.py $(PYTEST_VERBOSE)

# ==============================================================================
# Utility Targets
# ==============================================================================

.PHONY: collect
collect:
	@echo "Collecting RAPIDS FUB-Beats tests..."
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
