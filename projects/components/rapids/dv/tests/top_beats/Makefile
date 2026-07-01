# ==============================================================================
# RAPIDS Top-Beats Tests Makefile
# ==============================================================================
#
# Local test runner for the RAPIDS Core (beats) top-level integration test
# (rapids_core_beats: scheduler_group_array + sink/source data paths).
#
# Usage:
#   cd $REPO_ROOT/projects/components/rapids/dv/tests/top_beats
#   make <target>
#
# Quick start:
#   make help           - Show available targets
#   make run-parallel   - Run all top_beats tests in parallel (gate level)
#   make clean          - Clean local artifacts
#
# ==============================================================================

SHELL := /bin/bash

ifndef REPO_ROOT
$(error REPO_ROOT is not set. Please run: source $$REPO_ROOT/env_python)
endif

PYTEST = python3 -m pytest
PYTEST_VERBOSE = -v
PYTEST_QUIET = -q
PYTEST_XDIST = -n 48
PYTEST_TBSTYLE = --tb=short
PYTEST_RERUNS = --reruns 3 --reruns-delay 1

.DEFAULT_GOAL := help

# ==============================================================================
# Help
# ==============================================================================
.PHONY: help
help:
	@echo "================================================================================"
	@echo "RAPIDS Top-Beats Tests Makefile (rapids_core_beats)"
	@echo "================================================================================"
	@echo ""
	@echo "QUICK RUN TARGETS:"
	@echo "  make run-all                       Run all tests (FUNC level)"
	@echo "  make run-smoke                     Run the bring-up smoke test only"
	@echo ""
	@echo "PARALLEL 'RUN EVERYTHING' TARGETS (cover ALL test_*.py):"
	@echo "  make run-parallel                  (= run-gate-parallel)"
	@echo "  make run-parallel-waves            (= run-gate-parallel-waves)"
	@echo "  make run-gate-parallel   / -waves  GATE level in parallel [+ waveforms]"
	@echo "  make run-func-parallel   / -waves  FUNC level in parallel [+ waveforms]"
	@echo "  make run-full-parallel   / -waves  FULL level in parallel [+ waveforms]"
	@echo ""
	@echo "UTILITY:"
	@echo "  make clean                         Clean local artifacts"

# ==============================================================================
# Convenience run targets
# ==============================================================================
.PHONY: run-all run-smoke
run-all:
	REG_LEVEL=FUNC TEST_LEVEL=FUNC $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

run-smoke:
	REG_LEVEL=GATE TEST_LEVEL=GATE $(PYTEST) "test_rapids_core_beats.py::test_rapids_core_beats[smoke-512-default]" $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

# ==============================================================================
# Parallel run targets: run-parallel (=gate) + per-level, with/without waves.
# Each globs test_*.py so ALL tests in this env are covered.
# ==============================================================================
.PHONY: run-parallel run-parallel-waves
.PHONY: run-gate-parallel run-gate-parallel-waves run-func-parallel run-func-parallel-waves run-full-parallel run-full-parallel-waves
run-parallel: run-gate-parallel
run-parallel-waves: run-gate-parallel-waves
run-gate-parallel:
	@echo "Running RAPIDS top-beats tests at GATE level in parallel..."
	REG_LEVEL=GATE TEST_LEVEL=GATE $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)
run-gate-parallel-waves:
	@echo "Running RAPIDS top-beats tests at GATE level in parallel with waveforms..."
	WAVES=1 REG_LEVEL=GATE TEST_LEVEL=GATE $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)
run-func-parallel:
	@echo "Running RAPIDS top-beats tests at FUNC level in parallel..."
	REG_LEVEL=FUNC TEST_LEVEL=FUNC $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)
run-func-parallel-waves:
	@echo "Running RAPIDS top-beats tests at FUNC level in parallel with waveforms..."
	WAVES=1 REG_LEVEL=FUNC TEST_LEVEL=FUNC $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)
run-full-parallel:
	@echo "Running RAPIDS top-beats tests at FULL level in parallel..."
	REG_LEVEL=FULL TEST_LEVEL=FULL $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)
run-full-parallel-waves:
	@echo "Running RAPIDS top-beats tests at FULL level in parallel with waveforms..."
	WAVES=1 REG_LEVEL=FULL TEST_LEVEL=FULL $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# Clean
# ==============================================================================
.PHONY: clean clean-all
clean:
	rm -rf __pycache__ .pytest_cache *.pyc

clean-all: clean
	@echo "Cleaning all test artifacts..."
	rm -rf local_sim_build logs
	find . -name "*.vcd" -delete
	find . -name "*.log" -delete
