# ==============================================================================
# STREAM Top-Level Tests Makefile
# ==============================================================================
#
# Local test runner for top-level integration tests (stream_top_ch8)
#
# Usage:
#   cd $REPO_ROOT/projects/components/stream/dv/tests/top
#   make <target>
#
# Quick start:
#   make help           - Show available targets
#   make run            - Run stream_top tests (GATE level, default)
#   make run-func       - Run stream_top tests (FUNC level)
#   make run-full       - Run stream_top tests (FULL level)
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
PYTEST_XDIST = -n 8
PYTEST_TBSTYLE = --tb=short
PYTEST_RERUNS = --reruns 0 --reruns-delay 1

# Test files
TEST_FILE = test_stream_top.py
TEST_FILE_ADVANCED = test_stream_top_advanced.py

# Default target
.DEFAULT_GOAL := help

# ==============================================================================
# Help Target
# ==============================================================================

.PHONY: help
help:
	@echo "================================================================================"
	@echo "STREAM Top-Level Tests Makefile - stream_top_ch8 Integration Tests"
	@echo "================================================================================"
	@echo ""
	@echo "QUICK RUN TARGETS:"
	@echo "  make run                        Run stream_top tests (GATE level, default)"
	@echo "  make run-func                   Run stream_top tests (FUNC level)"
	@echo "  make run-full                   Run stream_top tests (FULL level)"
	@echo "  make run-waves                  Run stream_top tests with waveforms (GATE)"
	@echo "  make run-parallel               Run stream_top tests in parallel (GATE)"
	@echo ""
	@echo "STREAM_TOP TARGETS (test_stream_top.py):"
	@echo "  make run-gate                   Run stream_top tests at GATE level"
	@echo "  make run-gate-waves             Run stream_top tests at GATE with waveforms"
	@echo "  make run-gate-parallel          Run stream_top tests at GATE in parallel"
	@echo "  make run-gate-parallel-waves    Run stream_top tests at GATE parallel + waves"
	@echo ""
	@echo "  make run-func                   Run stream_top tests at FUNC level"
	@echo "  make run-func-waves             Run stream_top tests at FUNC with waveforms"
	@echo "  make run-func-parallel          Run stream_top tests at FUNC in parallel"
	@echo "  make run-func-parallel-waves    Run stream_top tests at FUNC parallel + waves"
	@echo ""
	@echo "  make run-full                   Run stream_top tests at FULL level"
	@echo "  make run-full-waves             Run stream_top tests at FULL with waveforms"
	@echo "  make run-full-parallel          Run stream_top tests at FULL in parallel"
	@echo "  make run-full-parallel-waves    Run stream_top tests at FULL parallel + waves"
	@echo ""
	@echo "ADVANCED TESTS (test_stream_top_advanced.py):"
	@echo "  make run-advanced               Run advanced tests (basic level, no waves)"
	@echo "  make run-advanced-waves         Run advanced tests (basic level, with waves)"
	@echo "  make run-advanced-parallel      Run advanced tests (basic level, parallel)"
	@echo "  make run-advanced-parallel-waves Run advanced tests (parallel + waves)"
	@echo "  make run-advanced-medium        Run advanced tests (medium level)"
	@echo "  make run-advanced-full          Run advanced tests (full level)"
	@echo "  make run-advanced-full-waves    Run advanced tests (full level, with waves)"
	@echo ""
	@echo "UTILITY TARGETS:"
	@echo "  make clean                      Clean local artifacts (sim_build, logs, etc.)"
	@echo "  make clean-waves                Clean waveform files only"
	@echo "  make clean-all                  Clean everything including results"
	@echo ""
	@echo "ENVIRONMENT VARIABLES:"
	@echo "  TEST_LEVEL=<gate|func|full>     Set test level (default: gate)"
	@echo "  WAVES=<0|1>                     Enable/disable waveforms (default: 0)"
	@echo "  PYTEST_ARGS=<args>              Additional pytest arguments"
	@echo ""
	@echo "EXAMPLES:"
	@echo "  make run                        # Quick GATE-level smoke test"
	@echo "  make run-func-waves             # FUNC-level with waveforms"
	@echo "  make run-full-parallel          # FULL-level in parallel (faster)"
	@echo "  make PYTEST_ARGS=-k=apb_config run  # Run specific test pattern"
	@echo ""
	@echo "================================================================================"

# ==============================================================================
# Quick Targets (Default Shortcuts)
# ==============================================================================

.PHONY: run
run: run-gate

.PHONY: run-waves
run-waves: run-gate-waves

.PHONY: run-parallel
run-parallel: run-gate-parallel

# ==============================================================================
# GATE Level Targets (Quick Smoke Tests)
# ==============================================================================

.PHONY: run-gate
run-gate:
	@echo "=== Running STREAM_TOP tests at GATE level ==="
	WAVES=0 TEST_LEVEL=gate $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-gate-waves
run-gate-waves:
	@echo "=== Running STREAM_TOP tests at GATE level with waveforms ==="
	WAVES=1 TEST_LEVEL=gate $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-gate-parallel
run-gate-parallel:
	@echo "=== Running STREAM_TOP tests at GATE level in parallel ==="
	WAVES=0 TEST_LEVEL=gate $(PYTEST) $(TEST_FILE) $(PYTEST_XDIST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-gate-parallel-waves
run-gate-parallel-waves:
	@echo "=== Running STREAM_TOP tests at GATE level parallel + waveforms ==="
	WAVES=1 TEST_LEVEL=gate $(PYTEST) $(TEST_FILE) $(PYTEST_XDIST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

# ==============================================================================
# FUNC Level Targets (Functional Coverage)
# ==============================================================================

.PHONY: run-func
run-func:
	@echo "=== Running STREAM_TOP tests at FUNC level ==="
	WAVES=0 TEST_LEVEL=func $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-func-waves
run-func-waves:
	@echo "=== Running STREAM_TOP tests at FUNC level with waveforms ==="
	WAVES=1 TEST_LEVEL=func $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-func-parallel
run-func-parallel:
	@echo "=== Running STREAM_TOP tests at FUNC level in parallel ==="
	WAVES=0 TEST_LEVEL=func $(PYTEST) $(TEST_FILE) $(PYTEST_XDIST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-func-parallel-waves
run-func-parallel-waves:
	@echo "=== Running STREAM_TOP tests at FUNC level parallel + waveforms ==="
	WAVES=1 TEST_LEVEL=func $(PYTEST) $(TEST_FILE) $(PYTEST_XDIST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

# ==============================================================================
# FULL Level Targets (Comprehensive Validation)
# ==============================================================================

.PHONY: run-full
run-full:
	@echo "=== Running STREAM_TOP tests at FULL level ==="
	WAVES=0 TEST_LEVEL=full $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-full-waves
run-full-waves:
	@echo "=== Running STREAM_TOP tests at FULL level with waveforms ==="
	WAVES=1 TEST_LEVEL=full $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-full-parallel
run-full-parallel:
	@echo "=== Running STREAM_TOP tests at FULL level in parallel ==="
	WAVES=0 TEST_LEVEL=full $(PYTEST) $(TEST_FILE) $(PYTEST_XDIST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-full-parallel-waves
run-full-parallel-waves:
	@echo "=== Running STREAM_TOP tests at FULL level parallel + waveforms ==="
	WAVES=1 TEST_LEVEL=full $(PYTEST) $(TEST_FILE) $(PYTEST_XDIST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

# ==============================================================================
# Utility Targets
# ==============================================================================

.PHONY: clean
clean:
	@echo "Cleaning local artifacts..."
	rm -rf local_sim_build/
	rm -rf __pycache__/
	rm -rf .pytest_cache/
	rm -rf logs/
	rm -f *.log
	@echo "Clean complete."

.PHONY: clean-waves
clean-waves:
	@echo "Cleaning waveform files..."
	find local_sim_build/ -name "*.fst" -delete 2>/dev/null || true
	find local_sim_build/ -name "*.vcd" -delete 2>/dev/null || true
	@echo "Waveform clean complete."

.PHONY: clean-all
clean-all: clean
	@echo "Cleaning all results and artifacts..."
	rm -rf results/
	@echo "Deep clean complete."

# ==============================================================================
# Advanced Test Targets (test_stream_top_advanced.py)
# ==============================================================================

.PHONY: run-advanced
run-advanced:
	@echo "=== Running STREAM_TOP Advanced tests at BASIC level ==="
	WAVES=0 TEST_LEVEL=basic $(PYTEST) $(TEST_FILE_ADVANCED) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-advanced-waves
run-advanced-waves:
	@echo "=== Running STREAM_TOP Advanced tests at BASIC level with waveforms ==="
	WAVES=1 TEST_LEVEL=basic $(PYTEST) $(TEST_FILE_ADVANCED) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-advanced-parallel
run-advanced-parallel:
	@echo "=== Running STREAM_TOP Advanced tests at BASIC level in parallel ==="
	WAVES=0 TEST_LEVEL=basic $(PYTEST) $(TEST_FILE_ADVANCED) $(PYTEST_XDIST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-advanced-parallel-waves
run-advanced-parallel-waves:
	@echo "=== Running STREAM_TOP Advanced tests at BASIC level parallel + waveforms ==="
	WAVES=1 TEST_LEVEL=basic $(PYTEST) $(TEST_FILE_ADVANCED) $(PYTEST_XDIST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-advanced-medium
run-advanced-medium:
	@echo "=== Running STREAM_TOP Advanced tests at MEDIUM level ==="
	WAVES=0 TEST_LEVEL=medium $(PYTEST) $(TEST_FILE_ADVANCED) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-advanced-medium-waves
run-advanced-medium-waves:
	@echo "=== Running STREAM_TOP Advanced tests at MEDIUM level with waveforms ==="
	WAVES=1 TEST_LEVEL=medium $(PYTEST) $(TEST_FILE_ADVANCED) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-advanced-medium-parallel
run-advanced-medium-parallel:
	@echo "=== Running STREAM_TOP Advanced tests at MEDIUM level in parallel ==="
	WAVES=0 TEST_LEVEL=medium $(PYTEST) $(TEST_FILE_ADVANCED) $(PYTEST_XDIST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-advanced-full
run-advanced-full:
	@echo "=== Running STREAM_TOP Advanced tests at FULL level ==="
	WAVES=0 TEST_LEVEL=full $(PYTEST) $(TEST_FILE_ADVANCED) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-advanced-full-waves
run-advanced-full-waves:
	@echo "=== Running STREAM_TOP Advanced tests at FULL level with waveforms ==="
	WAVES=1 TEST_LEVEL=full $(PYTEST) $(TEST_FILE_ADVANCED) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-advanced-full-parallel
run-advanced-full-parallel:
	@echo "=== Running STREAM_TOP Advanced tests at FULL level in parallel ==="
	WAVES=0 TEST_LEVEL=full $(PYTEST) $(TEST_FILE_ADVANCED) $(PYTEST_XDIST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-advanced-full-parallel-waves
run-advanced-full-parallel-waves:
	@echo "=== Running STREAM_TOP Advanced tests at FULL level parallel + waveforms ==="
	WAVES=1 TEST_LEVEL=full $(PYTEST) $(TEST_FILE_ADVANCED) $(PYTEST_XDIST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

# ==============================================================================
# Custom Targets
# ==============================================================================

.PHONY: run-custom
run-custom:
	@echo "=== Running STREAM_TOP tests with custom args ==="
	@echo "TEST_LEVEL=$(TEST_LEVEL) WAVES=$(WAVES) PYTEST_ARGS=$(PYTEST_ARGS)"
	WAVES=$(WAVES) TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_ARGS)

.PHONY: lint
lint:
	@echo "Linting test file..."
	python3 -m pylint $(TEST_FILE) || true
	@echo "Lint complete."

.PHONY: format
format:
	@echo "Formatting test file..."
	python3 -m black $(TEST_FILE)
	@echo "Format complete."
