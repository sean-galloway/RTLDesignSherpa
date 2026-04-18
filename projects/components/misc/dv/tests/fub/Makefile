# ==============================================================================
# Misc Components FUB Test Makefile
# ==============================================================================
#
# PREREQUISITES:
#   Must be run with sourced environment:
#     source $REPO_ROOT/env_python
#     cd $REPO_ROOT/projects/components/misc/dv/tests/fub
#     make <target>
#
# Quick start:
#   make help           - Show all available targets
#   make run-all        - Run all FUB tests (all modules)
#   make run-all-gate   - Run all FUB tests at GATE level (quick)
#   make clean-all      - Clean all test artifacts
#
# Test Levels (TEST_LEVEL environment variable):
#   gate = Quick smoke tests (~5 min)
#   func = Functional coverage (~30 min)
#   full = Comprehensive validation (~4 hr)
#
# All test_*.py files in this directory are automatically included.
# To add tests for a new module, create test_<module>.py and it will
# be picked up by all run/collect/coverage targets.
#
# ==============================================================================

SHELL := /bin/bash

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

# Default test level
TEST_LEVEL ?= func

.DEFAULT_GOAL := help

# ==============================================================================
# Help Target
# ==============================================================================

.PHONY: help
help:
	@echo "================================================================================"
	@echo "Misc Components FUB Test Makefile - Available Targets"
	@echo "================================================================================"
	@echo ""
	@echo "All test_*.py files in this directory are auto-discovered."
	@echo "Add a new test_<module>.py and it joins all targets automatically."
	@echo ""
	@echo "TEST LEVELS (set via TEST_LEVEL=gate|func|full):"
	@echo "  gate = Quick smoke tests (~5 min)"
	@echo "  func = Functional coverage (~30 min) [default]"
	@echo "  full = Comprehensive validation (~4 hr)"
	@echo ""
	@echo "RUN ALL MODULES:"
	@echo "  make run-all              Run all tests (TEST_LEVEL=$(TEST_LEVEL))"
	@echo "  make run-all-gate         Run all tests at GATE level"
	@echo "  make run-all-func         Run all tests at FUNC level"
	@echo "  make run-all-full         Run all tests at FULL level"
	@echo ""
	@echo "WITH WAVES (VCD dump):"
	@echo "  make run-all-wave               Waves (TEST_LEVEL=$(TEST_LEVEL))"
	@echo "  make run-all-gate-wave          GATE + waves"
	@echo "  make run-all-func-wave          FUNC + waves"
	@echo "  make run-all-full-wave          FULL + waves"
	@echo ""
	@echo "PARALLEL (48 workers, with retries):"
	@echo "  make run-all-parallel           All tests in parallel"
	@echo "  make run-all-gate-parallel      GATE level parallel"
	@echo "  make run-all-func-parallel      FUNC level parallel"
	@echo "  make run-all-full-parallel      FULL level parallel"
	@echo ""
	@echo "PARALLEL + WAVES:"
	@echo "  make run-all-parallel-wave      All parallel + waves"
	@echo "  make run-all-full-parallel-wave FULL parallel + waves"
	@echo ""
	@echo "INDIVIDUAL MODULES:"
	@echo "  make run-dma-addr-gen     Run DMA address generator tests"
	@echo "  make run-rd-pattern-gen   Run AXI4 read pattern generator tests"
	@echo "  make run-wr-crc-check     Run AXI4 write CRC check tests"
	@echo ""
	@echo "COLLECTION (verify tests, don't run):"
	@echo "  make collect-all          Collect all tests (verify imports)"
	@echo ""
	@echo "CLEAN:"
	@echo "  make clean-all            Remove all test artifacts"
	@echo "  make clean-logs           Remove all log files"
	@echo "  make clean-build          Remove simulation build directories"
	@echo ""
	@echo "================================================================================"
	@echo "Prerequisites: source $(REPO_ROOT)/env_python"
	@echo "Current REPO_ROOT: $(REPO_ROOT)"
	@echo "Current TEST_LEVEL: $(TEST_LEVEL)"
	@echo ""
	@echo "Available test modules:"
	@ls -1 test_*.py 2>/dev/null | sed 's/^/  /' || echo "  (none found)"
	@echo "================================================================================"

# ==============================================================================
# Run All Modules
# ==============================================================================

.PHONY: run-all
run-all:
	@echo "================================================================================"
	@echo "Running ALL Misc FUB Tests (TEST_LEVEL=$(TEST_LEVEL))"
	@echo "================================================================================"
	TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-parallel
run-all-parallel:
	@echo "================================================================================"
	@echo "Running ALL Misc FUB Tests (Parallel - 48 workers, TEST_LEVEL=$(TEST_LEVEL))"
	@echo "================================================================================"
	TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_*.py

.PHONY: run-all-gate
run-all-gate:
	@echo "================================================================================"
	@echo "Running ALL Misc FUB Tests - GATE level (quick smoke test)"
	@echo "================================================================================"
	TEST_LEVEL=gate $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-func
run-all-func:
	@echo "================================================================================"
	@echo "Running ALL Misc FUB Tests - FUNC level (functional coverage)"
	@echo "================================================================================"
	TEST_LEVEL=func $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-full
run-all-full:
	@echo "================================================================================"
	@echo "Running ALL Misc FUB Tests - FULL level (comprehensive validation)"
	@echo "================================================================================"
	TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-gate-parallel
run-all-gate-parallel:
	@echo "================================================================================"
	@echo "Running ALL Misc FUB Tests - GATE level PARALLEL (48 workers)"
	@echo "================================================================================"
	TEST_LEVEL=gate $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_*.py

.PHONY: run-all-func-parallel
run-all-func-parallel:
	@echo "================================================================================"
	@echo "Running ALL Misc FUB Tests - FUNC level PARALLEL (48 workers)"
	@echo "================================================================================"
	TEST_LEVEL=func $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_*.py

.PHONY: run-all-full-parallel
run-all-full-parallel:
	@echo "================================================================================"
	@echo "Running ALL Misc FUB Tests - FULL level PARALLEL (48 workers)"
	@echo "================================================================================"
	TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_*.py

# ==============================================================================
# Individual Test Modules
# ==============================================================================
# Add a target for each module as test files are created.
# Convention: make run-<short-name>

.PHONY: run-dma-addr-gen
run-dma-addr-gen:
	@echo "Running DMA address generator tests..."
	TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_dma_address_gen.py

.PHONY: run-rd-pattern-gen
run-rd-pattern-gen:
	@echo "Running AXI4 read pattern generator tests..."
	TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_slave_rd_pattern_gen.py

.PHONY: run-wr-crc-check
run-wr-crc-check:
	@echo "Running AXI4 write CRC check tests..."
	TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_slave_wr_crc_check.py

# ==============================================================================
# Wave-Enabled Targets (WAVES=1 enables VCD dump)
# ==============================================================================

.PHONY: run-all-wave
run-all-wave:
	WAVES=1 TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-gate-wave
run-all-gate-wave:
	WAVES=1 TEST_LEVEL=gate $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-func-wave
run-all-func-wave:
	WAVES=1 TEST_LEVEL=func $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-full-wave
run-all-full-wave:
	WAVES=1 TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

# ==============================================================================
# Parallel + Wave Targets
# ==============================================================================

.PHONY: run-all-parallel-wave
run-all-parallel-wave:
	WAVES=1 TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_*.py

.PHONY: run-all-gate-parallel-wave
run-all-gate-parallel-wave:
	WAVES=1 TEST_LEVEL=gate $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_*.py

.PHONY: run-all-func-parallel-wave
run-all-func-parallel-wave:
	WAVES=1 TEST_LEVEL=func $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_*.py

.PHONY: run-all-full-parallel-wave
run-all-full-parallel-wave:
	WAVES=1 TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_*.py

# ==============================================================================
# Collection Targets (verify tests without running)
# ==============================================================================

.PHONY: collect-all
collect-all:
	@echo "Collecting ALL Misc FUB tests (verifying imports)..."
	$(PYTEST) --collect-only test_*.py

# ==============================================================================
# Clean Targets
# ==============================================================================

.PHONY: clean-build
clean-build:
	@echo "Cleaning simulation build directories..."
	rm -rf local_sim_build
	rm -rf sim_build
	@echo "Build directories cleaned"

.PHONY: clean-logs
clean-logs:
	@echo "Cleaning log files..."
	rm -rf logs
	find . -type f -name "*.log" -delete 2>/dev/null || true
	@echo "Log files cleaned"

.PHONY: clean-pycache
clean-pycache:
	@echo "Cleaning Python cache files..."
	find . -type d -name "__pycache__" -exec rm -rf {} + 2>/dev/null || true
	find . -type f -name "*.pyc" -delete 2>/dev/null || true
	@echo "Python cache cleaned"

.PHONY: clean-vcd
clean-vcd:
	@echo "Cleaning VCD trace files..."
	find . -type f -name "*.vcd" -delete 2>/dev/null || true
	find . -type f -name "*.fst" -delete 2>/dev/null || true
	@echo "Trace files cleaned"

.PHONY: clean-all
clean-all: clean-build clean-logs clean-pycache clean-vcd
	@echo "All test artifacts cleaned"
