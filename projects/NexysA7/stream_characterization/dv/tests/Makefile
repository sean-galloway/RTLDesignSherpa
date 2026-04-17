# ==============================================================================
# Stream Characterization Harness Test Makefile
# ==============================================================================
#
# PREREQUISITES:
#   Must be run with sourced environment:
#     source $REPO_ROOT/env_python
#     cd $REPO_ROOT/projects/NexysA7/stream_characterization/dv/tests
#     make <target>
#
# Quick start:
#   make help               - Show all available targets
#   make run-all-gate       - Quick smoke tests (ping only)
#   make run-sim-suite      - Simulation DMA suite (sim_suite.csv)
#   make run-fpga-suite     - FPGA-sized DMA suite (fpga_suite.csv)
#   make clean-all          - Clean all test artifacts
#
# Test Levels (TEST_LEVEL environment variable):
#   gate = Quick smoke tests - ping only (~90s compile, ~3s sim)
#   func = Functional coverage - ping + desc + csr + apb + dma_1ch/2ch
#   full = Comprehensive - func + dma_3ch..dma_8ch
#
# CSV Suites (same descriptor builder used by FPGA host runner):
#   sim_suite.csv   - 2 desc/ch x 8 KB, 1-8 channels (fast sim)
#   fpga_suite.csv  - 1/2/4/8/16 desc/ch x 1 MB, 1-8 channels (full)
#
# NOTE: First run compiles the full STREAM + harness RTL (~90s). Subsequent
# runs with the same parameters reuse the compiled model and are much faster.
#
# ==============================================================================

SHELL := /bin/bash

ifndef REPO_ROOT
$(error REPO_ROOT is not set. Please run: source $$REPO_ROOT/env_python)
endif

# Paths
HOST_DIR = ../../host
CHAR_RUNNER = python3 $(HOST_DIR)/run_characterization.py
SIM_SUITE = $(HOST_DIR)/sim_suite.csv
FPGA_SUITE = $(HOST_DIR)/fpga_suite.csv

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
	@echo "Stream Characterization Harness Test Makefile"
	@echo "================================================================================"
	@echo ""
	@echo "COCOTB SIMULATION TESTS (pytest + Verilator):"
	@echo "  TEST LEVELS (set via TEST_LEVEL=gate|func|full):"
	@echo "    gate = Quick smoke tests - ping only (~90s compile, ~3s sim)"
	@echo "    func = Functional - ping + desc + csr + apb + dma_1ch/2ch [default]"
	@echo "    full = Comprehensive - func + dma_3ch..dma_8ch"
	@echo ""
	@echo "  RUN BY LEVEL:"
	@echo "    make run-all              Run all tests (TEST_LEVEL=$(TEST_LEVEL))"
	@echo "    make run-all-gate         GATE level (ping only)"
	@echo "    make run-all-func         FUNC level"
	@echo "    make run-all-full         FULL level (1-8 channel DMA)"
	@echo ""
	@echo "  WITH WAVES (VCD dump):"
	@echo "    make run-all-wave               Waves (TEST_LEVEL=$(TEST_LEVEL))"
	@echo "    make run-all-gate-wave          GATE + waves"
	@echo "    make run-all-func-wave          FUNC + waves"
	@echo "    make run-all-full-wave          FULL + waves"
	@echo ""
	@echo "  PARALLEL (48 workers):"
	@echo "    make run-all-parallel                 Parallel (TEST_LEVEL=$(TEST_LEVEL))"
	@echo "    make run-all-gate-parallel            GATE parallel"
	@echo "    make run-all-func-parallel            FUNC parallel"
	@echo "    make run-all-full-parallel             FULL parallel"
	@echo ""
	@echo "  PARALLEL + WAVES:"
	@echo "    make run-all-parallel-wave            Parallel + waves"
	@echo "    make run-all-gate-parallel-wave       GATE parallel + waves"
	@echo "    make run-all-func-parallel-wave       FUNC parallel + waves"
	@echo "    make run-all-full-parallel-wave       FULL parallel + waves"
	@echo ""
	@echo "  (legacy aliases):"
	@echo "    make run-all-parallel           Parallel (TEST_LEVEL=$(TEST_LEVEL))"
	@echo "    make run-all-gate-parallel      GATE parallel"
	@echo "    make run-all-func-parallel      FUNC parallel"
	@echo "    make run-all-full-parallel      FULL parallel"
	@echo ""
	@echo "  INDIVIDUAL:"
	@echo "    make run-stream-char      Run stream_char harness tests only"
	@echo ""
	@echo "CSV-DRIVEN SUITE RUNS (same descriptors as FPGA host runner):"
	@echo "  make run-sim-suite          sim_suite.csv   (2desc x 8KB, 1-8ch)"
	@echo "  make run-fpga-suite         fpga_suite.csv  (1-16desc x 1MB, 1-8ch)"
	@echo "  make run-csv CSV=<file>     Run from any CSV file"
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
	@echo ""
	@echo "Available CSV suites:"
	@ls -1 $(HOST_DIR)/*_suite.csv 2>/dev/null | sed 's/^/  /' || echo "  (none found)"
	@echo "================================================================================"

# ==============================================================================
# CocoTB Simulation Tests (pytest)
# ==============================================================================

.PHONY: run-all
run-all:
	@echo "================================================================================"
	@echo "Running Stream Char Tests (TEST_LEVEL=$(TEST_LEVEL))"
	@echo "================================================================================"
	TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-parallel
run-all-parallel:
	@echo "================================================================================"
	@echo "Running Stream Char Tests (Parallel, TEST_LEVEL=$(TEST_LEVEL))"
	@echo "================================================================================"
	TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_*.py

.PHONY: run-all-gate
run-all-gate:
	@echo "================================================================================"
	@echo "Running Stream Char Tests - GATE level (quick smoke test)"
	@echo "================================================================================"
	TEST_LEVEL=gate $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-func
run-all-func:
	@echo "================================================================================"
	@echo "Running Stream Char Tests - FUNC level (functional coverage)"
	@echo "================================================================================"
	TEST_LEVEL=func $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-full
run-all-full:
	@echo "================================================================================"
	@echo "Running Stream Char Tests - FULL level (comprehensive validation)"
	@echo "================================================================================"
	TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-gate-parallel
run-all-gate-parallel:
	TEST_LEVEL=gate $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_*.py

.PHONY: run-all-func-parallel
run-all-func-parallel:
	TEST_LEVEL=func $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_*.py

.PHONY: run-all-full-parallel
run-all-full-parallel:
	TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_*.py

# ==============================================================================
# Wave-Enabled Targets (WAVES=1 enables VCD dump)
# ==============================================================================

.PHONY: run-all-wave
run-all-wave:
	@echo "================================================================================"
	@echo "Running Stream Char Tests + Waves (TEST_LEVEL=$(TEST_LEVEL))"
	@echo "================================================================================"
	WAVES=1 TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-gate-wave
run-all-gate-wave:
	@echo "================================================================================"
	@echo "Running Stream Char Tests - GATE + Waves"
	@echo "================================================================================"
	WAVES=1 TEST_LEVEL=gate $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-func-wave
run-all-func-wave:
	@echo "================================================================================"
	@echo "Running Stream Char Tests - FUNC + Waves"
	@echo "================================================================================"
	WAVES=1 TEST_LEVEL=func $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-full-wave
run-all-full-wave:
	@echo "================================================================================"
	@echo "Running Stream Char Tests - FULL + Waves"
	@echo "================================================================================"
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

.PHONY: run-stream-char
run-stream-char:
	@echo "Running stream_char harness tests..."
	TEST_LEVEL=$(TEST_LEVEL) $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_stream_char.py

# ==============================================================================
# CSV-Driven Suite Runs
#
# These use the same descriptor builder and CSV format as the FPGA host
# runner, so the simulation exercises the exact same descriptor layouts
# and test sequences that will run on real hardware.
# ==============================================================================

.PHONY: run-sim-suite
run-sim-suite:
	@echo "================================================================================"
	@echo "Running Simulation Suite (sim_suite.csv)"
	@echo "================================================================================"
	@echo "This runs the same DMA test flow as FPGA hardware, but with"
	@echo "simulation-sized transfers (2 desc/ch x 8 KB = 16 KB/ch)."
	@echo ""
	TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
		-k "dma_" test_stream_char.py

.PHONY: run-fpga-suite
run-fpga-suite:
	@echo "================================================================================"
	@echo "Running FPGA Suite in Simulation (fpga_suite.csv configs at sim size)"
	@echo "================================================================================"
	@echo "NOTE: This runs all 1-8 channel DMA tests. Transfer sizes are"
	@echo "determined by DMA_XFER_BYTES env var (default 8KB for sim speed)."
	@echo ""
	TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
		-k "dma_" test_stream_char.py

.PHONY: run-csv
run-csv:
	@if [ -z "$(CSV)" ]; then echo "Usage: make run-csv CSV=path/to/file.csv"; exit 1; fi
	@echo "================================================================================"
	@echo "Running CSV Suite: $(CSV)"
	@echo "================================================================================"
	$(CHAR_RUNNER) --csv $(CSV) --dry-run
	@echo ""
	@echo "NOTE: To run on actual FPGA hardware, use:"
	@echo "  cd ../../host && python3 run_characterization.py --csv $(CSV)"

# ==============================================================================
# Collection Targets (verify tests without running)
# ==============================================================================

.PHONY: collect-all
collect-all:
	@echo "Collecting all stream char tests (verifying imports)..."
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
