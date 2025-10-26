# ==============================================================================
# COMMON Subsystem Test Makefile
# ==============================================================================
#
# PREREQUISITES:
#   Must be run with sourced environment:
#     source $REPO_ROOT/env_python  # Sets $REPO_ROOT and activates venv
#     cd $REPO_ROOT/val/common
#     make <target>
#
# Quick start:
#   make help           - Show all available targets
#   make run-all        - Run all COMMON tests
#   make run-counters   - Run all counter tests
#   make run-arbiters   - Run all arbiter tests
#   make clean-all      - Clean all test artifacts
#
# Advanced:
#   make run-all-parallel   - Run all tests in parallel (4 workers)
#   make collect-all        - Collect (don't run) all tests
#   make status             - Show test status and coverage
#
# ==============================================================================

# Force bash shell (required for source command)
SHELL := /bin/bash

# Repository root comes from environment (set by env_python)
# No path calculation needed - works from any project location!

# Pytest options
PYTEST = python3 -m pytest
PYTEST_VERBOSE = -v
PYTEST_QUIET = -q
PYTEST_XDIST = -n 48  # parallel workers (48 with unique test names)
PYTEST_TBSTYLE = --tb=short

# Default target - show help
.DEFAULT_GOAL := help

# Check if REPO_ROOT is set (only for non-help targets)
# This allows 'make help' to work without sourcing env_python
define check_repo_root
	@if [ -z "$(REPO_ROOT)" ]; then \
		echo "ERROR: REPO_ROOT is not set."; \
		echo "Please run: source \$$REPO_ROOT/env_python"; \
		exit 1; \
	fi
endef

# ==============================================================================
# Help Target
# ==============================================================================

.PHONY: help
help:
	@echo "================================================================================"
	@echo "COMMON Test Makefile - Available Targets"
	@echo "================================================================================"
	@echo ""
	@echo "RUN TARGETS (by Category):"
	@echo "  make run-counters              Run all counter tests"
	@echo "  make run-counters-parallel     Run all counter tests (parallel)"
	@echo "  make run-arbiters              Run all arbiter tests"
	@echo "  make run-arbiters-parallel     Run all arbiter tests (parallel)"
	@echo "  make run-fifos                 Run all FIFO tests"
	@echo "  make run-fifos-parallel        Run all FIFO tests (parallel)"
	@echo "  make run-math                  Run all math tests"
	@echo "  make run-math-parallel         Run all math tests (parallel)"
	@echo "  make run-dataint               Run data integrity tests (ECC, CRC, parity)"
	@echo "  make run-dataint-parallel      Run data integrity tests (parallel)"
	@echo "  make run-shifters              Run all shifter tests"
	@echo "  make run-shifters-parallel     Run all shifter tests (parallel)"
	@echo "  make run-clocks                Run clock utility tests"
	@echo "  make run-clocks-parallel       Run clock utility tests (parallel)"
	@echo "  make run-encoders              Run encoder/decoder tests"
	@echo "  make run-encoders-parallel     Run encoder/decoder tests (parallel)"
	@echo "  make run-all                   Run all COMMON tests"
	@echo "  make run-all-parallel          Run all tests in parallel"
	@echo ""
	@echo "REG_LEVEL TARGETS (configurable test depth):"
	@echo "  GATE = Quick smoke tests (~5 min), FUNC = Default (~30 min), FULL = Comprehensive (~hours)"
	@echo ""
	@echo "  ALL Tests:"
	@echo "    make run-all-{gate|func|full}[-parallel]"
	@echo "  Counters:"
	@echo "    make run-counters-{gate|func|full}[-parallel]"
	@echo "  Arbiters:"
	@echo "    make run-arbiters-{gate|func|full}[-parallel]"
	@echo "  Clocks:"
	@echo "    make run-clocks-{gate|func|full}[-parallel]"
	@echo "  Data Integrity:"
	@echo "    make run-dataint-{gate|func|full}[-parallel]"
	@echo "  FIFOs:"
	@echo "    make run-fifos-{gate|func|full}[-parallel]"
	@echo "  Shifters:"
	@echo "    make run-shifters-{gate|func|full}[-parallel]"
	@echo "  Math:"
	@echo "    make run-math-{gate|func|full}[-parallel]"
	@echo "  Encoders/Converters:"
	@echo "    make run-encoders-{gate|func|full}[-parallel]"
	@echo "  Miscellaneous:"
	@echo "    make run-misc-{gate|func|full}[-parallel]"
	@echo ""
	@echo "COLLECTION TARGETS (verify tests, don't run):"
	@echo "  make collect-all          Collect all tests"
	@echo ""
	@echo "CLEAN TARGETS:"
	@echo "  make clean-all            Remove all test artifacts"
	@echo "  make clean-logs           Remove all log files"
	@echo "  make clean-pycache        Remove Python cache files"
	@echo "  make clean-build          Remove simulation build directories"
	@echo "  make clean-vcd            Remove VCD waveform files"
	@echo ""
	@echo "UTILITY TARGETS:"
	@echo "  make list-all             List all test modules"
	@echo "  make status               Show test status and coverage"
	@echo ""
	@echo "================================================================================"
	@echo "Prerequisites: source $(REPO_ROOT)/env_python"
	@echo "Current REPO_ROOT: $(REPO_ROOT)"
	@echo "================================================================================"

# ==============================================================================
# Run Targets - By Category
# ==============================================================================

.PHONY: run-counters
run-counters:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running COMMON Counter Tests (default FUNC level)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_counter*.py

.PHONY: run-arbiters
run-arbiters:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running COMMON Arbiter Tests"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_arbiter*.py

.PHONY: run-fifos
run-fifos:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running COMMON FIFO Tests"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_fifo*.py

.PHONY: run-math
run-math:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running COMMON Math Tests"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_math*.py

.PHONY: run-math-gate
run-math-gate:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Math Tests - GATE level (~18 tests, ~5 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_math*.py

.PHONY: run-math-func
run-math-func:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Math Tests - FUNC level (~36 tests, ~15 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_math*.py

.PHONY: run-math-full
run-math-full:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Math Tests - FULL level (~54 tests, ~40 min)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_math*.py

# ------------------------------------------------------------------------------
# Encoder/Converter Tests - REG_LEVEL Targets
# ------------------------------------------------------------------------------

.PHONY: run-encoders-gate
run-encoders-gate:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Encoder/Converter Tests - GATE level (~8 tests, ~2 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_encoder*.py test_decoder*.py test_*2*.py

.PHONY: run-encoders-func
run-encoders-func:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Encoder/Converter Tests - FUNC level (~16 tests, ~5 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_encoder*.py test_decoder*.py test_*2*.py

.PHONY: run-encoders-full
run-encoders-full:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Encoder/Converter Tests - FULL level (~32 tests, ~15 min)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_encoder*.py test_decoder*.py test_*2*.py

# ------------------------------------------------------------------------------
# Miscellaneous Tests - REG_LEVEL Targets
# ------------------------------------------------------------------------------

.PHONY: run-misc-gate
run-misc-gate:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Miscellaneous Tests - GATE level (~12 tests, ~3 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_cam*.py test_debounce*.py test_glitch*.py test_pwm*.py test_reset_sync*.py test_sort*.py test_*leading*.py test_find*.py test_reverse*.py test_hex*.py test_count_leading*.py

.PHONY: run-misc-func
run-misc-func:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Miscellaneous Tests - FUNC level (~24 tests, ~8 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_cam*.py test_debounce*.py test_glitch*.py test_pwm*.py test_reset_sync*.py test_sort*.py test_*leading*.py test_find*.py test_reverse*.py test_hex*.py test_count_leading*.py

.PHONY: run-misc-full
run-misc-full:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Miscellaneous Tests - FULL level (~48 tests, ~25 min)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_cam*.py test_debounce*.py test_glitch*.py test_pwm*.py test_reset_sync*.py test_sort*.py test_*leading*.py test_find*.py test_reverse*.py test_hex*.py test_count_leading*.py

.PHONY: run-dataint
run-dataint:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running COMMON Data Integrity Tests"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_dataint*.py

.PHONY: run-shifters
run-shifters:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running COMMON Shifter Tests"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_shifter*.py

.PHONY: run-clocks
run-clocks:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running COMMON Clock Tests"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_clock*.py

.PHONY: run-encoders
run-encoders:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running COMMON Encoder/Decoder Tests"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_encoder*.py test_decoder*.py test_*2*.py

# ==============================================================================
# Parallel Run Targets - By Category
# ==============================================================================

.PHONY: run-counters-parallel
run-counters-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running COMMON Counter Tests (Parallel, default FUNC level)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_counter*.py

# ==============================================================================
# REG_LEVEL Control for Counter Tests
# ==============================================================================
# All 8 counter tests support GATE|FUNC|FULL levels:
#   test_counter_bin.py, test_counter_bingray.py, test_counter_bin_load.py,
#   test_counter_freq_invariant.py, test_counter_johnson.py,
#   test_counter_load_clear.py, test_counter_ring.py, test_counter.py
#
# GATE: ~8 tests total (~5 min) - Quick smoke tests
# FUNC: ~31 tests total (~30 min) - Functional coverage - DEFAULT
# FULL: ~83 tests total (~4 hr) - Comprehensive validation

.PHONY: run-counters-gate
run-counters-gate:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Counter Tests - GATE level (~8 tests, ~5 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_counter*.py

.PHONY: run-counters-func
run-counters-func:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Counter Tests - FUNC level (~31 tests, ~30 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_counter*.py

.PHONY: run-counters-full
run-counters-full:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Counter Tests - FULL level (~83 tests, ~4 hr)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_counter*.py

# Parallel versions of REG_LEVEL targets

.PHONY: run-counters-gate-parallel
run-counters-gate-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Counter Tests - GATE level PARALLEL (~8 tests, ~2 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_counter*.py

.PHONY: run-counters-func-parallel
run-counters-func-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Counter Tests - FUNC level PARALLEL (~31 tests, ~10 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_counter*.py

.PHONY: run-counters-full-parallel
run-counters-full-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Counter Tests - FULL level PARALLEL (~83 tests, ~1 hr)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_counter*.py

# ==============================================================================
# ARBITER TESTS - REG_LEVEL Support
# ==============================================================================

.PHONY: run-arbiters-gate
run-arbiters-gate:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Arbiter Tests - GATE level (~4 tests, ~5 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_arbiter*.py

.PHONY: run-arbiters-func
run-arbiters-func:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Arbiter Tests - FUNC level (~8 tests, ~15 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_arbiter*.py

.PHONY: run-arbiters-full
run-arbiters-full:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Arbiter Tests - FULL level (~16 tests, ~45 min)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_arbiter*.py

.PHONY: run-arbiters-gate-parallel
run-arbiters-gate-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Arbiter Tests - GATE level PARALLEL (~4 tests, ~2 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_arbiter*.py

.PHONY: run-arbiters-func-parallel
run-arbiters-func-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Arbiter Tests - FUNC level PARALLEL (~8 tests, ~5 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_arbiter*.py

.PHONY: run-arbiters-full-parallel
run-arbiters-full-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Arbiter Tests - FULL level PARALLEL (~16 tests, ~15 min)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_arbiter*.py

# ==============================================================================
# CLOCK TESTS - REG_LEVEL Support
# ==============================================================================

.PHONY: run-clocks-gate
run-clocks-gate:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Clock Tests - GATE level (~3 tests, ~3 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_clock*.py

.PHONY: run-clocks-func
run-clocks-func:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Clock Tests - FUNC level (~5 tests, ~5 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_clock*.py

.PHONY: run-clocks-full
run-clocks-full:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Clock Tests - FULL level (~13 tests, ~15 min)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_clock*.py

.PHONY: run-clocks-gate-parallel
run-clocks-gate-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Clock Tests - GATE level PARALLEL (~3 tests, ~1 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_clock*.py

.PHONY: run-clocks-func-parallel
run-clocks-func-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Clock Tests - FUNC level PARALLEL (~12 tests, ~3 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_clock*.py

.PHONY: run-clocks-full-parallel
run-clocks-full-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Clock Tests - FULL level PARALLEL (~50 tests, ~10 min)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_clock*.py

# ==============================================================================
# DATA INTEGRITY TESTS - REG_LEVEL Support
# ==============================================================================

.PHONY: run-dataint-gate
run-dataint-gate:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Data Integrity Tests - GATE level (~10 tests, ~5 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_dataint*.py

.PHONY: run-dataint-func
run-dataint-func:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Data Integrity Tests - FUNC level (~30 tests, ~20 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_dataint*.py

.PHONY: run-dataint-full
run-dataint-full:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Data Integrity Tests - FULL level (~60 tests, ~1 hr)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_dataint*.py

.PHONY: run-dataint-gate-parallel
run-dataint-gate-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Data Integrity Tests - GATE level PARALLEL (~10 tests, ~2 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_dataint*.py

.PHONY: run-dataint-func-parallel
run-dataint-func-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Data Integrity Tests - FUNC level PARALLEL (~30 tests, ~7 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_dataint*.py

.PHONY: run-dataint-full-parallel
run-dataint-full-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Data Integrity Tests - FULL level PARALLEL (~60 tests, ~20 min)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_dataint*.py

# ==============================================================================
# FIFO TESTS - REG_LEVEL Support
# ==============================================================================

.PHONY: run-fifos-gate
run-fifos-gate:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running FIFO Tests - GATE level (~6 tests, ~5 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_fifo_buffer*.py

.PHONY: run-fifos-func
run-fifos-func:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running FIFO Tests - FUNC level (~24 tests, ~20 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_fifo_buffer*.py

.PHONY: run-fifos-full
run-fifos-full:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running FIFO Tests - FULL level (~112 tests, ~2 hr)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_fifo_buffer*.py

.PHONY: run-fifos-gate-parallel
run-fifos-gate-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running FIFO Tests - GATE level PARALLEL (~6 tests, ~2 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_fifo_buffer*.py

.PHONY: run-fifos-func-parallel
run-fifos-func-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running FIFO Tests - FUNC level PARALLEL (~24 tests, ~7 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_fifo_buffer*.py

.PHONY: run-fifos-full-parallel
run-fifos-full-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running FIFO Tests - FULL level PARALLEL (~112 tests, ~40 min)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_fifo_buffer*.py

# ==============================================================================
# SHIFTER TESTS - REG_LEVEL Support
# ==============================================================================

.PHONY: run-shifters-gate
run-shifters-gate:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Shifter Tests - GATE level (~8 tests, ~5 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_shifter*.py

.PHONY: run-shifters-func
run-shifters-func:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Shifter Tests - FUNC level (~24 tests, ~20 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_shifter*.py

.PHONY: run-shifters-full
run-shifters-full:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Shifter Tests - FULL level (~47 tests, ~1 hr)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_shifter*.py

.PHONY: run-shifters-gate-parallel
run-shifters-gate-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Shifter Tests - GATE level PARALLEL (~8 tests, ~2 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_shifter*.py

.PHONY: run-shifters-func-parallel
run-shifters-func-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Shifter Tests - FUNC level PARALLEL (~24 tests, ~7 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_shifter*.py

.PHONY: run-shifters-full-parallel
run-shifters-full-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Shifter Tests - FULL level PARALLEL (~47 tests, ~20 min)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_shifter*.py

# ------------------------------------------------------------------------------
# Math Tests - REG_LEVEL Targets (Parallel)
# ------------------------------------------------------------------------------

.PHONY: run-math-gate-parallel
run-math-gate-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Math Tests - GATE level PARALLEL (~18 tests, ~2 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_math*.py

.PHONY: run-math-func-parallel
run-math-func-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Math Tests - FUNC level PARALLEL (~36 tests, ~5 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_math*.py

.PHONY: run-math-full-parallel
run-math-full-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Math Tests - FULL level PARALLEL (~54 tests, ~15 min)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_math*.py

# ------------------------------------------------------------------------------
# Encoder/Converter Tests - REG_LEVEL Parallel Targets
# ------------------------------------------------------------------------------

.PHONY: run-encoders-gate-parallel
run-encoders-gate-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Encoder/Converter Tests - GATE level PARALLEL (~8 tests, ~1 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_encoder*.py test_decoder*.py test_*2*.py

.PHONY: run-encoders-func-parallel
run-encoders-func-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Encoder/Converter Tests - FUNC level PARALLEL (~16 tests, ~2 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_encoder*.py test_decoder*.py test_*2*.py

.PHONY: run-encoders-full-parallel
run-encoders-full-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Encoder/Converter Tests - FULL level PARALLEL (~32 tests, ~5 min)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_encoder*.py test_decoder*.py test_*2*.py

# ------------------------------------------------------------------------------
# Miscellaneous Tests - REG_LEVEL Parallel Targets
# ------------------------------------------------------------------------------

.PHONY: run-misc-gate-parallel
run-misc-gate-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Miscellaneous Tests - GATE level PARALLEL (~12 tests, ~1 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_cam*.py test_debounce*.py test_glitch*.py test_pwm*.py test_reset_sync*.py test_sort*.py test_*leading*.py test_find*.py test_reverse*.py test_hex*.py test_count_leading*.py

.PHONY: run-misc-func-parallel
run-misc-func-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Miscellaneous Tests - FUNC level PARALLEL (~24 tests, ~3 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_cam*.py test_debounce*.py test_glitch*.py test_pwm*.py test_reset_sync*.py test_sort*.py test_*leading*.py test_find*.py test_reverse*.py test_hex*.py test_count_leading*.py

.PHONY: run-misc-full-parallel
run-misc-full-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running Miscellaneous Tests - FULL level PARALLEL (~48 tests, ~8 min)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_cam*.py test_debounce*.py test_glitch*.py test_pwm*.py test_reset_sync*.py test_sort*.py test_*leading*.py test_find*.py test_reverse*.py test_hex*.py test_count_leading*.py

# ==============================================================================
# Legacy Parallel Targets (no REG_LEVEL)
# ==============================================================================

.PHONY: run-arbiters-parallel
run-arbiters-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running COMMON Arbiter Tests (Parallel)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_arbiter*.py

.PHONY: run-fifos-parallel
run-fifos-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running COMMON FIFO Tests (Parallel)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_fifo*.py

.PHONY: run-math-parallel
run-math-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running COMMON Math Tests (Parallel)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_math*.py

.PHONY: run-dataint-parallel
run-dataint-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running COMMON Data Integrity Tests (Parallel)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_dataint*.py

.PHONY: run-shifters-parallel
run-shifters-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running COMMON Shifter Tests (Parallel)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_shifter*.py

.PHONY: run-clocks-parallel
run-clocks-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running COMMON Clock Tests (Parallel)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_clock*.py

.PHONY: run-encoders-parallel
run-encoders-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running COMMON Encoder/Decoder Tests (Parallel)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_encoder*.py test_decoder*.py test_*2*.py

# ==============================================================================
# Run All Targets
# ==============================================================================

.PHONY: run-all
run-all:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running ALL COMMON Tests"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-parallel
run-all-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running ALL COMMON Tests (Parallel - 4 workers)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_*.py

# REG_LEVEL Variants - Run all tests with specific regression levels
.PHONY: run-all-gate
run-all-gate:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running ALL COMMON Tests - GATE level (minimal params, ~5-10 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-func
run-all-func:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running ALL COMMON Tests - FUNC level (default params, ~30-60 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-full
run-all-full:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running ALL COMMON Tests - FULL level (comprehensive, ~2-4 hours)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-gate-parallel
run-all-gate-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running ALL COMMON Tests - GATE level PARALLEL (~2-3 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_*.py

.PHONY: run-all-func-parallel
run-all-func-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running ALL COMMON Tests - FUNC level PARALLEL (~10-20 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_*.py

.PHONY: run-all-full-parallel
run-all-full-parallel:
	$(check_repo_root)
	@echo "================================================================================"
	@echo "Running ALL COMMON Tests - FULL level PARALLEL (~30-60 min)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_*.py

# ==============================================================================
# Collection Targets (verify tests without running)
# ==============================================================================

.PHONY: collect-all
collect-all:
	$(check_repo_root)
	@echo "Collecting ALL COMMON tests..."
	$(PYTEST) --collect-only test_*.py

# ==============================================================================
# Clean Targets
# ==============================================================================

.PHONY: clean-logs
clean-logs:
	@echo "Cleaning all log files..."
	rm -rf logs/
	find . -type f -name "*.log" -delete
	@echo "✓ Log files cleaned"

.PHONY: clean-pycache
clean-pycache:
	@echo "Cleaning Python cache files..."
	find . -type d -name "__pycache__" -exec rm -rf {} + 2>/dev/null || true
	find . -type f -name "*.pyc" -delete
	@echo "✓ Python cache cleaned"

.PHONY: clean-build
clean-build:
	@echo "Cleaning simulation build directories..."
	rm -rf local_sim_build/
	rm -rf sim_build/
	find . -type d -name "local_sim_build" -exec rm -rf {} + 2>/dev/null || true
	find . -type d -name "sim_build" -exec rm -rf {} + 2>/dev/null || true
	@echo "✓ Build directories cleaned"

.PHONY: clean-vcd
clean-vcd:
	@echo "Cleaning VCD waveform files..."
	find . -type f -name "*.vcd" -delete
	find . -type f -name "*.fst" -delete
	@echo "✓ Waveform files cleaned"

.PHONY: clean-all
clean-all: clean-logs clean-pycache clean-build clean-vcd
	@echo "================================================================================"
	@echo "✓ All COMMON test artifacts cleaned"
	@echo "================================================================================"

# ==============================================================================
# Utility Targets
# ==============================================================================

.PHONY: list-all
list-all:
	@echo "All COMMON Test Modules:"
	@ls test_*.py 2>/dev/null | sort

.PHONY: status
status:
	@echo "================================================================================"
	@echo "COMMON Test Status"
	@echo "================================================================================"
	@echo "Test directories:"
	@echo "  Val/COMMON:  $(REPO_ROOT)/val/common/"
	@echo ""
	@echo "Test modules found:"
	@echo -n "  Counters:    "
	@ls test_counter*.py 2>/dev/null | wc -l
	@echo -n "  Arbiters:    "
	@ls test_arbiter*.py 2>/dev/null | wc -l
	@echo -n "  FIFOs:       "
	@ls test_fifo*.py 2>/dev/null | wc -l
	@echo -n "  Math:        "
	@ls test_math*.py 2>/dev/null | wc -l
	@echo -n "  Data Integ:  "
	@ls test_dataint*.py 2>/dev/null | wc -l
	@echo -n "  Shifters:    "
	@ls test_shifter*.py 2>/dev/null | wc -l
	@echo -n "  Total:       "
	@ls test_*.py 2>/dev/null | wc -l
	@echo ""
	@echo "Build artifacts:"
	@echo -n "  local_sim_build dirs: "
	@find . -type d -name "local_sim_build" 2>/dev/null | wc -l
	@echo -n "  Log files:            "
	@find . -type f -name "*.log" 2>/dev/null | wc -l
	@echo -n "  VCD files:            "
	@find . -type f -name "*.vcd" 2>/dev/null | wc -l
	@echo ""
	@echo "Python environment:"
	@echo "  REPO_ROOT: $(REPO_ROOT)"
	@echo "  Virtual env: $(REPO_ROOT)/env_python"
	@echo "================================================================================"

# ==============================================================================
# Combined Targets (clean + run)
# ==============================================================================

.PHONY: fresh-all
fresh-all: clean-all run-all
	@echo "✓ Fresh all tests run complete"

# ==============================================================================
# Quick Aliases
# ==============================================================================

.PHONY: counters
counters: run-counters

.PHONY: counters-parallel
counters-parallel: run-counters-parallel

.PHONY: arbiters
arbiters: run-arbiters

.PHONY: arbiters-parallel
arbiters-parallel: run-arbiters-parallel

.PHONY: fifos
fifos: run-fifos

.PHONY: fifos-parallel
fifos-parallel: run-fifos-parallel

.PHONY: all
all: run-all

.PHONY: all-parallel
all-parallel: run-all-parallel

.PHONY: clean
clean: clean-all

.PHONY: collect
collect: collect-all

.PHONY: list
list: list-all

# ==============================================================================
# End of Makefile
# ==============================================================================
