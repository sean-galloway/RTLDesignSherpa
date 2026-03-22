# ==============================================================================
# Timing Characterization Top-Level Tests Makefile
# ==============================================================================
#
# Local test runner for char_top integration tests
#
# Usage:
#   cd $REPO_ROOT/projects/components/timing_characterization/dv/tests/top
#   make <target>
#
# Quick start:
#   make help           - Show available targets
#   make run            - Run all top-level tests
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

# Default target
.DEFAULT_GOAL := help

# ==============================================================================
# Help Target
# ==============================================================================

.PHONY: help
help:
	@echo "================================================================================"
	@echo "Timing Characterization Top-Level Tests Makefile"
	@echo "================================================================================"
	@echo ""
	@echo "RUN TARGETS (ALL CONFIGS):"
	@echo "  make run                  Run all char_top config tests"
	@echo "  make run-waves            Run all char_top tests with waveforms"
	@echo "  make run-parallel         Run all char_top tests in parallel (48 workers)"
	@echo "  make run-parallel-waves   Run all char_top tests parallel with waveforms"
	@echo ""
	@echo "INDIVIDUAL CONFIG TARGETS:"
	@echo "  make run-all-enabled             Run with all features enabled"
	@echo "  make run-trees-only              Run with trees only (nand+xor+mux)"
	@echo "  make run-datapath-only           Run with datapath only (carry+mult)"
	@echo "  make run-counters-clk            Run with counters+clock divider"
	@echo "  make run-nand-only               Run with NAND tree only"
	@echo "  make run-queue-only              Run with queue depth only"
	@echo ""
	@echo "TEST TYPE TARGETS:"
	@echo "  make run-integration             Run integration tests (toggle check)"
	@echo "  make run-integration-parallel    Run integration tests in parallel"
	@echo "  make run-lfsr                    Run LFSR seed determinism test"
	@echo ""
	@echo "UTILITY TARGETS:"
	@echo "  make collect              Collect (don't run) tests"
	@echo "  make clean                Clean local artifacts"
	@echo "  make clean-all            Clean all test artifacts"
	@echo "  make clean-logs           Clean stale log files only"
	@echo ""
	@echo "================================================================================"

# ==============================================================================
# Run Targets - All Tests
# ==============================================================================

.PHONY: run run-waves run-parallel run-parallel-waves
run:
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

run-waves:
	WAVES=1 $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

run-parallel:
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

run-parallel-waves:
	WAVES=1 $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# Individual Config Targets
# ==============================================================================

.PHONY: run-all-enabled run-trees-only run-datapath-only run-counters-clk \
        run-nand-only run-queue-only

run-all-enabled:
	$(PYTEST) test_char_top.py -k "all_enabled and not lfsr" $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

run-trees-only:
	$(PYTEST) test_char_top.py -k "trees_only" $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

run-datapath-only:
	$(PYTEST) test_char_top.py -k "datapath_only" $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

run-counters-clk:
	$(PYTEST) test_char_top.py -k "counters_clk" $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

run-nand-only:
	$(PYTEST) test_char_top.py -k "nand_only" $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

run-queue-only:
	$(PYTEST) test_char_top.py -k "queue_only" $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

# ==============================================================================
# Test Type Targets
# ==============================================================================

.PHONY: run-integration run-integration-parallel run-lfsr

run-integration:
	$(PYTEST) test_char_top.py::test_char_top $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

run-integration-parallel:
	$(PYTEST) test_char_top.py::test_char_top $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

run-lfsr:
	$(PYTEST) test_char_top.py::test_char_top_lfsr_seed $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

# ==============================================================================
# Standardized Aggregation Targets (used by bin/aggregate_test_results.py)
# ==============================================================================

.PHONY: run-all-gate-parallel run-all-gate-parallel-waves \
        run-all-func-parallel run-all-func-parallel-waves \
        run-all-full-parallel run-all-full-parallel-waves \
        run-all-gate run-all-gate-waves \
        run-all-func run-all-func-waves \
        run-all-full run-all-full-waves \
        run-all-gate-serial run-all-func-serial run-all-full-serial

run-all-gate-parallel: run-parallel
run-all-gate-parallel-waves: run-parallel-waves
run-all-func-parallel: run-parallel
run-all-func-parallel-waves: run-parallel-waves
run-all-full-parallel: run-parallel
run-all-full-parallel-waves: run-parallel-waves
run-all-gate: run
run-all-gate-waves: run-waves
run-all-func: run
run-all-func-waves: run-waves
run-all-full: run
run-all-full-waves: run-waves
run-all-gate-serial: run
run-all-func-serial: run
run-all-full-serial: run

# ==============================================================================
# Utility Targets
# ==============================================================================

.PHONY: collect clean clean-all clean-logs

collect:
	$(PYTEST) --collect-only $(PYTEST_VERBOSE)

clean:
	rm -rf local_sim_build/
	rm -rf logs/
	rm -rf __pycache__/
	rm -rf .pytest_cache/

clean-all: clean
	find . -name "*.vcd" -delete
	find . -name "*.fst" -delete
	find . -name "results_*.xml" -delete

clean-logs:
	rm -rf logs/
