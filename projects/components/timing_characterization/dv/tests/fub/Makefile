# ==============================================================================
# Timing Characterization FUB Tests Makefile
# ==============================================================================
#
# Local test runner for FUB (Functional Unit Block) tests
#
# Usage:
#   cd $REPO_ROOT/projects/components/timing_characterization/dv/tests/fub
#   make <target>
#
# Quick start:
#   make help           - Show available targets
#   make run            - Run all FUB tests
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
	@echo "Timing Characterization FUB Tests Makefile"
	@echo "================================================================================"
	@echo ""
	@echo "RUN TARGETS (ALL TESTS):"
	@echo "  make run                  Run all FUB tests"
	@echo "  make run-waves            Run all FUB tests with waveforms"
	@echo "  make run-parallel         Run all FUB tests in parallel (48 workers)"
	@echo "  make run-parallel-waves   Run all FUB tests parallel with waveforms"
	@echo ""
	@echo "INDIVIDUAL FUB TARGETS:"
	@echo "  make run-nand-chain              Run nand_chain tests"
	@echo "  make run-nand-chain-parallel     Run nand_chain tests in parallel"
	@echo "  make run-inverter-chain          Run inverter_chain tests"
	@echo "  make run-inverter-chain-parallel Run inverter_chain tests in parallel"
	@echo "  make run-xor-tree               Run xor_tree tests"
	@echo "  make run-xor-tree-parallel       Run xor_tree tests in parallel"
	@echo "  make run-carry-chain             Run carry_chain tests"
	@echo "  make run-carry-chain-parallel    Run carry_chain tests in parallel"
	@echo "  make run-multiplier-tree         Run multiplier_tree tests"
	@echo "  make run-multiplier-tree-parallel Run multiplier_tree tests in parallel"
	@echo "  make run-mux-tree               Run mux_tree tests"
	@echo "  make run-mux-tree-parallel       Run mux_tree tests in parallel"
	@echo "  make run-queue-depth             Run queue_depth tests"
	@echo "  make run-queue-depth-parallel    Run queue_depth tests in parallel"
	@echo "  make run-clk-divider             Run clock_divider_chain tests"
	@echo "  make run-clk-divider-parallel    Run clock_divider_chain tests in parallel"
	@echo "  make run-gray-counter            Run gray_counter_chain tests"
	@echo "  make run-gray-counter-parallel   Run gray_counter_chain tests in parallel"
	@echo ""
	@echo "GROUPED TARGETS:"
	@echo "  make run-trees                   Run tree FUBs (nand, xor, mux)"
	@echo "  make run-trees-parallel          Run tree FUBs in parallel"
	@echo "  make run-chains                  Run chain FUBs (inverter, carry, clk_div, gray)"
	@echo "  make run-chains-parallel         Run chain FUBs in parallel"
	@echo "  make run-datapath                Run datapath FUBs (multiplier, queue)"
	@echo "  make run-datapath-parallel       Run datapath FUBs in parallel"
	@echo ""
	@echo "TEST_LEVEL TARGETS:"
	@echo "  make run-gate                    Run all FUB tests at GATE level (quick)"
	@echo "  make run-gate-waves              Run all FUB tests at GATE level with waveforms"
	@echo "  make run-gate-parallel           Run all FUB tests at GATE level in parallel"
	@echo "  make run-gate-parallel-waves     Run all FUB tests at GATE level parallel + waves"
	@echo "  make run-func                    Run all FUB tests at FUNC level"
	@echo "  make run-func-waves              Run all FUB tests at FUNC level with waveforms"
	@echo "  make run-func-parallel           Run all FUB tests at FUNC level in parallel"
	@echo "  make run-func-parallel-waves     Run all FUB tests at FUNC level parallel + waves"
	@echo "  make run-full                    Run all FUB tests at FULL level (comprehensive)"
	@echo "  make run-full-waves              Run all FUB tests at FULL level with waveforms"
	@echo "  make run-full-parallel           Run all FUB tests at FULL level in parallel"
	@echo "  make run-full-parallel-waves     Run all FUB tests at FULL level parallel + waves"
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
# Individual FUB Targets
# ==============================================================================

.PHONY: run-nand-chain run-nand-chain-parallel \
        run-inverter-chain run-inverter-chain-parallel \
        run-xor-tree run-xor-tree-parallel \
        run-carry-chain run-carry-chain-parallel \
        run-multiplier-tree run-multiplier-tree-parallel \
        run-mux-tree run-mux-tree-parallel \
        run-queue-depth run-queue-depth-parallel \
        run-clk-divider run-clk-divider-parallel \
        run-gray-counter run-gray-counter-parallel

run-nand-chain:
	$(PYTEST) test_nand_chain.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

run-nand-chain-parallel:
	$(PYTEST) test_nand_chain.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

run-inverter-chain:
	$(PYTEST) test_inverter_chain.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

run-inverter-chain-parallel:
	$(PYTEST) test_inverter_chain.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

run-xor-tree:
	$(PYTEST) test_xor_tree.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

run-xor-tree-parallel:
	$(PYTEST) test_xor_tree.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

run-carry-chain:
	$(PYTEST) test_carry_chain.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

run-carry-chain-parallel:
	$(PYTEST) test_carry_chain.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

run-multiplier-tree:
	$(PYTEST) test_multiplier_tree.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

run-multiplier-tree-parallel:
	$(PYTEST) test_multiplier_tree.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

run-mux-tree:
	$(PYTEST) test_mux_tree.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

run-mux-tree-parallel:
	$(PYTEST) test_mux_tree.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

run-queue-depth:
	$(PYTEST) test_queue_depth.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

run-queue-depth-parallel:
	$(PYTEST) test_queue_depth.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

run-clk-divider:
	$(PYTEST) test_clock_divider_chain.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

run-clk-divider-parallel:
	$(PYTEST) test_clock_divider_chain.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

run-gray-counter:
	$(PYTEST) test_gray_counter_chain.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

run-gray-counter-parallel:
	$(PYTEST) test_gray_counter_chain.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# Grouped Targets
# ==============================================================================

.PHONY: run-trees run-trees-parallel \
        run-chains run-chains-parallel \
        run-datapath run-datapath-parallel

run-trees:
	$(PYTEST) test_nand_chain.py test_xor_tree.py test_mux_tree.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

run-trees-parallel:
	$(PYTEST) test_nand_chain.py test_xor_tree.py test_mux_tree.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

run-chains:
	$(PYTEST) test_inverter_chain.py test_carry_chain.py test_clock_divider_chain.py test_gray_counter_chain.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

run-chains-parallel:
	$(PYTEST) test_inverter_chain.py test_carry_chain.py test_clock_divider_chain.py test_gray_counter_chain.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

run-datapath:
	$(PYTEST) test_multiplier_tree.py test_queue_depth.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

run-datapath-parallel:
	$(PYTEST) test_multiplier_tree.py test_queue_depth.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# Test Level Targets
# ==============================================================================

.PHONY: run-gate run-gate-waves run-gate-parallel run-gate-parallel-waves \
        run-func run-func-waves run-func-parallel run-func-parallel-waves \
        run-full run-full-waves run-full-parallel run-full-parallel-waves

run-gate:
	TEST_LEVEL=gate $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

run-gate-waves:
	TEST_LEVEL=gate WAVES=1 $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

run-gate-parallel:
	TEST_LEVEL=gate $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

run-gate-parallel-waves:
	TEST_LEVEL=gate WAVES=1 $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

run-func:
	TEST_LEVEL=func $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

run-func-waves:
	TEST_LEVEL=func WAVES=1 $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

run-func-parallel:
	TEST_LEVEL=func $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

run-func-parallel-waves:
	TEST_LEVEL=func WAVES=1 $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

run-full:
	TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

run-full-waves:
	TEST_LEVEL=full WAVES=1 $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

run-full-parallel:
	TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

run-full-parallel-waves:
	TEST_LEVEL=full WAVES=1 $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

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
