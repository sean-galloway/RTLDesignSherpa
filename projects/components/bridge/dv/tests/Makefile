# ==============================================================================
# BRIDGE Tests Makefile
# ==============================================================================
#
# Local test runner for BRIDGE tests
#
# Usage:
#   cd $REPO_ROOT/projects/components/bridge/dv/tests
#   make <target>
#
# Quick start:
#   make help           - Show available targets
#   make run-passing    - Run passing tests (1x2_rd, 1x2_wr, 2x2_rw)
#   make run-passing-waves - Run passing tests with waveforms
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
PYTEST_RERUNS = --reruns 0 --reruns-delay 1

# Test files: Matching-width configurations (no converters) - GENERATED
MATCHING_WIDTH_TESTS = test_bridge_1x2_rd.py test_bridge_1x2_wr.py

# Test files: Mixed-width configurations (uses converters) - GENERATED
MIXED_WIDTH_TESTS = test_bridge_1x3_rd.py test_bridge_1x3_wr.py

# Test files: APB protocol conversion - GENERATED
APB_TESTS = test_bridge_1x4_rd.py test_bridge_1x4_wr.py

# Test files: AXI-Lite protocol conversion - GENERATED
AXIL_TESTS = test_bridge_1x5_rd.py test_bridge_1x5_wr.py

# Test files: Currently disabled (not in batch CSV)
# DISABLED_TESTS = test_bridge_2x2_rw.py test_bridge_4x4_rw.py test_bridge_5x3_channels.py test_bridge_example.py test_apb_bridge.py

# All tests (currently generated and available)
ALL_TESTS = $(MATCHING_WIDTH_TESTS) $(MIXED_WIDTH_TESTS) $(APB_TESTS) $(AXIL_TESTS)

# Default target
.DEFAULT_GOAL := help

# ==============================================================================
# Help Target
# ==============================================================================

.PHONY: help
help:
	@echo "================================================================================"
	@echo "BRIDGE Tests Makefile"
	@echo "================================================================================"
	@echo ""
	@echo "⚠️  CRITICAL SAFETY WARNING:"
	@echo "  Bridge tests compile large Verilator models (~1GB each)."
	@echo "  PARALLEL EXECUTION TARGETS BELOW ARE DISABLED FOR SAFETY."
	@echo "  Running parallel tests can cause system crashes due to memory exhaustion."
	@echo ""
	@echo "SAFE EXECUTION TARGETS (RECOMMENDED):"
	@echo "  make run-all                  Run all bridge tests (SEQUENTIAL - SAFE)"
	@echo "  make run-matching             Run matching-width tests (1x2_rd, 1x2_wr, 2x2_rw)"
	@echo "  make run-mixed                Run mixed-width tests (1x3_rd, 1x3_wr)"
	@echo "  make run-apb                  Run APB protocol tests (1x4_rd, 1x4_wr)"
	@echo "  make run-axil                 Run AXI-Lite protocol tests (1x5_rd, 1x5_wr)"
	@echo ""
	@echo "⚠️  DANGEROUS TARGETS (CAN CRASH SYSTEM):"
	@echo "  make run-all-parallel         ❌ DISABLED - Would use 48GB+ RAM"
	@echo "  make run-matching-parallel    ❌ DISABLED - Would use 48GB+ RAM"
	@echo "  make run-mixed-parallel       ❌ DISABLED - Would use 48GB+ RAM"
	@echo "  make run-apb-parallel         ❌ DISABLED - Would use 48GB+ RAM"
	@echo "  make run-axil-parallel        ❌ DISABLED - Would use 48GB+ RAM"
	@echo ""
	@echo "WAVEFORM TARGETS:"
	@echo "  make run-all-waves            Run all bridge tests with waveforms"
	@echo "  make run-matching-waves       Run matching-width tests with waveforms"
	@echo "  make run-mixed-waves          Run mixed-width tests with waveforms"
	@echo "  make run-apb-waves            Run APB tests with waveforms"
	@echo "  make run-axil-waves           Run AXI-Lite tests with waveforms"
	@echo ""
	@echo "UTILITY TARGETS:"
	@echo "  make collect                  Collect (don't run) tests"
	@echo "  make clean                    Clean local artifacts"
	@echo "  make clean-all                Clean all test artifacts and generated files"
	@echo ""
	@echo "BUILD/REGENERATION TARGETS:"
	@echo "  make build-clean              Delete ALL generated RTL and tests"
	@echo "  make clean-rtl                Delete ALL generated RTL only"
	@echo "  make clean-test               Delete ALL generated tests only"
	@echo ""
	@echo "RTL ONLY (no tests/TB):"
	@echo "  make rtl                      Regenerate ALL bridge RTL (no tests)"
	@echo "  make rtl-matching             Regenerate matching-width RTL only"
	@echo "  make rtl-mixed                Regenerate mixed-width RTL only"
	@echo ""
	@echo "RTL + TESTS + TB (complete generation):"
	@echo "  make test                     Regenerate ALL (RTL + tests + TB) from batch CSV"
	@echo "  make test-matching            Regenerate matching-width (RTL + tests + TB)"
	@echo "  make test-mixed               Regenerate mixed-width (RTL + tests + TB)"
	@echo "  make rebuild-all              Clean + regenerate everything (calls 'make test')"
	@echo ""
	@echo "SAFETY NOTES:"
	@echo "  - Each bridge test compiles ~1GB Verilator model during simulation"
	@echo "  - Parallel execution with -n 48 would require 48GB+ RAM simultaneously"
	@echo "  - Sequential execution enforced in conftest.py for system safety"
	@echo "  - System has 256GB RAM, but parallel compilation still risks OOM"
	@echo ""
	@echo "REGENERATION NOTES:"
	@echo "  - Batch file: bin/bridge_batch.csv (7 configs: 1x2_rd, 1x2_wr, 2x2, 4x4, 5x3, example, apb)"
	@echo "  - All tests are GENERATED from YAML configs"
	@echo "  - Uses unified bridge_generator.py with Jinja2 templates"
	@echo "  - RTL generation: bridge_generator.py --ports X --connectivity Y"
	@echo "  - RTL + tests: bridge_generator.py --ports X --connectivity Y --generate-tests"
	@echo "  - Batch mode: bridge_generator.py --bulk bridge_batch.csv --generate-tests"
	@echo "  - Templates: bin/bridge_pkg/jinja_templates/"
	@echo ""
	@echo "================================================================================"

# ==============================================================================
# Run Targets - Matching-Width Tests (No Converters)
# ==============================================================================

.PHONY: run-matching
run-matching:
	@echo "Running matching-width bridge tests (1x2_rd, 1x2_wr, 2x2_rw)..."
	$(PYTEST) $(MATCHING_WIDTH_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-matching-waves
run-matching-waves:
	@echo "Running matching-width bridge tests with waveforms..."
	WAVES=1 $(PYTEST) $(MATCHING_WIDTH_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-matching-parallel
run-matching-parallel:
	@echo "Running matching-width bridge tests in parallel (48 workers)..."
	$(PYTEST) $(MATCHING_WIDTH_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-matching-parallel-waves
run-matching-parallel-waves:
	@echo "Running matching-width bridge tests in parallel with waveforms..."
	WAVES=1 $(PYTEST) $(MATCHING_WIDTH_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# Run Targets - Mixed-Width Tests (Uses Converters)
# ==============================================================================

.PHONY: run-mixed
run-mixed:
	@echo "Running mixed-width bridge tests (4x4, 5x3)..."
	$(PYTEST) $(MIXED_WIDTH_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-mixed-waves
run-mixed-waves:
	@echo "Running mixed-width bridge tests with waveforms..."
	WAVES=1 $(PYTEST) $(MIXED_WIDTH_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-mixed-parallel
run-mixed-parallel:
	@echo "Running mixed-width bridge tests in parallel..."
	$(PYTEST) $(MIXED_WIDTH_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-mixed-parallel-waves
run-mixed-parallel-waves:
	@echo "Running mixed-width bridge tests in parallel with waveforms..."
	WAVES=1 $(PYTEST) $(MIXED_WIDTH_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# Run Targets - APB Protocol Tests
# ==============================================================================

.PHONY: run-apb
run-apb:
	@echo "Running APB protocol bridge tests (1x4_rd, 1x4_wr)..."
	$(PYTEST) $(APB_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-apb-waves
run-apb-waves:
	@echo "Running APB protocol bridge tests with waveforms..."
	WAVES=1 $(PYTEST) $(APB_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-apb-parallel
run-apb-parallel:
	@echo "Running APB protocol bridge tests in parallel..."
	$(PYTEST) $(APB_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-apb-parallel-waves
run-apb-parallel-waves:
	@echo "Running APB protocol bridge tests in parallel with waveforms..."
	WAVES=1 $(PYTEST) $(APB_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# Run Targets - AXI-Lite Protocol Tests
# ==============================================================================

.PHONY: run-axil
run-axil:
	@echo "Running AXI-Lite protocol bridge tests (1x5_rd, 1x5_wr)..."
	$(PYTEST) $(AXIL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-axil-waves
run-axil-waves:
	@echo "Running AXI-Lite protocol bridge tests with waveforms..."
	WAVES=1 $(PYTEST) $(AXIL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-axil-parallel
run-axil-parallel:
	@echo "Running AXI-Lite protocol bridge tests in parallel..."
	$(PYTEST) $(AXIL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-axil-parallel-waves
run-axil-parallel-waves:
	@echo "Running AXI-Lite protocol bridge tests in parallel with waveforms..."
	WAVES=1 $(PYTEST) $(AXIL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# Run Targets - All Tests
# ==============================================================================

.PHONY: run-all
run-all:
	@echo "Running ALL bridge tests (10 tests total)..."
	$(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-all-waves
run-all-waves:
	@echo "Running ALL bridge tests with waveforms..."
	WAVES=1 $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-all-parallel
run-all-parallel:
	@echo "Running ALL bridge tests in parallel..."
	$(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-all-parallel-waves
run-all-parallel-waves:
	@echo "Running ALL bridge tests in parallel with waveforms..."
	WAVES=1 $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# Legacy aliases for backward compatibility
.PHONY: run run-waves run-parallel run-parallel-waves
run: run-all
run-waves: run-all-waves
run-parallel: run-all-parallel
run-parallel-waves: run-all-parallel-waves

# ==============================================================================
# Utility Targets
# ==============================================================================

.PHONY: collect
collect:
	@echo "Collecting bridge tests..."
	$(PYTEST) test_bridge_*.py --collect-only

.PHONY: clean
clean:
	@echo "Cleaning local artifacts..."
	rm -rf __pycache__ .pytest_cache *.pyc

.PHONY: clean-all
clean-all: clean build-clean
	@echo "Cleaning all test artifacts and generated files..."
	rm -rf logs local_sim_build sim_build sim_build_*
	find . -name "*.vcd" -delete
	find . -name "*.fst" -delete
	find . -name "*.log" -delete
	@echo "All test artifacts and generated files cleaned."

# ==============================================================================
# Build/Regeneration Targets
# ==============================================================================

BIN_DIR = ../../bin
RTL_DIR = ../../rtl
TB_DIR = ../tbclasses
# When cd'd to BIN_DIR, use this path to RTL (from bin/ perspective)
RTL_FROM_BIN = ../rtl/generated

.PHONY: clean-rtl
clean-rtl:
	@echo "================================================================================"
	@echo "DELETING ALL GENERATED RTL"
	@echo "================================================================================"
	@echo "Deleting $(RTL_DIR)/generated/ directory..."
	rm -rf $(RTL_DIR)/generated/
	@echo "✅ All generated RTL deleted"
	@echo "================================================================================"

.PHONY: clean-test
clean-test:
	@echo "================================================================================"
	@echo "DELETING ALL GENERATED TESTS"
	@echo "================================================================================"
	@echo "Deleting GENERATED test files..."
	rm -f test_bridge_1x2_rd.py
	rm -f test_bridge_1x2_wr.py
	rm -f test_bridge_1x3_rd.py
	rm -f test_bridge_1x3_wr.py
	rm -f test_bridge_1x4_rd.py
	rm -f test_bridge_1x4_wr.py
	rm -f test_bridge_1x5_rd.py
	rm -f test_bridge_1x5_wr.py
	rm -f test_bridge_2x2_rw.py
	rm -f test_bridge_4x4_rw.py
	rm -f test_bridge_5x3_channels.py
	rm -f test_bridge_example.py
	rm -f test_apb_bridge.py
	@echo "Deleting GENERATED testbench classes..."
	rm -f $(TB_DIR)/bridge1x2_rd_tb.py
	rm -f $(TB_DIR)/bridge1x2_wr_tb.py
	rm -f $(TB_DIR)/bridge1x3_rd_tb.py
	rm -f $(TB_DIR)/bridge1x3_wr_tb.py
	rm -f $(TB_DIR)/bridge1x4_rd_tb.py
	rm -f $(TB_DIR)/bridge1x4_wr_tb.py
	rm -f $(TB_DIR)/bridge1x5_rd_tb.py
	rm -f $(TB_DIR)/bridge1x5_wr_tb.py
	rm -f $(TB_DIR)/bridge2x2_rw_tb.py
	rm -f $(TB_DIR)/bridge4x4_rw_tb.py
	rm -f $(TB_DIR)/bridge5x3_channels_tb.py
	rm -f $(TB_DIR)/bridge_example_tb.py
	rm -f $(TB_DIR)/test_apb_bridge_tb.py
	@echo "✅ All generated tests deleted"
	@echo "================================================================================"

.PHONY: build-clean
build-clean: clean-rtl clean-test
	@echo "================================================================================"
	@echo "✅ ALL GENERATED FILES DELETED"
	@echo "================================================================================"

# YAML config files are at test_configs/ from bin/ directory
CONFIG_DIR = test_configs

# Output directories from bin/ perspective
TB_FROM_BIN = ../dv/tbclasses
TEST_FROM_BIN = ../dv/tests

# Unified batch file (used for both RTL and tests)
BATCH_FILE = $(BIN_DIR)/bridge_batch.csv

.PHONY: rtl-matching
rtl-matching:
	@echo "================================================================================"
	@echo "REGENERATING MATCHING-WIDTH RTL (1x2_rd, 1x2_wr, 2x2_rw)"
	@echo "================================================================================"
	@echo "Generating bridge_1x2_rd..."
	cd $(BIN_DIR) && python3 bridge_generator.py \
		--ports $(CONFIG_DIR)/bridge_1x2_rd_matched.toml \
		--name bridge_1x2_rd \
		--output-dir $(RTL_FROM_BIN)
	@echo "Generating bridge_1x2_wr..."
	cd $(BIN_DIR) && python3 bridge_generator.py \
		--ports $(CONFIG_DIR)/bridge_1x2_wr_matched.toml \
		--name bridge_1x2_wr \
		--output-dir $(RTL_FROM_BIN)
	@echo "Generating bridge_2x2_rw..."
	cd $(BIN_DIR) && python3 bridge_generator.py \
		--ports $(CONFIG_DIR)/bridge_2x2_rw.toml \
		--name bridge_2x2_rw \
		--output-dir $(RTL_FROM_BIN)
	@echo ""
	@echo "✅ Matching-width RTL regenerated"
	@echo "================================================================================"

.PHONY: rtl-mixed
rtl-mixed:
	@echo "================================================================================"
	@echo "REGENERATING MIXED-WIDTH RTL (4x4, 5x3, example)"
	@echo "================================================================================"
	@echo "Generating bridge_4x4_rw..."
	cd $(BIN_DIR) && python3 bridge_generator.py \
		--ports $(CONFIG_DIR)/bridge_4x4_rw.toml \
		--name bridge_4x4_rw \
		--output-dir $(RTL_FROM_BIN)
	@echo "Generating bridge_5x3_channels..."
	cd $(BIN_DIR) && python3 bridge_generator.py \
		--ports $(CONFIG_DIR)/bridge_5x3_channels.toml \
		--name bridge_5x3_channels \
		--output-dir $(RTL_FROM_BIN)
	@echo "Generating bridge_example..."
	cd $(BIN_DIR) && python3 bridge_generator.py \
		--ports $(CONFIG_DIR)/bridge_example.toml \
		--name bridge_example \
		--output-dir $(RTL_FROM_BIN)
	@echo ""
	@echo "✅ Mixed-width RTL regenerated"
	@echo "================================================================================"

.PHONY: rtl
rtl: rtl-matching rtl-mixed
	@echo "================================================================================"
	@echo "✅ ALL BRIDGE RTL REGENERATED"
	@echo "================================================================================"

.PHONY: test
test: $(BATCH_FILE)
	@echo "================================================================================"
	@echo "REGENERATING ALL TEST FILES FROM BATCH"
	@echo "================================================================================"
	@cd $(BIN_DIR) && python3 bridge_generator.py --bulk bridge_batch.csv --generate-tests
	@echo ""
	@echo "✅ All test files regenerated from $(BATCH_FILE)"
	@echo "================================================================================"

.PHONY: test-matching
test-matching:
	@echo "================================================================================"
	@echo "REGENERATING MATCHING-WIDTH TESTS (1x2_rd, 1x2_wr, 2x2_rw)"
	@echo "================================================================================"
	@echo "Generating bridge_1x2_rd tests..."
	cd $(BIN_DIR) && python3 bridge_generator.py \
		--ports $(CONFIG_DIR)/bridge_1x2_rd_matched.toml \
		--name bridge_1x2_rd \
		--output-dir $(RTL_FROM_BIN) \
		--generate-tests \
		--output-tb $(TB_FROM_BIN) \
		--output-test $(TEST_FROM_BIN)
	@echo "Generating bridge_1x2_wr tests..."
	cd $(BIN_DIR) && python3 bridge_generator.py \
		--ports $(CONFIG_DIR)/bridge_1x2_wr_matched.toml \
		--name bridge_1x2_wr \
		--output-dir $(RTL_FROM_BIN) \
		--generate-tests \
		--output-tb $(TB_FROM_BIN) \
		--output-test $(TEST_FROM_BIN)
	@echo "Generating bridge_2x2_rw tests..."
	cd $(BIN_DIR) && python3 bridge_generator.py \
		--ports $(CONFIG_DIR)/bridge_2x2_rw.toml \
		--name bridge_2x2_rw \
		--output-dir $(RTL_FROM_BIN) \
		--generate-tests \
		--output-tb $(TB_FROM_BIN) \
		--output-test $(TEST_FROM_BIN)
	@echo ""
	@echo "✅ Matching-width test files regenerated"
	@echo "================================================================================"

.PHONY: test-mixed
test-mixed:
	@echo "================================================================================"
	@echo "REGENERATING MIXED-WIDTH TESTS (4x4, 5x3, example)"
	@echo "================================================================================"
	@echo "Generating bridge_4x4_rw tests..."
	cd $(BIN_DIR) && python3 bridge_generator.py \
		--ports $(CONFIG_DIR)/bridge_4x4_rw.toml \
		--name bridge_4x4_rw \
		--output-dir $(RTL_FROM_BIN) \
		--generate-tests \
		--output-tb $(TB_FROM_BIN) \
		--output-test $(TEST_FROM_BIN)
	@echo "Generating bridge_5x3_channels tests..."
	cd $(BIN_DIR) && python3 bridge_generator.py \
		--ports $(CONFIG_DIR)/bridge_5x3_channels.toml \
		--name bridge_5x3_channels \
		--output-dir $(RTL_FROM_BIN) \
		--generate-tests \
		--output-tb $(TB_FROM_BIN) \
		--output-test $(TEST_FROM_BIN)
	@echo "Generating bridge_example tests..."
	cd $(BIN_DIR) && python3 bridge_generator.py \
		--ports $(CONFIG_DIR)/bridge_example.toml \
		--name bridge_example \
		--output-dir $(RTL_FROM_BIN) \
		--generate-tests \
		--output-tb $(TB_FROM_BIN) \
		--output-test $(TEST_FROM_BIN)
	@echo ""
	@echo "✅ Mixed-width test files regenerated"
	@echo "================================================================================"

# Create default batch file if missing
$(BATCH_FILE):
	@echo "Creating default bridge_batch.csv..."
	@echo "ERROR: $(BATCH_FILE) not found!"
	@echo "Please create it with the following format:"
	@echo "  name,ports,connectivity,output_dir,output_tb,output_test,expose_arbiter_signals"
	@echo "  bridge_1x2_rd,../dv/bridge_csv/bridge_minimal_rd_1x2_ports.csv,../dv/bridge_csv/bridge_minimal_rd_1x2_connectivity.csv,../rtl,../dv/tbclasses,../dv/tests,false"
	@exit 1

.PHONY: rebuild-all
rebuild-all: build-clean test
	@echo "================================================================================"
	@echo "✅ FULL REBUILD COMPLETE (RTL + TESTS)"
	@echo "================================================================================"
	@echo "Note: 'make test' generates both RTL and tests from unified batch file"
	@echo ""
	@echo "Next steps:"
	@echo "  1. Run matching-width tests: make run-matching-parallel"
	@echo "  2. Run mixed-width tests: make run-mixed-parallel"
	@echo "  3. Or run all: make run-parallel"
	@echo "================================================================================"
