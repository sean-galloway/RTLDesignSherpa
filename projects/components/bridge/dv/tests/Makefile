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
#
# Bridge tests run SERIALLY ONLY. Parallel execution via pytest-xdist
# has been removed for two reasons:
#   1. Each bridge test compiles a ~1 GB Verilator model. Running N in
#      parallel needs N×1 GB RAM during compile, which OOMs even on
#      256 GB hosts under load.
#   2. Bridge tests have observed cross-test state leakage when run in
#      the same pytest session (basic_connectivity vs address_decode
#      flakes), so serial execution is the only mode where we trust
#      pass/fail signals.
PYTEST = python3 -m pytest
PYTEST_VERBOSE = -v
PYTEST_QUIET = -q
PYTEST_TBSTYLE = --tb=short

# Test files: Matching-width configurations (no converters) - GENERATED
# Includes 2x2_rw (one master id_width=4, both slaves id_width=4 — no
# conversion needed) alongside the two 1x2 tests.
MATCHING_WIDTH_TESTS = test_bridge_1x2_rd.py test_bridge_1x2_wr.py test_bridge_2x2_rw.py

# Test files: Mixed-width configurations (uses converters) - GENERATED
MIXED_WIDTH_TESTS = test_bridge_1x3_rd.py test_bridge_1x3_wr.py

# Test files: APB protocol conversion - GENERATED
APB_TESTS = test_bridge_1x4_rd.py test_bridge_1x4_wr.py

# Test files: AXI-Lite protocol conversion - GENERATED
AXIL_TESTS = test_bridge_1x5_rd.py test_bridge_1x5_wr.py

# Test files: Channel-specific master configurations (wr/rd/rw mix) - GENERATED
# Exercises Phase 2 channel-aware port emission (write-only/read-only masters).
CHANNELS_TESTS = test_bridge_5x3_channels.py

# Test files: Currently disabled (commented out in bin/bridge_batch.csv)
# DISABLED_TESTS = test_bridge_4x4_rw.py test_bridge_example.py test_apb_bridge.py

# All tests (currently generated and available — 10 total)
ALL_TESTS = $(MATCHING_WIDTH_TESTS) $(MIXED_WIDTH_TESTS) $(APB_TESTS) $(AXIL_TESTS) $(CHANNELS_TESTS)

# Default target
.DEFAULT_GOAL := help

# ==============================================================================
# Help Target
# ==============================================================================

.PHONY: help
help:
	@echo "================================================================================"
	@echo "BRIDGE Tests Makefile (serial-only)"
	@echo "================================================================================"
	@echo ""
	@echo "EXECUTION TARGETS:"
	@echo "  make run-all                  Run all bridge tests"
	@echo "  make run-matching             Run matching-width tests (1x2_rd, 1x2_wr, 2x2_rw)"
	@echo "  make run-mixed                Run mixed-width tests (1x3_rd, 1x3_wr)"
	@echo "  make run-apb                  Run APB protocol tests (1x4_rd, 1x4_wr)"
	@echo "  make run-axil                 Run AXI-Lite protocol tests (1x5_rd, 1x5_wr)"
	@echo "  make run-channels             Run channel-specific tests (5x3_channels)"
	@echo ""
	@echo "WAVEFORM TARGETS:"
	@echo "  make run-all-waves            Run all bridge tests with waveforms"
	@echo "  make run-matching-waves       Run matching-width tests with waveforms"
	@echo "  make run-mixed-waves          Run mixed-width tests with waveforms"
	@echo "  make run-apb-waves            Run APB tests with waveforms"
	@echo "  make run-axil-waves           Run AXI-Lite tests with waveforms"
	@echo "  make run-channels-waves       Run channel-specific tests with waveforms"
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
	@echo "  make test-apb                 Regenerate APB protocol (RTL + tests + TB)"
	@echo "  make test-axil                Regenerate AXI-Lite protocol (RTL + tests + TB)"
	@echo "  make test-channels            Regenerate channel-specific (RTL + tests + TB)"
	@echo "  make regenerate-all           Regenerate every category sequentially"
	@echo "  make rebuild-all              Clean + regenerate everything (calls 'make test')"
	@echo ""
	@echo "EXECUTION NOTES:"
	@echo "  - Each bridge test compiles a ~1 GB Verilator model"
	@echo "  - All bridge targets are SERIAL — pytest-xdist support has been removed"
	@echo "    (parallel runs OOMed the host and exposed cross-test state leaks)"
	@echo "  - For coverage, ENV vars (COVERAGE=1, REG_LEVEL=…), or WAVES=1, just"
	@echo "    prefix the make invocation — they pass through to the sequential run"
	@echo ""
	@echo "REGENERATION NOTES:"
	@echo "  - Batch file: bin/bridge_batch.csv (10 active: 1x2_{rd,wr}, 1x3_{rd,wr},"
	@echo "                                       1x4_{rd,wr}, 1x5_{rd,wr}, 2x2_rw, 5x3_channels;"
	@echo "                                       4x4_rw and bridge_example are commented out)"
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

# ==============================================================================
# Run Targets - Mixed-Width Tests (Uses Converters)
# ==============================================================================

.PHONY: run-mixed
run-mixed:
	@echo "Running mixed-width bridge tests (1x3_rd, 1x3_wr)..."
	$(PYTEST) $(MIXED_WIDTH_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-mixed-waves
run-mixed-waves:
	@echo "Running mixed-width bridge tests with waveforms..."
	WAVES=1 $(PYTEST) $(MIXED_WIDTH_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

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

# ==============================================================================
# Run Targets - Channel-Specific Tests (Phase 2 wr/rd/rw masters)
# ==============================================================================

.PHONY: run-channels
run-channels:
	@echo "Running channel-specific bridge tests (5x3_channels)..."
	$(PYTEST) $(CHANNELS_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-channels-waves
run-channels-waves:
	@echo "Running channel-specific bridge tests with waveforms..."
	WAVES=1 $(PYTEST) $(CHANNELS_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

# ==============================================================================
# Run Targets - All Tests
# ==============================================================================

.PHONY: run-all
run-all:
	@echo "Running ALL bridge tests..."
	$(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-all-waves
run-all-waves:
	@echo "Running ALL bridge tests with waveforms..."
	WAVES=1 $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

# ==============================================================================
# Coverage Targets
# ==============================================================================

COVERAGE_DIR = coverage_data

.PHONY: run-coverage
run-coverage:
	@echo "Running bridge tests with coverage (sequential for safety)..."
	COVERAGE=1 $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-coverage-func
run-coverage-func:
	@echo "Running bridge tests with coverage (FUNC level)..."
	COVERAGE=1 REG_LEVEL=FUNC $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: coverage-report
coverage-report:
	@echo "Generating bridge coverage report..."
	python3 $(REPO_ROOT)/bin/cov_utils/generate_coverage_report.py --component bridge

.PHONY: fresh-coverage
fresh-coverage: clean-coverage run-coverage coverage-report
	@echo "Fresh bridge coverage complete"

.PHONY: clean-coverage
clean-coverage:
	@echo "Cleaning bridge coverage artifacts..."
	rm -rf $(COVERAGE_DIR) coverage_html
	@echo "Coverage artifacts cleaned"

# Legacy aliases for backward compatibility
.PHONY: run run-waves
run: run-all
run-waves: run-all-waves

# ==============================================================================
# REG_LEVEL Targets (gate/func/full) - Required by master Makefile
# ==============================================================================
# Bridge tests don't currently use REG_LEVEL since they're already specialized
# per configuration. These targets just map to run-all with the env var passed
# through.

.PHONY: run-all-gate
run-all-gate:
	@echo "Running ALL bridge tests (GATE level)..."
	REG_LEVEL=GATE $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-all-func
run-all-func:
	@echo "Running ALL bridge tests (FUNC level)..."
	REG_LEVEL=FUNC $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-all-full
run-all-full:
	@echo "Running ALL bridge tests (FULL level)..."
	REG_LEVEL=FULL $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

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
clean-all: clean
	@echo "Cleaning all test artifacts..."
	rm -rf logs local_sim_build sim_build sim_build_* coverage_data
	find . -name "*.vcd" -delete
	find . -name "*.fst" -delete
	find . -name "*.log" -delete
	@echo "All test artifacts cleaned."
	@echo ""
	@echo "NOTE: Generated test files preserved. To delete them: make build-clean"

.PHONY: clean-generated
clean-generated: build-clean
	@echo "All generated files (RTL + tests) deleted."
	@echo "Run 'make regenerate-all' to regenerate them."

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
	@echo "REGENERATING MIXED-WIDTH TESTS (1x3_rd, 1x3_wr)"
	@echo "================================================================================"
	@echo "Generating bridge_1x3_rd tests..."
	cd $(BIN_DIR) && python3 bridge_generator.py \
		--ports $(CONFIG_DIR)/bridge_1x3_rd_mixed.toml \
		--name bridge_1x3_rd \
		--output-dir $(RTL_FROM_BIN) \
		--generate-tests \
		--output-tb $(TB_FROM_BIN) \
		--output-test $(TEST_FROM_BIN)
	@echo "Generating bridge_1x3_wr tests..."
	cd $(BIN_DIR) && python3 bridge_generator.py \
		--ports $(CONFIG_DIR)/bridge_1x3_wr_mixed.toml \
		--name bridge_1x3_wr \
		--output-dir $(RTL_FROM_BIN) \
		--generate-tests \
		--output-tb $(TB_FROM_BIN) \
		--output-test $(TEST_FROM_BIN)
	@echo ""
	@echo "✅ Mixed-width test files regenerated"
	@echo "================================================================================"

.PHONY: test-apb
test-apb:
	@echo "================================================================================"
	@echo "REGENERATING APB PROTOCOL TESTS (1x4_rd, 1x4_wr)"
	@echo "================================================================================"
	@echo "Generating bridge_1x4_rd tests..."
	cd $(BIN_DIR) && python3 bridge_generator.py \
		--ports $(CONFIG_DIR)/bridge_1x4_rd_apb.toml \
		--name bridge_1x4_rd \
		--output-dir $(RTL_FROM_BIN) \
		--generate-tests \
		--output-tb $(TB_FROM_BIN) \
		--output-test $(TEST_FROM_BIN)
	@echo "Generating bridge_1x4_wr tests..."
	cd $(BIN_DIR) && python3 bridge_generator.py \
		--ports $(CONFIG_DIR)/bridge_1x4_wr_apb.toml \
		--name bridge_1x4_wr \
		--output-dir $(RTL_FROM_BIN) \
		--generate-tests \
		--output-tb $(TB_FROM_BIN) \
		--output-test $(TEST_FROM_BIN)
	@echo ""
	@echo "✅ APB protocol test files regenerated"
	@echo "================================================================================"

.PHONY: test-axil
test-axil:
	@echo "================================================================================"
	@echo "REGENERATING AXI-LITE PROTOCOL TESTS (1x5_rd, 1x5_wr)"
	@echo "================================================================================"
	@echo "Generating bridge_1x5_rd tests..."
	cd $(BIN_DIR) && python3 bridge_generator.py \
		--ports $(CONFIG_DIR)/bridge_1x5_rd_axil.toml \
		--name bridge_1x5_rd \
		--output-dir $(RTL_FROM_BIN) \
		--generate-tests \
		--output-tb $(TB_FROM_BIN) \
		--output-test $(TEST_FROM_BIN)
	@echo "Generating bridge_1x5_wr tests..."
	cd $(BIN_DIR) && python3 bridge_generator.py \
		--ports $(CONFIG_DIR)/bridge_1x5_wr_axil.toml \
		--name bridge_1x5_wr \
		--output-dir $(RTL_FROM_BIN) \
		--generate-tests \
		--output-tb $(TB_FROM_BIN) \
		--output-test $(TEST_FROM_BIN)
	@echo ""
	@echo "✅ AXI-Lite protocol test files regenerated"
	@echo "================================================================================"

.PHONY: test-channels
test-channels:
	@echo "================================================================================"
	@echo "REGENERATING CHANNEL-SPECIFIC TESTS (5x3_channels)"
	@echo "================================================================================"
	@echo "Generating bridge_5x3_channels tests..."
	cd $(BIN_DIR) && python3 bridge_generator.py \
		--ports $(CONFIG_DIR)/bridge_5x3_channels.toml \
		--name bridge_5x3_channels \
		--output-dir $(RTL_FROM_BIN) \
		--generate-tests \
		--output-tb $(TB_FROM_BIN) \
		--output-test $(TEST_FROM_BIN)
	@echo ""
	@echo "✅ Channel-specific test files regenerated"
	@echo "================================================================================"

# Create default batch file if missing
$(BATCH_FILE):
	@echo "Creating default bridge_batch.csv..."
	@echo "ERROR: $(BATCH_FILE) not found!"
	@echo "Please create it with the following format:"
	@echo "  name,ports,connectivity,output_dir,output_tb,output_test,expose_arbiter_signals"
	@echo "  bridge_1x2_rd,../dv/bridge_csv/bridge_minimal_rd_1x2_ports.csv,../dv/bridge_csv/bridge_minimal_rd_1x2_connectivity.csv,../rtl,../dv/tbclasses,../dv/tests,false"
	@exit 1

.PHONY: regenerate-all
regenerate-all: test-matching test-mixed test-apb test-axil test-channels
	@echo "================================================================================"
	@echo "✅ ALL TEST FILES REGENERATED"
	@echo "================================================================================"
	@echo "Generated tests:"
	@echo "  - test_bridge_1x2_rd.py, test_bridge_1x2_wr.py (matching-width)"
	@echo "  - test_bridge_2x2_rw.py (matching-width)"
	@echo "  - test_bridge_1x3_rd.py, test_bridge_1x3_wr.py (mixed-width)"
	@echo "  - test_bridge_1x4_rd.py, test_bridge_1x4_wr.py (APB protocol)"
	@echo "  - test_bridge_1x5_rd.py, test_bridge_1x5_wr.py (AXI-Lite protocol)"
	@echo "  - test_bridge_5x3_channels.py (channel-specific wr/rd/rw)"
	@echo "================================================================================"

.PHONY: rebuild-all
rebuild-all: build-clean regenerate-all
	@echo "================================================================================"
	@echo "✅ FULL REBUILD COMPLETE (RTL + TESTS)"
	@echo "================================================================================"
	@echo ""
	@echo "Next steps:"
	@echo "  1. Run matching-width tests: make run-matching"
	@echo "  2. Run mixed-width tests: make run-mixed"
	@echo "  3. Run APB tests: make run-apb"
	@echo "  4. Run AXI-Lite tests: make run-axil"
	@echo "  5. Or run all: make run-all"
	@echo "================================================================================"

# ==============================================================================
# Pattern-rule fallback: any `-waves` variant of an existing target is just
# the same target with WAVES=1 in the environment. Lets you do
#   make run-all-gate-waves
#   make run-fub-func-parallel-waves
#   ...
# without writing a separate stanza per category x level x parallelism.
# Explicit `-waves` recipes elsewhere in this file take precedence (Make
# prefers explicit over pattern rules); anything not explicitly defined
# falls through here.
# ==============================================================================
%-waves:
	@$(MAKE) --no-print-directory $* WAVES=1
