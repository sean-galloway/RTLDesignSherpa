# ==============================================================================
# STREAM Subsystem Test Makefile
# ==============================================================================
#
# PREREQUISITES:
#   Must be run with sourced environment:
#     source $REPO_ROOT/env_python  # Sets $REPO_ROOT and activates venv
#     cd $REPO_ROOT/projects/components/stream/dv/tests
#     make <target>
#
# Quick start:
#   make help           - Show all available targets
#   make run-fub        - Run all FUB tests
#   make run-macro      - Run all macro tests
#   make run-all        - Run all tests
#   make clean-all      - Clean all test artifacts
#
# Advanced:
#   make run-fub-parallel   - Run FUB tests in parallel (48 workers)
#   make run-fub-gate       - Run FUB tests at GATE level
#   make run-fub-func       - Run FUB tests at FUNC level (default)
#   make run-fub-full       - Run FUB tests at FULL level
#   make collect-fub        - Collect (don't run) FUB tests
#
# ==============================================================================

# Force bash shell (required for source command)
SHELL := /bin/bash

# Check if REPO_ROOT is set (from env_python)
ifndef REPO_ROOT
$(error REPO_ROOT is not set. Please run: source $$REPO_ROOT/env_python)
endif

# Repository root comes from environment (set by env_python)
# No path calculation needed - works from any project location!

# Test directories
FUB_TESTS_DIR = fub
MACRO_TESTS_DIR = macro

# Pytest options
PYTEST = python3 -m pytest
PYTEST_VERBOSE = -v
PYTEST_QUIET = -q
PYTEST_XDIST = -n 48  # 48 parallel workers (matching AMBA)
PYTEST_TBSTYLE = --tb=short
PYTEST_RERUNS = --reruns 3 --reruns-delay 1  # Retry failed tests

# Default target - show help
.DEFAULT_GOAL := help

# ==============================================================================
# Help Target
# ==============================================================================

.PHONY: help
help:
	@echo "================================================================================"
	@echo "STREAM Test Makefile - Available Targets"
	@echo "================================================================================"
	@echo ""
	@echo "RUN TARGETS (by Test Type):"
	@echo "  make run-fub              Run all FUB (Functional Unit Block) tests"
	@echo "  make run-fub-parallel     Run FUB tests in parallel (48 workers)"
	@echo "  make run-macro            Run all macro tests"
	@echo "  make run-macro-parallel   Run macro tests in parallel"
	@echo "  make run-all              Run all tests (FUB + macro)"
	@echo "  make run-all-parallel     Run all tests in parallel"
	@echo ""
	@echo "REG_LEVEL TARGETS (configurable test depth):"
	@echo "  GATE = Quick smoke tests (~5 min), FUNC = Default (~30 min), FULL = Comprehensive (~4 hr)"
	@echo ""
	@echo "  FUB Tests:"
	@echo "    make run-fub-{gate|func|full}[-parallel]"
	@echo "  Macro Tests:"
	@echo "    make run-macro-{gate|func|full}[-parallel]"
	@echo "  ALL Tests:"
	@echo "    make run-all-{gate|func|full}[-parallel]"
	@echo ""
	@echo "INDIVIDUAL TEST MODULES:"
	@echo "  make run-perf             Run perf_profiler tests only"
	@echo "  make run-scheduler        Run scheduler tests only"
	@echo "  make run-sram             Run simple_sram tests only"
	@echo "  make run-axi-rd           Run axi_read_engine tests only"
	@echo "  make run-axi-wr           Run axi_write_engine tests only"
	@echo "  make run-sram-ctrl        Run sram_controller tests only"
	@echo "  make run-desc-engine      Run descriptor_engine tests only"
	@echo "  make run-apbtodescr       Run apbtodescr tests only"
	@echo ""
	@echo "COLLECTION TARGETS (verify tests, don't run):"
	@echo "  make collect-fub          Collect FUB tests (verify imports)"
	@echo "  make collect-macro        Collect macro tests"
	@echo "  make collect-all          Collect all tests"
	@echo ""
	@echo "CLEAN TARGETS:"
	@echo "  make clean-fub            Remove FUB test artifacts"
	@echo "  make clean-macro          Remove macro test artifacts"
	@echo "  make clean-all            Remove all test artifacts"
	@echo "  make clean-logs           Remove all log files"
	@echo "  make clean-pycache        Remove Python cache files"
	@echo "  make clean-build          Remove simulation build directories"
	@echo "  make clean-vcd            Remove VCD waveform files"
	@echo ""
	@echo "DEVELOPMENT TARGETS:"
	@echo "  make ptw-fub              Run pytest-watch for FUB tests (auto-rerun)"
	@echo "  make ptw-macro            Run pytest-watch for macro tests (auto-rerun)"
	@echo ""
	@echo "UTILITY TARGETS:"
	@echo "  make list-fub             List all FUB test modules"
	@echo "  make list-macro           List all macro test modules"
	@echo "  make status               Show test status and coverage"
	@echo ""
	@echo "================================================================================"
	@echo "Prerequisites: source $(REPO_ROOT)/env_python"
	@echo "Current REPO_ROOT: $(REPO_ROOT)"
	@echo "================================================================================"

# ==============================================================================
# Run Targets - FUB Tests
# ==============================================================================

.PHONY: run-fub
run-fub:
	@echo "================================================================================"
	@echo "Running STREAM FUB Tests (default FUNC level)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_*.py

.PHONY: run-fub-parallel
run-fub-parallel:
	@echo "================================================================================"
	@echo "Running STREAM FUB Tests (Parallel - 48 workers, default FUNC level)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(FUB_TESTS_DIR)/test_*.py

# REG_LEVEL Control for FUB Tests
.PHONY: run-fub-gate
run-fub-gate:
	@echo "================================================================================"
	@echo "Running STREAM FUB Tests - GATE level (quick smoke test)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_*.py

.PHONY: run-fub-func
run-fub-func:
	@echo "================================================================================"
	@echo "Running STREAM FUB Tests - FUNC level (functional coverage)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_*.py

.PHONY: run-fub-full
run-fub-full:
	@echo "================================================================================"
	@echo "Running STREAM FUB Tests - FULL level (comprehensive validation)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_*.py

# Parallel versions of REG_LEVEL targets
.PHONY: run-fub-gate-parallel
run-fub-gate-parallel:
	@echo "================================================================================"
	@echo "Running STREAM FUB Tests - GATE level PARALLEL (48 workers)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(FUB_TESTS_DIR)/test_*.py

.PHONY: run-fub-func-parallel
run-fub-func-parallel:
	@echo "================================================================================"
	@echo "Running STREAM FUB Tests - FUNC level PARALLEL (48 workers)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(FUB_TESTS_DIR)/test_*.py

.PHONY: run-fub-full-parallel
run-fub-full-parallel:
	@echo "================================================================================"
	@echo "Running STREAM FUB Tests - FULL level PARALLEL (48 workers)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(FUB_TESTS_DIR)/test_*.py

# ==============================================================================
# Run Targets - Macro Tests
# ==============================================================================

.PHONY: run-macro
run-macro:
	@echo "================================================================================"
	@echo "Running STREAM Macro Tests (default FUNC level)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(MACRO_TESTS_DIR)/test_*.py

.PHONY: run-macro-parallel
run-macro-parallel:
	@echo "================================================================================"
	@echo "Running STREAM Macro Tests (Parallel - 48 workers)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(MACRO_TESTS_DIR)/test_*.py

# REG_LEVEL Control for Macro Tests
.PHONY: run-macro-gate
run-macro-gate:
	@echo "================================================================================"
	@echo "Running STREAM Macro Tests - GATE level"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(MACRO_TESTS_DIR)/test_*.py

.PHONY: run-macro-func
run-macro-func:
	@echo "================================================================================"
	@echo "Running STREAM Macro Tests - FUNC level"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(MACRO_TESTS_DIR)/test_*.py

.PHONY: run-macro-full
run-macro-full:
	@echo "================================================================================"
	@echo "Running STREAM Macro Tests - FULL level"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(MACRO_TESTS_DIR)/test_*.py

# Parallel versions
.PHONY: run-macro-gate-parallel
run-macro-gate-parallel:
	@echo "================================================================================"
	@echo "Running STREAM Macro Tests - GATE level PARALLEL (48 workers)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(MACRO_TESTS_DIR)/test_*.py

.PHONY: run-macro-func-parallel
run-macro-func-parallel:
	@echo "================================================================================"
	@echo "Running STREAM Macro Tests - FUNC level PARALLEL (48 workers)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(MACRO_TESTS_DIR)/test_*.py

.PHONY: run-macro-full-parallel
run-macro-full-parallel:
	@echo "================================================================================"
	@echo "Running STREAM Macro Tests - FULL level PARALLEL (48 workers)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(MACRO_TESTS_DIR)/test_*.py

# ==============================================================================
# Run Targets - All Tests
# ==============================================================================

.PHONY: run-all
run-all:
	@echo "================================================================================"
	@echo "Running ALL STREAM Tests (FUB + Macro, default FUNC level)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_*.py $(MACRO_TESTS_DIR)/test_*.py

.PHONY: run-all-parallel
run-all-parallel:
	@echo "================================================================================"
	@echo "Running ALL STREAM Tests (Parallel - 48 workers)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(FUB_TESTS_DIR)/test_*.py $(MACRO_TESTS_DIR)/test_*.py

# REG_LEVEL Variants - Run all tests with specific regression levels
.PHONY: run-all-gate
run-all-gate:
	@echo "================================================================================"
	@echo "Running ALL STREAM Tests - GATE level (minimal params)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_*.py $(MACRO_TESTS_DIR)/test_*.py

.PHONY: run-all-func
run-all-func:
	@echo "================================================================================"
	@echo "Running ALL STREAM Tests - FUNC level (default params)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_*.py $(MACRO_TESTS_DIR)/test_*.py

.PHONY: run-all-full
run-all-full:
	@echo "================================================================================"
	@echo "Running ALL STREAM Tests - FULL level (comprehensive)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_*.py $(MACRO_TESTS_DIR)/test_*.py

.PHONY: run-all-gate-parallel
run-all-gate-parallel:
	@echo "================================================================================"
	@echo "Running ALL STREAM Tests - GATE level PARALLEL (48 workers)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(FUB_TESTS_DIR)/test_*.py $(MACRO_TESTS_DIR)/test_*.py

.PHONY: run-all-func-parallel
run-all-func-parallel:
	@echo "================================================================================"
	@echo "Running ALL STREAM Tests - FUNC level PARALLEL (48 workers)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(FUB_TESTS_DIR)/test_*.py $(MACRO_TESTS_DIR)/test_*.py

.PHONY: run-all-full-parallel
run-all-full-parallel:
	@echo "================================================================================"
	@echo "Running ALL STREAM Tests - FULL level PARALLEL (48 workers)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) $(FUB_TESTS_DIR)/test_*.py $(MACRO_TESTS_DIR)/test_*.py

# ==============================================================================
# Development Targets - pytest-watch for auto-rerunning tests
# ==============================================================================

.PHONY: ptw-fub
ptw-fub:
	@echo "================================================================================"
	@echo "Starting pytest-watch for STREAM FUB tests"
	@echo "Tests will auto-rerun when files change. Press Ctrl+C to stop."
	@echo "================================================================================"
	@cd $(FUB_TESTS_DIR) && $(MAKE) ptw

.PHONY: ptw-macro
ptw-macro:
	@echo "================================================================================"
	@echo "Starting pytest-watch for STREAM macro tests"
	@echo "Tests will auto-rerun when files change. Press Ctrl+C to stop."
	@echo "================================================================================"
	@cd $(MACRO_TESTS_DIR) && $(MAKE) ptw

# ==============================================================================
# Run Targets - Individual Test Modules (flattened structure)
# ==============================================================================

.PHONY: run-perf
run-perf:
	@echo "Running perf_profiler tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_perf_profiler.py

.PHONY: run-scheduler
run-scheduler:
	@echo "Running scheduler tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_scheduler.py

.PHONY: run-sram
run-sram:
	@echo "Running simple_sram tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_simple_sram.py

.PHONY: run-axi-rd
run-axi-rd:
	@echo "Running axi_read_engine tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_axi_read_engine.py

.PHONY: run-axi-wr
run-axi-wr:
	@echo "Running axi_write_engine tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_axi_write_engine.py

.PHONY: run-sram-ctrl
run-sram-ctrl:
	@echo "Running sram_controller tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_sram_controller.py

.PHONY: run-desc-engine
run-desc-engine:
	@echo "Running descriptor_engine tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_descriptor_engine.py

.PHONY: run-apbtodescr
run-apbtodescr:
	@echo "Running apbtodescr tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(FUB_TESTS_DIR)/test_apbtodescr.py

.PHONY: run-monbus
run-monbus:
	@echo "Running monbus_axil_group tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(MACRO_TESTS_DIR)/test_monbus_axil_group.py

# ==============================================================================
# Collection Targets (verify tests without running)
# ==============================================================================

.PHONY: collect-fub
collect-fub:
	@echo "Collecting STREAM FUB tests (verifying imports)..."
	$(PYTEST) --collect-only $(FUB_TESTS_DIR)/test_*.py

.PHONY: collect-macro
collect-macro:
	@echo "Collecting STREAM macro tests..."
	$(PYTEST) --collect-only $(MACRO_TESTS_DIR)/test_*.py

.PHONY: collect-all
collect-all:
	@echo "Collecting ALL STREAM tests..."
	$(PYTEST) --collect-only $(FUB_TESTS_DIR)/test_*.py $(MACRO_TESTS_DIR)/test_*.py

# ==============================================================================
# Clean Targets
# ==============================================================================

.PHONY: clean-fub
clean-fub:
	@echo "Cleaning FUB test artifacts..."
	rm -rf $(FUB_TESTS_DIR)/local_sim_build
	rm -rf $(FUB_TESTS_DIR)/sim_build
	find $(FUB_TESTS_DIR) -type f -name "*.log" -delete
	find $(FUB_TESTS_DIR) -type f -name "*.vcd" -delete
	find $(FUB_TESTS_DIR) -type f -name "dump.vcd" -delete
	@echo "✓ FUB test artifacts cleaned"

.PHONY: clean-macro
clean-macro:
	@echo "Cleaning macro test artifacts..."
	rm -rf $(MACRO_TESTS_DIR)/local_sim_build
	rm -rf $(MACRO_TESTS_DIR)/sim_build
	find $(MACRO_TESTS_DIR) -type f -name "*.log" -delete
	find $(MACRO_TESTS_DIR) -type f -name "*.vcd" -delete
	find $(MACRO_TESTS_DIR) -type f -name "dump.vcd" -delete
	@echo "✓ Macro test artifacts cleaned"

.PHONY: clean-logs
clean-logs:
	@echo "Cleaning all log files..."
	find . -type f -name "*.log" -delete
	find . -type d -name "logs" -exec rm -rf {} + 2>/dev/null || true
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
clean-all: clean-fub clean-macro clean-logs clean-pycache clean-build clean-vcd
	@echo "================================================================================"
	@echo "✓ All STREAM test artifacts cleaned"
	@echo "================================================================================"

# ==============================================================================
# Utility Targets
# ==============================================================================

.PHONY: list-fub
list-fub:
	@echo "STREAM FUB Test Modules:"
	@find $(FUB_TESTS_DIR) -name "test_*.py" -type f | sort

.PHONY: list-macro
list-macro:
	@echo "STREAM Macro Test Modules:"
	@find $(MACRO_TESTS_DIR) -name "test_*.py" -type f | sort

.PHONY: status
status:
	@echo "================================================================================"
	@echo "STREAM Test Status"
	@echo "================================================================================"
	@echo "Test directories:"
	@echo "  FUB tests:   $(FUB_TESTS_DIR)/ (flattened structure)"
	@echo "  Macro tests: $(MACRO_TESTS_DIR)/"
	@echo ""
	@echo "Test modules found:"
	@echo -n "  FUB:   "
	@find $(FUB_TESTS_DIR) -name "test_*.py" -type f | wc -l
	@echo -n "  Macro: "
	@find $(MACRO_TESTS_DIR) -name "test_*.py" -type f | wc -l
	@echo ""
	@echo "Build artifacts:"
	@echo -n "  local_sim_build dirs: "
	@find . -type d -name "local_sim_build" | wc -l
	@echo -n "  Log files:            "
	@find . -type f -name "*.log" | wc -l
	@echo -n "  VCD files:            "
	@find . -type f -name "*.vcd" | wc -l
	@echo ""
	@echo "Python environment:"
	@echo "  REPO_ROOT: $(REPO_ROOT)"
	@echo "  Virtual env: $(REPO_ROOT)/env_python"
	@echo "================================================================================"

# ==============================================================================
# Combined Targets (clean + run)
# ==============================================================================

.PHONY: fresh-fub
fresh-fub: clean-fub run-fub
	@echo "✓ Fresh FUB test run complete"

.PHONY: fresh-macro
fresh-macro: clean-macro run-macro
	@echo "✓ Fresh macro test run complete"

.PHONY: fresh-all
fresh-all: clean-all run-all
	@echo "✓ Fresh all tests run complete"

# ==============================================================================
# Quick Aliases
# ==============================================================================

.PHONY: fub
fub: run-fub

.PHONY: macro
macro: run-macro

.PHONY: all
all: run-all

.PHONY: clean
clean: clean-all

.PHONY: collect
collect: collect-all

.PHONY: list
list: list-fub list-macro

# ==============================================================================
# End of Makefile
# ==============================================================================
