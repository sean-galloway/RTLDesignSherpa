# ==============================================================================
# RAPIDS Subsystem Test Makefile
# ==============================================================================
#
# PREREQUISITES:
#   Must be run with sourced environment:
#     source $REPO_ROOT/env_python  # Sets $REPO_ROOT and activates venv
#     cd $REPO_ROOT/projects/components/rapids/dv/tests
#     make <target>
#
# Test Directory Structure:
#   fub/           - Legacy network-based FUB modules (ctrlwr_engine, ctrlrd_engine)
#   fub_beats/     - AXIS-based FUB modules (scheduler, descriptor_engine, etc.)
#   macro/         - Macro-level integration tests
#   macro_beats/   - Macro-beats integration tests
#
# Quick start:
#   make help           - Show all available targets
#   make run-fub        - Run legacy FUB tests
#   make run-fub-beats  - Run AXIS-based FUB tests
#   make run-macro      - Run macro tests
#   make run-all        - Run all tests
#   make clean-all      - Clean all test artifacts
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

# Test directories (reorganized structure)
# Legacy network-based FUB modules (ctrlwr_engine, ctrlrd_engine)
FUB_DIR = fub
# AXIS-based FUB modules (scheduler, descriptor_engine, etc.)
FUB_BEATS_DIR = fub_beats
# Macro-level integration tests
MACRO_DIR = macro
# Macro-beats integration tests
MACRO_BEATS_DIR = macro_beats

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
	@echo "RAPIDS Test Makefile - Available Targets"
	@echo "================================================================================"
	@echo ""
	@echo "Test Directory Structure:"
	@echo "  fub/           Legacy network-based FUB (ctrlwr_engine, ctrlrd_engine)"
	@echo "  fub_beats/     AXIS-based FUB (scheduler, descriptor_engine, etc.)"
	@echo "  macro/         Macro-level integration tests"
	@echo "  macro_beats/   Macro-beats integration tests"
	@echo ""
	@echo "RUN TARGETS (by Test Type):"
	@echo "  make run-fub              Run legacy FUB tests (calls fub/Makefile)"
	@echo "  make run-fub-beats        Run AXIS-based FUB tests (calls fub_beats/Makefile)"
	@echo "  make run-macro            Run macro tests (calls macro/Makefile)"
	@echo "  make run-macro-beats      Run macro-beats tests (calls macro_beats/Makefile)"
	@echo "  make run-all              Run all tests"
	@echo ""
	@echo "PARALLEL TARGETS:"
	@echo "  make run-fub-parallel         Run legacy FUB tests in parallel"
	@echo "  make run-fub-beats-parallel   Run AXIS FUB tests in parallel"
	@echo "  make run-macro-parallel       Run macro tests in parallel"
	@echo "  make run-macro-beats-parallel Run macro-beats tests in parallel"
	@echo "  make run-all-parallel         Run all tests in parallel"
	@echo ""
	@echo "REG_LEVEL TARGETS (configurable test depth):"
	@echo "  GATE = Quick smoke tests, FUNC = Default, FULL = Comprehensive"
	@echo ""
	@echo "  Legacy FUB Tests:"
	@echo "    make run-fub-{gate|func|full}[-parallel]"
	@echo "  AXIS FUB Tests:"
	@echo "    make run-fub-beats-{gate|func|full}[-parallel]"
	@echo "  Macro Tests:"
	@echo "    make run-macro-{gate|func|full}[-parallel]"
	@echo "  Macro-Beats Tests:"
	@echo "    make run-macro-beats-{gate|func|full}[-parallel]"
	@echo ""
	@echo "DEVELOPMENT TARGETS (pytest-watch):"
	@echo "  make ptw-fub              Auto-rerun legacy FUB tests on file changes"
	@echo "  make ptw-fub-beats        Auto-rerun AXIS FUB tests on file changes"
	@echo "  make ptw-macro            Auto-rerun macro tests on file changes"
	@echo "  make ptw-macro-beats      Auto-rerun macro-beats tests on file changes"
	@echo ""
	@echo "COLLECTION TARGETS (verify tests, don't run):"
	@echo "  make collect-fub          Collect legacy FUB tests (verify imports)"
	@echo "  make collect-fub-beats    Collect AXIS FUB tests"
	@echo "  make collect-macro        Collect macro tests"
	@echo "  make collect-macro-beats  Collect macro-beats tests"
	@echo "  make collect-all          Collect all tests"
	@echo ""
	@echo "CLEAN TARGETS:"
	@echo "  make clean-fub            Remove legacy FUB test artifacts"
	@echo "  make clean-fub-beats      Remove AXIS FUB test artifacts"
	@echo "  make clean-macro          Remove macro test artifacts"
	@echo "  make clean-macro-beats    Remove macro-beats test artifacts"
	@echo "  make clean-all            Remove all test artifacts"
	@echo ""
	@echo "UTILITY TARGETS:"
	@echo "  make list-fub             List legacy FUB test modules"
	@echo "  make list-fub-beats       List AXIS FUB test modules"
	@echo "  make list-macro           List macro test modules"
	@echo "  make list-macro-beats     List macro-beats test modules"
	@echo "  make list-all             List all test modules"
	@echo "  make status               Show test status and coverage"
	@echo ""
	@echo "================================================================================"
	@echo "Prerequisites: source $(REPO_ROOT)/env_python"
	@echo "Current REPO_ROOT: $(REPO_ROOT)"
	@echo "================================================================================"

# ==============================================================================
# Run Targets - Legacy FUB Tests (ctrlwr_engine, ctrlrd_engine)
# ==============================================================================

.PHONY: run-fub
run-fub:
	@echo "================================================================================"
	@echo "Running RAPIDS Legacy FUB Tests"
	@echo "================================================================================"
	@cd $(FUB_DIR) && $(MAKE) run

.PHONY: run-fub-parallel
run-fub-parallel:
	@echo "================================================================================"
	@echo "Running RAPIDS Legacy FUB Tests (Parallel)"
	@echo "================================================================================"
	@cd $(FUB_DIR) && $(MAKE) run-parallel

.PHONY: run-fub-waves
run-fub-waves:
	@echo "================================================================================"
	@echo "Running RAPIDS Legacy FUB Tests (with waveforms)"
	@echo "================================================================================"
	@cd $(FUB_DIR) && $(MAKE) run-waves

# REG_LEVEL Control for Legacy FUB Tests
.PHONY: run-fub-gate
run-fub-gate:
	@cd $(FUB_DIR) && $(MAKE) run-gate

.PHONY: run-fub-func
run-fub-func:
	@cd $(FUB_DIR) && $(MAKE) run-func

.PHONY: run-fub-full
run-fub-full:
	@cd $(FUB_DIR) && $(MAKE) run-full

.PHONY: run-fub-gate-parallel
run-fub-gate-parallel:
	@cd $(FUB_DIR) && $(MAKE) run-parallel

.PHONY: run-fub-func-parallel
run-fub-func-parallel:
	@cd $(FUB_DIR) && REG_LEVEL=FUNC $(MAKE) run-parallel

.PHONY: run-fub-full-parallel
run-fub-full-parallel:
	@cd $(FUB_DIR) && REG_LEVEL=FULL $(MAKE) run-parallel

# ==============================================================================
# Run Targets - AXIS-based FUB Tests (scheduler, descriptor_engine, etc.)
# ==============================================================================

.PHONY: run-fub-beats
run-fub-beats:
	@echo "================================================================================"
	@echo "Running RAPIDS AXIS FUB Tests"
	@echo "================================================================================"
	@cd $(FUB_BEATS_DIR) && $(MAKE) run

.PHONY: run-fub-beats-parallel
run-fub-beats-parallel:
	@echo "================================================================================"
	@echo "Running RAPIDS AXIS FUB Tests (Parallel)"
	@echo "================================================================================"
	@cd $(FUB_BEATS_DIR) && $(MAKE) run-parallel

.PHONY: run-fub-beats-waves
run-fub-beats-waves:
	@echo "================================================================================"
	@echo "Running RAPIDS AXIS FUB Tests (with waveforms)"
	@echo "================================================================================"
	@cd $(FUB_BEATS_DIR) && $(MAKE) run-waves

# REG_LEVEL Control for AXIS FUB Tests
.PHONY: run-fub-beats-gate
run-fub-beats-gate:
	@cd $(FUB_BEATS_DIR) && $(MAKE) run-gate

.PHONY: run-fub-beats-func
run-fub-beats-func:
	@cd $(FUB_BEATS_DIR) && $(MAKE) run-func

.PHONY: run-fub-beats-full
run-fub-beats-full:
	@cd $(FUB_BEATS_DIR) && $(MAKE) run-full

.PHONY: run-fub-beats-gate-parallel
run-fub-beats-gate-parallel:
	@cd $(FUB_BEATS_DIR) && $(MAKE) run-parallel

.PHONY: run-fub-beats-func-parallel
run-fub-beats-func-parallel:
	@cd $(FUB_BEATS_DIR) && REG_LEVEL=FUNC $(MAKE) run-parallel

.PHONY: run-fub-beats-full-parallel
run-fub-beats-full-parallel:
	@cd $(FUB_BEATS_DIR) && REG_LEVEL=FULL $(MAKE) run-parallel

# ==============================================================================
# Run Targets - Macro Tests
# ==============================================================================

.PHONY: run-macro
run-macro:
	@echo "================================================================================"
	@echo "Running RAPIDS Macro Tests"
	@echo "================================================================================"
	@cd $(MACRO_DIR) && $(MAKE) run

.PHONY: run-macro-parallel
run-macro-parallel:
	@echo "================================================================================"
	@echo "Running RAPIDS Macro Tests (Parallel)"
	@echo "================================================================================"
	@cd $(MACRO_DIR) && $(MAKE) run-parallel

.PHONY: run-macro-waves
run-macro-waves:
	@echo "================================================================================"
	@echo "Running RAPIDS Macro Tests (with waveforms)"
	@echo "================================================================================"
	@cd $(MACRO_DIR) && $(MAKE) run-waves

# REG_LEVEL Control for Macro Tests
.PHONY: run-macro-gate
run-macro-gate:
	@cd $(MACRO_DIR) && $(MAKE) run-gate

.PHONY: run-macro-func
run-macro-func:
	@cd $(MACRO_DIR) && $(MAKE) run-func

.PHONY: run-macro-full
run-macro-full:
	@cd $(MACRO_DIR) && $(MAKE) run-full

.PHONY: run-macro-gate-parallel
run-macro-gate-parallel:
	@cd $(MACRO_DIR) && $(MAKE) run-parallel

.PHONY: run-macro-func-parallel
run-macro-func-parallel:
	@cd $(MACRO_DIR) && REG_LEVEL=FUNC $(MAKE) run-parallel

.PHONY: run-macro-full-parallel
run-macro-full-parallel:
	@cd $(MACRO_DIR) && REG_LEVEL=FULL $(MAKE) run-parallel

# ==============================================================================
# Run Targets - Macro-Beats Tests
# ==============================================================================

.PHONY: run-macro-beats
run-macro-beats:
	@echo "================================================================================"
	@echo "Running RAPIDS Macro-Beats Tests"
	@echo "================================================================================"
	@cd $(MACRO_BEATS_DIR) && $(MAKE) run

.PHONY: run-macro-beats-parallel
run-macro-beats-parallel:
	@echo "================================================================================"
	@echo "Running RAPIDS Macro-Beats Tests (Parallel)"
	@echo "================================================================================"
	@cd $(MACRO_BEATS_DIR) && $(MAKE) run-parallel

.PHONY: run-macro-beats-waves
run-macro-beats-waves:
	@echo "================================================================================"
	@echo "Running RAPIDS Macro-Beats Tests (with waveforms)"
	@echo "================================================================================"
	@cd $(MACRO_BEATS_DIR) && $(MAKE) run-waves

# REG_LEVEL Control for Macro-Beats Tests
.PHONY: run-macro-beats-gate
run-macro-beats-gate:
	@cd $(MACRO_BEATS_DIR) && $(MAKE) run-gate

.PHONY: run-macro-beats-func
run-macro-beats-func:
	@cd $(MACRO_BEATS_DIR) && $(MAKE) run-func

.PHONY: run-macro-beats-full
run-macro-beats-full:
	@cd $(MACRO_BEATS_DIR) && $(MAKE) run-full

.PHONY: run-macro-beats-gate-parallel
run-macro-beats-gate-parallel:
	@cd $(MACRO_BEATS_DIR) && $(MAKE) run-parallel

.PHONY: run-macro-beats-func-parallel
run-macro-beats-func-parallel:
	@cd $(MACRO_BEATS_DIR) && REG_LEVEL=FUNC $(MAKE) run-parallel

.PHONY: run-macro-beats-full-parallel
run-macro-beats-full-parallel:
	@cd $(MACRO_BEATS_DIR) && REG_LEVEL=FULL $(MAKE) run-parallel

# ==============================================================================
# Run Targets - All Tests
# ==============================================================================

.PHONY: run-all
run-all: run-fub run-fub-beats run-macro run-macro-beats
	@echo "================================================================================"
	@echo "All RAPIDS Tests Complete"
	@echo "================================================================================"

.PHONY: run-all-parallel
run-all-parallel: run-fub-parallel run-fub-beats-parallel run-macro-parallel run-macro-beats-parallel
	@echo "================================================================================"
	@echo "All RAPIDS Tests Complete (Parallel)"
	@echo "================================================================================"

.PHONY: run-all-gate
run-all-gate: run-fub-gate run-fub-beats-gate run-macro-gate run-macro-beats-gate
	@echo "All RAPIDS Tests Complete - GATE level"

.PHONY: run-all-func
run-all-func: run-fub-func run-fub-beats-func run-macro-func run-macro-beats-func
	@echo "All RAPIDS Tests Complete - FUNC level"

.PHONY: run-all-full
run-all-full: run-fub-full run-fub-beats-full run-macro-full run-macro-beats-full
	@echo "All RAPIDS Tests Complete - FULL level"

.PHONY: run-all-gate-parallel
run-all-gate-parallel: run-fub-gate-parallel run-fub-beats-gate-parallel run-macro-gate-parallel run-macro-beats-gate-parallel
	@echo "All RAPIDS Tests Complete - GATE level (Parallel)"

.PHONY: run-all-func-parallel
run-all-func-parallel: run-fub-func-parallel run-fub-beats-func-parallel run-macro-func-parallel run-macro-beats-func-parallel
	@echo "All RAPIDS Tests Complete - FUNC level (Parallel)"

.PHONY: run-all-full-parallel
run-all-full-parallel: run-fub-full-parallel run-fub-beats-full-parallel run-macro-full-parallel run-macro-beats-full-parallel
	@echo "All RAPIDS Tests Complete - FULL level (Parallel)"

# ==============================================================================
# Development Targets (pytest-watch) - Delegate to sub-Makefiles
# ==============================================================================

.PHONY: ptw-fub
ptw-fub:
	@echo "================================================================================"
	@echo "Starting pytest-watch for RAPIDS Legacy FUB tests"
	@echo "Tests will auto-rerun when files change. Press Ctrl+C to stop."
	@echo "================================================================================"
	@cd $(FUB_DIR) && $(MAKE) ptw

.PHONY: ptw-fub-beats
ptw-fub-beats:
	@echo "================================================================================"
	@echo "Starting pytest-watch for RAPIDS AXIS FUB tests"
	@echo "Tests will auto-rerun when files change. Press Ctrl+C to stop."
	@echo "================================================================================"
	@cd $(FUB_BEATS_DIR) && $(MAKE) ptw

.PHONY: ptw-macro
ptw-macro:
	@echo "================================================================================"
	@echo "Starting pytest-watch for RAPIDS macro tests"
	@echo "Tests will auto-rerun when files change. Press Ctrl+C to stop."
	@echo "================================================================================"
	@cd $(MACRO_DIR) && $(MAKE) ptw

.PHONY: ptw-macro-beats
ptw-macro-beats:
	@echo "================================================================================"
	@echo "Starting pytest-watch for RAPIDS macro-beats tests"
	@echo "Tests will auto-rerun when files change. Press Ctrl+C to stop."
	@echo "================================================================================"
	@cd $(MACRO_BEATS_DIR) && $(MAKE) ptw

# ==============================================================================
# Collection Targets (verify tests without running) - Delegate to sub-Makefiles
# ==============================================================================

.PHONY: collect-fub
collect-fub:
	@echo "Collecting RAPIDS Legacy FUB tests..."
	@cd $(FUB_DIR) && $(MAKE) collect

.PHONY: collect-fub-beats
collect-fub-beats:
	@echo "Collecting RAPIDS AXIS FUB tests..."
	@cd $(FUB_BEATS_DIR) && $(MAKE) collect

.PHONY: collect-macro
collect-macro:
	@echo "Collecting RAPIDS macro tests..."
	@cd $(MACRO_DIR) && $(MAKE) collect

.PHONY: collect-macro-beats
collect-macro-beats:
	@echo "Collecting RAPIDS macro-beats tests..."
	@cd $(MACRO_BEATS_DIR) && $(MAKE) collect

.PHONY: collect-all
collect-all: collect-fub collect-fub-beats collect-macro collect-macro-beats
	@echo "All RAPIDS tests collected"

# ==============================================================================
# Clean Targets - Delegate to sub-Makefiles
# ==============================================================================

.PHONY: clean-fub
clean-fub:
	@echo "Cleaning Legacy FUB test artifacts..."
	@cd $(FUB_DIR) && $(MAKE) clean-all

.PHONY: clean-fub-beats
clean-fub-beats:
	@echo "Cleaning AXIS FUB test artifacts..."
	@cd $(FUB_BEATS_DIR) && $(MAKE) clean-all

.PHONY: clean-macro
clean-macro:
	@echo "Cleaning macro test artifacts..."
	@cd $(MACRO_DIR) && $(MAKE) clean-all

.PHONY: clean-macro-beats
clean-macro-beats:
	@echo "Cleaning macro-beats test artifacts..."
	@cd $(MACRO_BEATS_DIR) && $(MAKE) clean-all

.PHONY: clean-logs
clean-logs:
	@echo "Cleaning all log files..."
	find . -type f -name "*.log" -delete
	find . -type d -name "logs" -exec rm -rf {} + 2>/dev/null || true
	@echo "Log files cleaned"

.PHONY: clean-pycache
clean-pycache:
	@echo "Cleaning Python cache files..."
	find . -type d -name "__pycache__" -exec rm -rf {} + 2>/dev/null || true
	find . -type f -name "*.pyc" -delete
	@echo "Python cache cleaned"

.PHONY: clean-build
clean-build:
	@echo "Cleaning simulation build directories..."
	find . -type d -name "local_sim_build" -exec rm -rf {} + 2>/dev/null || true
	find . -type d -name "sim_build" -exec rm -rf {} + 2>/dev/null || true
	@echo "Build directories cleaned"

.PHONY: clean-vcd
clean-vcd:
	@echo "Cleaning VCD waveform files..."
	find . -type f -name "*.vcd" -delete
	find . -type f -name "*.fst" -delete
	@echo "Waveform files cleaned"

.PHONY: clean-all
clean-all: clean-fub clean-fub-beats clean-macro clean-macro-beats clean-logs clean-pycache clean-build clean-vcd
	@echo "================================================================================"
	@echo "All RAPIDS test artifacts cleaned"
	@echo "================================================================================"

# ==============================================================================
# Utility Targets - List test modules
# ==============================================================================

.PHONY: list-fub
list-fub:
	@echo "RAPIDS Legacy FUB Test Modules:"
	@find $(FUB_DIR) -name "test_*.py" -type f 2>/dev/null | sort || echo "  (no tests found)"

.PHONY: list-fub-beats
list-fub-beats:
	@echo "RAPIDS AXIS FUB Test Modules:"
	@find $(FUB_BEATS_DIR) -name "test_*.py" -type f 2>/dev/null | sort || echo "  (no tests found)"

.PHONY: list-macro
list-macro:
	@echo "RAPIDS Macro Test Modules:"
	@find $(MACRO_DIR) -name "test_*.py" -type f 2>/dev/null | sort || echo "  (no tests found)"

.PHONY: list-macro-beats
list-macro-beats:
	@echo "RAPIDS Macro-Beats Test Modules:"
	@find $(MACRO_BEATS_DIR) -name "test_*.py" -type f 2>/dev/null | sort || echo "  (no tests found)"

.PHONY: list-all
list-all: list-fub list-fub-beats list-macro list-macro-beats

.PHONY: status
status:
	@echo "================================================================================"
	@echo "RAPIDS Test Status"
	@echo "================================================================================"
	@echo "Test directories:"
	@echo "  Legacy FUB:    $(FUB_DIR)/ (ctrlwr_engine, ctrlrd_engine)"
	@echo "  AXIS FUB:      $(FUB_BEATS_DIR)/ (scheduler, descriptor_engine, etc.)"
	@echo "  Macro:         $(MACRO_DIR)/"
	@echo "  Macro-Beats:   $(MACRO_BEATS_DIR)/"
	@echo ""
	@echo "Test modules found:"
	@echo -n "  Legacy FUB:   "
	@find $(FUB_DIR) -name "test_*.py" -type f 2>/dev/null | wc -l || echo "0"
	@echo -n "  AXIS FUB:     "
	@find $(FUB_BEATS_DIR) -name "test_*.py" -type f 2>/dev/null | wc -l || echo "0"
	@echo -n "  Macro:        "
	@find $(MACRO_DIR) -name "test_*.py" -type f 2>/dev/null | wc -l || echo "0"
	@echo -n "  Macro-Beats:  "
	@find $(MACRO_BEATS_DIR) -name "test_*.py" -type f 2>/dev/null | wc -l || echo "0"
	@echo ""
	@echo "Build artifacts:"
	@echo -n "  local_sim_build dirs: "
	@find . -type d -name "local_sim_build" 2>/dev/null | wc -l || echo "0"
	@echo -n "  Log files:            "
	@find . -type f -name "*.log" 2>/dev/null | wc -l || echo "0"
	@echo -n "  VCD/FST files:        "
	@find . -type f \( -name "*.vcd" -o -name "*.fst" \) 2>/dev/null | wc -l || echo "0"
	@echo ""
	@echo "Python environment:"
	@echo "  REPO_ROOT: $(REPO_ROOT)"
	@echo "  Virtual env: $(REPO_ROOT)/env_python"
	@echo "================================================================================"

# ==============================================================================
# Coverage Targets
# ==============================================================================

# Coverage environment variables
COVERAGE_ENV = SIM=verilator WAVES=0 COVERAGE=1 COVERAGE_LEGAL=1

# Coverage reports directory
COVERAGE_REPORTS_DIR = coverage_reports

.PHONY: coverage-fub-beats
coverage-fub-beats:
	@echo "================================================================================"
	@echo "Running RAPIDS FUB-Beats Tests with Coverage"
	@echo "================================================================================"
	@cd $(FUB_BEATS_DIR) && \
	PYTHONPATH=$(REPO_ROOT)/bin:$(REPO_ROOT):$$PYTHONPATH \
	$(COVERAGE_ENV) \
	TEST_LEVEL=func \
	timeout 900 $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: coverage-macro-beats
coverage-macro-beats:
	@echo "================================================================================"
	@echo "Running RAPIDS Macro-Beats Tests with Coverage"
	@echo "================================================================================"
	@cd $(MACRO_BEATS_DIR) && \
	PYTHONPATH=$(REPO_ROOT)/bin:$(REPO_ROOT):$$PYTHONPATH \
	$(COVERAGE_ENV) \
	TEST_LEVEL=func \
	timeout 900 $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: coverage-beats
coverage-beats: coverage-fub-beats coverage-macro-beats
	@echo "================================================================================"
	@echo "All RAPIDS Beats Coverage Runs Complete"
	@echo "================================================================================"

.PHONY: coverage-fub-beats-gate
coverage-fub-beats-gate:
	@cd $(FUB_BEATS_DIR) && \
	PYTHONPATH=$(REPO_ROOT)/bin:$(REPO_ROOT):$$PYTHONPATH \
	$(COVERAGE_ENV) \
	TEST_LEVEL=gate \
	timeout 600 $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: coverage-fub-beats-func
coverage-fub-beats-func:
	@cd $(FUB_BEATS_DIR) && \
	PYTHONPATH=$(REPO_ROOT)/bin:$(REPO_ROOT):$$PYTHONPATH \
	$(COVERAGE_ENV) \
	TEST_LEVEL=func \
	timeout 900 $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: coverage-fub-beats-full
coverage-fub-beats-full:
	@cd $(FUB_BEATS_DIR) && \
	PYTHONPATH=$(REPO_ROOT)/bin:$(REPO_ROOT):$$PYTHONPATH \
	$(COVERAGE_ENV) \
	TEST_LEVEL=full \
	timeout 1800 $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: coverage-macro-beats-gate
coverage-macro-beats-gate:
	@cd $(MACRO_BEATS_DIR) && \
	PYTHONPATH=$(REPO_ROOT)/bin:$(REPO_ROOT):$$PYTHONPATH \
	$(COVERAGE_ENV) \
	TEST_LEVEL=gate \
	timeout 600 $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: coverage-macro-beats-func
coverage-macro-beats-func:
	@cd $(MACRO_BEATS_DIR) && \
	PYTHONPATH=$(REPO_ROOT)/bin:$(REPO_ROOT):$$PYTHONPATH \
	$(COVERAGE_ENV) \
	TEST_LEVEL=func \
	timeout 900 $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: coverage-macro-beats-full
coverage-macro-beats-full:
	@cd $(MACRO_BEATS_DIR) && \
	PYTHONPATH=$(REPO_ROOT)/bin:$(REPO_ROOT):$$PYTHONPATH \
	$(COVERAGE_ENV) \
	TEST_LEVEL=full \
	timeout 1800 $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: coverage-beats-gate
coverage-beats-gate: coverage-fub-beats-gate coverage-macro-beats-gate
	@echo "All RAPIDS Beats Coverage Complete - GATE level"

.PHONY: coverage-beats-func
coverage-beats-func: coverage-fub-beats-func coverage-macro-beats-func
	@echo "All RAPIDS Beats Coverage Complete - FUNC level"

.PHONY: coverage-beats-full
coverage-beats-full: coverage-fub-beats-full coverage-macro-beats-full
	@echo "All RAPIDS Beats Coverage Complete - FULL level"

.PHONY: coverage-report
coverage-report:
	@echo "================================================================================"
	@echo "Generating RAPIDS Combined Coverage Report"
	@echo "================================================================================"
	@mkdir -p $(COVERAGE_REPORTS_DIR)
	@python3 -c " \
import os, json, glob; \
from datetime import datetime; \
\
levels = [('fub_beats', 'FUB-Beats'), ('macro_beats', 'Macro-Beats')]; \
combined = {'levels': {}, 'totals': {'protocol': 0, 'line': 0, 'count': 0}}; \
\
for level_dir, level_name in levels: \
    json_path = f'{level_dir}/coverage_data/merged/latest_merged_coverage.json'; \
    if os.path.exists(json_path): \
        with open(json_path) as f: \
            data = json.load(f); \
            combined['levels'][level_name] = data; \
            for r in data.get('tests', []): \
                combined['totals']['protocol'] += r.get('protocol_pct', 0); \
                combined['totals']['line'] += r.get('line_pct', 0); \
                combined['totals']['count'] += 1; \
\
if combined['totals']['count'] > 0: \
    avg_protocol = combined['totals']['protocol'] / combined['totals']['count']; \
    avg_line = combined['totals']['line'] / combined['totals']['count']; \
else: \
    avg_protocol = avg_line = 0; \
\
lines = ['# RAPIDS Beats Coverage Report', '', f'Generated: {datetime.now()}', '']; \
lines.append('## Overall Summary'); \
lines.append(f'- **Average Protocol Coverage:** {avg_protocol:.1f}%'); \
lines.append(f'- **Average Line Coverage:** {avg_line:.1f}%'); \
lines.append(f'- **Total Tests:** {combined[\"totals\"][\"count\"]}'); \
lines.append(''); \
\
for level_name in [l[1] for l in levels]: \
    if level_name in combined['levels']: \
        data = combined['levels'][level_name]; \
        test_count = len(data.get('tests', [])); \
        lines.append(f'## {level_name} Level ({test_count} tests)'); \
        lines.append('| Test | Protocol % | Line % |'); \
        lines.append('|------|------------|--------|'); \
        for r in data.get('tests', []): \
            lines.append(f'| {r[\"name\"]} | {r[\"protocol_pct\"]:.1f}% | {r[\"line_pct\"]:.1f}% |'); \
        lines.append(''); \
\
with open('$(COVERAGE_REPORTS_DIR)/combined_coverage_report.md', 'w') as f: \
    f.write('\n'.join(lines)); \
print('Report written to: $(COVERAGE_REPORTS_DIR)/combined_coverage_report.md'); \
"

.PHONY: coverage-full-report
coverage-full-report: clean-coverage coverage-beats-func coverage-report
	@echo "================================================================================"
	@echo "RAPIDS Full Coverage Report Complete"
	@echo "================================================================================"

.PHONY: clean-coverage
clean-coverage:
	@echo "Cleaning RAPIDS coverage data..."
	rm -rf $(FUB_BEATS_DIR)/coverage_data
	rm -rf $(MACRO_BEATS_DIR)/coverage_data
	rm -rf $(COVERAGE_REPORTS_DIR)
	@echo "Coverage data cleaned"

.PHONY: coverage-status
coverage-status:
	@echo "================================================================================"
	@echo "RAPIDS Coverage Data Status"
	@echo "================================================================================"
	@for level in fub_beats macro_beats; do \
		echo ""; \
		echo "$$level level:"; \
		if [ -d "$$level/coverage_data/per_test" ]; then \
			count=$$(ls -1 $$level/coverage_data/per_test/*_summary.json 2>/dev/null | wc -l); \
			echo "  - $$count test coverage files"; \
		else \
			echo "  - No coverage data"; \
		fi; \
	done

# ==============================================================================
# Combined Targets (clean + run)
# ==============================================================================

.PHONY: fresh-fub
fresh-fub: clean-fub run-fub
	@echo "Fresh Legacy FUB test run complete"

.PHONY: fresh-fub-beats
fresh-fub-beats: clean-fub-beats run-fub-beats
	@echo "Fresh AXIS FUB test run complete"

.PHONY: fresh-macro
fresh-macro: clean-macro run-macro
	@echo "Fresh macro test run complete"

.PHONY: fresh-macro-beats
fresh-macro-beats: clean-macro-beats run-macro-beats
	@echo "Fresh macro-beats test run complete"

.PHONY: fresh-all
fresh-all: clean-all run-all
	@echo "Fresh all tests run complete"

# ==============================================================================
# Quick Aliases
# ==============================================================================

.PHONY: fub
fub: run-fub

.PHONY: fub-beats
fub-beats: run-fub-beats

.PHONY: macro
macro: run-macro

.PHONY: macro-beats
macro-beats: run-macro-beats

.PHONY: all
all: run-all

.PHONY: clean
clean: clean-all

.PHONY: collect
collect: collect-all

.PHONY: list
list: list-all

# ==============================================================================
# End of Makefile
# ==============================================================================
