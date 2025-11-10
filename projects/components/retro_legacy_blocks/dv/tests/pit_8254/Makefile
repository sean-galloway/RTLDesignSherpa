# ==============================================================================
# APB PIT 8254 Test Makefile
# ==============================================================================
#
# PREREQUISITES:
#   Must be run with sourced environment:
#     source $REPO_ROOT/env_python  # Sets $REPO_ROOT and activates venv
#     cd $REPO_ROOT/projects/components/retro_legacy_blocks/dv/tests/pit_8254
#     make <target>
#
# Quick start:
#   make help           - Show all available targets
#   make run-all        - Run all APB PIT 8254 tests (TEST_LEVEL=basic)
#   make run-all-full   - Run comprehensive tests (TEST_LEVEL=full)
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

# Pytest options
PYTEST = python3 -m pytest
PYTEST_VERBOSE = -v
PYTEST_QUIET = -q
PYTEST_XDIST = -n 48  # 48 parallel workers (matching AMBA/STREAM/RAPIDS/HPET)
PYTEST_TBSTYLE = --tb=short
PYTEST_RERUNS = --reruns 3 --reruns-delay 1  # Retry failed tests up to 3 times

# Default target - show help
.DEFAULT_GOAL := help

# ==============================================================================
# Help Target
# ==============================================================================

.PHONY: help
help:
	@echo "================================================================================"
	@echo "APB PIT 8254 Test Makefile - Available Targets"
	@echo "================================================================================"
	@echo ""
	@echo "OVERVIEW:"
	@echo "  APB 8254 Programmable Interval Timer - 3-counter peripheral"
	@echo "  Test coverage: Mode 0 (Interrupt on Terminal Count) implemented"
	@echo ""
	@echo "TEST_LEVEL CONTROL:"
	@echo "  TEST_LEVEL environment variable controls test depth:"
	@echo "    basic:  Quick smoke test (~30s)  - Basic register access, mode 0"
	@echo "    medium: Extended coverage (~90s) - Multiple counters, status register"
	@echo "    full:   Comprehensive validation (~3 min) - Stress tests, edge cases"
	@echo ""
	@echo "RUN TARGETS:"
	@echo "  make run-all              Run all tests (TEST_LEVEL=basic, serial)"
	@echo "  make run-all-parallel     Run all tests (TEST_LEVEL=basic, 48 workers)"
	@echo ""
	@echo "  make run-all-basic        Run basic level tests"
	@echo "  make run-all-basic-parallel Run basic tests (parallel)"
	@echo ""
	@echo "  make run-all-medium       Run medium level tests"
	@echo "  make run-all-medium-parallel Run medium tests (parallel)"
	@echo ""
	@echo "  make run-all-full         Run full tests (comprehensive)"
	@echo "  make run-all-full-parallel Run full tests (parallel)"
	@echo ""
	@echo "INDIVIDUAL TEST TARGETS:"
	@echo "  make run-pit              Run APB PIT 8254 tests (TEST_LEVEL=basic)"
	@echo "  make run-pit-basic        Run APB PIT 8254 tests (TEST_LEVEL=basic)"
	@echo "  make run-pit-medium       Run APB PIT 8254 tests (TEST_LEVEL=medium)"
	@echo "  make run-pit-full         Run APB PIT 8254 tests (TEST_LEVEL=full)"
	@echo ""
	@echo "COLLECTION TARGETS (verify tests, don't run):"
	@echo "  make collect-all          Collect all tests"
	@echo ""
	@echo "DEVELOPMENT TARGETS (pytest-watch):"
	@echo "  make ptw                  Auto-rerun tests on file changes"
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
	@echo "EXAMPLES:"
	@echo "  make run-all-parallel          # Default: basic level, 48 workers"
	@echo "  make run-all-basic-parallel    # Quick smoke test, 48 workers"
	@echo "  make run-all-full-parallel     # Comprehensive test, 48 workers"
	@echo "  make run-pit-basic             # Single test, basic level"
	@echo ""
	@echo "================================================================================"
	@echo "Prerequisites: source $(REPO_ROOT)/env_python"
	@echo "Current REPO_ROOT: $(REPO_ROOT)"
	@echo "================================================================================"

# ==============================================================================
# TEST_LEVEL Control for All Tests
# ==============================================================================

.PHONY: run-all-basic
run-all-basic:
	@echo "================================================================================"
	@echo "Running APB PIT 8254 Tests - basic level (quick smoke test)"
	@echo "================================================================================"
	TEST_LEVEL=basic $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-basic-parallel
run-all-basic-parallel:
	@echo "================================================================================"
	@echo "Running APB PIT 8254 Tests - basic level (parallel, 48 workers)"
	@echo "================================================================================"
	TEST_LEVEL=basic $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_*.py

.PHONY: run-all-medium
run-all-medium:
	@echo "================================================================================"
	@echo "Running APB PIT 8254 Tests - medium level (extended coverage)"
	@echo "================================================================================"
	TEST_LEVEL=medium $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-medium-parallel
run-all-medium-parallel:
	@echo "================================================================================"
	@echo "Running APB PIT 8254 Tests - medium level (parallel, 48 workers)"
	@echo "================================================================================"
	TEST_LEVEL=medium $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_*.py

.PHONY: run-all-full
run-all-full:
	@echo "================================================================================"
	@echo "Running APB PIT 8254 Tests - full level (comprehensive validation)"
	@echo "================================================================================"
	TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-full-parallel
run-all-full-parallel:
	@echo "================================================================================"
	@echo "Running APB PIT 8254 Tests - full level (parallel, 48 workers)"
	@echo "================================================================================"
	TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_*.py

# ==============================================================================
# Individual Test Targets (APB PIT 8254)
# ==============================================================================

.PHONY: run-pit
run-pit:
	@echo "Running APB PIT 8254 Tests (TEST_LEVEL=basic)..."
	TEST_LEVEL=basic $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_apb_pit_8254.py

.PHONY: run-pit-basic
run-pit-basic:
	@echo "Running APB PIT 8254 Tests (TEST_LEVEL=basic)..."
	TEST_LEVEL=basic $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_apb_pit_8254.py

.PHONY: run-pit-medium
run-pit-medium:
	@echo "Running APB PIT 8254 Tests (TEST_LEVEL=medium)..."
	TEST_LEVEL=medium $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_apb_pit_8254.py

.PHONY: run-pit-full
run-pit-full:
	@echo "Running APB PIT 8254 Tests (TEST_LEVEL=full)..."
	TEST_LEVEL=full $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_apb_pit_8254.py

# ==============================================================================
# Legacy Run Targets (backwards compatibility)
# ==============================================================================

.PHONY: run-all
run-all:
	@echo "================================================================================"
	@echo "Running ALL APB PIT 8254 Tests (TEST_LEVEL=basic, serial)"
	@echo "================================================================================"
	TEST_LEVEL=basic $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-parallel
run-all-parallel:
	@echo "================================================================================"
	@echo "Running ALL APB PIT 8254 Tests (TEST_LEVEL=basic, parallel - 48 workers)"
	@echo "================================================================================"
	TEST_LEVEL=basic $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_*.py

# ==============================================================================
# Collection Targets (verify tests without running)
# ==============================================================================

.PHONY: collect-all
collect-all:
	@echo "Collecting ALL APB PIT 8254 tests..."
	$(PYTEST) --collect-only test_*.py

# ==============================================================================
# Development Targets (pytest-watch)
# ==============================================================================

# Pytest-watch options
PTW = ptw
PTW_FLAGS = --runner "pytest --maxfail=1"

.PHONY: ptw
ptw:
	@echo "================================================================================"
	@echo "Starting pytest-watch for APB PIT 8254 tests"
	@echo "Tests will auto-rerun when files change. Press Ctrl+C to stop."
	@echo "================================================================================"
	$(PTW) $(PTW_FLAGS) -- test_*.py $(PYTEST_VERBOSE)

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
	rm -rf sim_build*/
	find . -type d -name "local_sim_build" -exec rm -rf {} + 2>/dev/null || true
	find . -type d -name "sim_build*" -exec rm -rf {} + 2>/dev/null || true
	@echo "✓ Build directories cleaned"

.PHONY: clean-vcd
clean-vcd:
	@echo "Cleaning VCD waveform files..."
	find . -type f -name "*.vcd" -delete
	find . -type f -name "*.fst" -delete
	find . -type f -name "view_waves.sh" -delete
	@echo "✓ Waveform files cleaned"

.PHONY: clean-all
clean-all: clean-logs clean-pycache clean-build clean-vcd
	@echo "================================================================================"
	@echo "✓ All APB PIT 8254 test artifacts cleaned"
	@echo "================================================================================"

# ==============================================================================
# Utility Targets
# ==============================================================================

.PHONY: list-all
list-all:
	@echo "All APB PIT 8254 Test Modules:"
	@ls test_*.py 2>/dev/null | sort

.PHONY: status
status:
	@echo "================================================================================"
	@echo "APB PIT 8254 Test Status"
	@echo "================================================================================"
	@echo "Test directories:"
	@echo "  APB_PIT_8254 Tests:  $(REPO_ROOT)/projects/components/retro_legacy_blocks/dv/tests/pit_8254/"
	@echo ""
	@echo "Test modules found:"
	@echo -n "  Total:       "
	@ls test_*.py 2>/dev/null | wc -l
	@echo ""
	@echo "Build artifacts:"
	@echo -n "  local_sim_build dirs: "
	@find . -type d -name "local_sim_build" 2>/dev/null | wc -l
	@echo -n "  sim_build dirs:       "
	@find . -type d -name "sim_build*" 2>/dev/null | wc -l
	@echo -n "  Log files:            "
	@find . -type f -name "*.log" 2>/dev/null | wc -l
	@echo -n "  VCD files:            "
	@find . -type f -name "*.vcd" 2>/dev/null | wc -l
	@echo -n "  FST files:            "
	@find . -type f -name "*.fst" 2>/dev/null | wc -l
	@echo ""
	@echo "Python environment:"
	@echo "  REPO_ROOT: $(REPO_ROOT)"
	@echo "  Virtual env: $(REPO_ROOT)/env_python"
	@echo ""
	@echo "Test Coverage Summary:"
	@echo "  Mode 0 (Interrupt on Terminal Count): Implemented"
	@echo "  Modes 1-5: Planned for future implementation"
	@echo "  Basic test suite: 6 tests"
	@echo "================================================================================"

# ==============================================================================
# Combined Targets (clean + run)
# ==============================================================================

.PHONY: fresh-all
fresh-all: clean-all run-all
	@echo "✓ Fresh all tests run complete"

.PHONY: fresh-all-parallel
fresh-all-parallel: clean-all run-all-parallel
	@echo "✓ Fresh all tests (parallel) run complete"

# ==============================================================================
# Quick Aliases
# ==============================================================================

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
