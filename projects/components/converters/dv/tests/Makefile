# ==============================================================================
# Converters (Data Width + Protocol) Test Makefile
# ==============================================================================
#
# PREREQUISITES:
#   Must be run with sourced environment:
#     source $REPO_ROOT/env_python  # Sets $REPO_ROOT and activates venv
#     cd $REPO_ROOT/projects/components/converters/dv/tests
#     make <target>
#
# Quick start:
#   make help           - Show all available targets
#   make run-all        - Run all converter tests (REG_LEVEL=FUNC)
#   make run-all-full   - Run comprehensive tests (REG_LEVEL=FULL)
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
PYTEST_XDIST = -n 48  # 48 parallel workers (matching AMBA/STREAM/RAPIDS)
PYTEST_TBSTYLE = --tb=short
PYTEST_RERUNS = --reruns 0 --reruns-delay 1  # Retry failed tests up to 3 times

# Default target - show help
.DEFAULT_GOAL := help

# ==============================================================================
# Help Target
# ==============================================================================

.PHONY: help
help:
	@echo "================================================================================"
	@echo "Converters (Data Width + Protocol) Test Makefile - Available Targets"
	@echo "================================================================================"
	@echo ""
	@echo "OVERVIEW:"
	@echo "  Converters - Data width and protocol conversion modules"
	@echo "  Components: Data width converters (up/down), Protocol converters (AXI4-APB)"
	@echo ""
	@echo "REG_LEVEL CONTROL:"
	@echo "  REG_LEVEL environment variable controls test depth:"
	@echo "    GATE: Quick smoke test (~5 min)  - Basic connectivity"
	@echo "    FUNC: Functional coverage (~30 min, DEFAULT) - Full validation"
	@echo "    FULL: Comprehensive validation (~4 hr) - Stress tests, edge cases"
	@echo ""
	@echo "RUN TARGETS:"
	@echo "  make run-all              Run all tests (REG_LEVEL=FUNC, serial)"
	@echo "  make run-all-parallel     Run all tests (REG_LEVEL=FUNC, 48 workers)"
	@echo ""
	@echo "  make run-all-gate         Run gate level tests (quick smoke)"
	@echo "  make run-all-gate-parallel Run gate tests (parallel)"
	@echo ""
	@echo "  make run-all-func         Run functional tests (default level)"
	@echo "  make run-all-func-parallel Run functional tests (parallel)"
	@echo ""
	@echo "  make run-all-full         Run full tests (comprehensive)"
	@echo "  make run-all-full-parallel Run full tests (parallel)"
	@echo ""
	@echo "INDIVIDUAL TEST TARGETS:"
	@echo "  Data Width Converters:"
	@echo "    make run-rd-converter     Run read converter tests (REG_LEVEL=FUNC)"
	@echo "    make run-wr-converter     Run write converter tests (REG_LEVEL=FUNC)"
	@echo ""
	@echo "    make run-rd-converter-gate Run read converter (REG_LEVEL=GATE)"
	@echo "    make run-rd-converter-func Run read converter (REG_LEVEL=FUNC)"
	@echo "    make run-rd-converter-full Run read converter (REG_LEVEL=FULL)"
	@echo ""
	@echo "    make run-wr-converter-gate Run write converter (REG_LEVEL=GATE)"
	@echo "    make run-wr-converter-func Run write converter (REG_LEVEL=FUNC)"
	@echo "    make run-wr-converter-full Run write converter (REG_LEVEL=FULL)"
	@echo ""
	@echo "  Protocol Converters:"
	@echo "    make run-peakrdl-cmdrsp      Run PeakRDL-to-CmdRsp (REG_LEVEL=FUNC)"
	@echo "    make run-peakrdl-cmdrsp-gate Run PeakRDL-to-CmdRsp (REG_LEVEL=GATE)"
	@echo "    make run-peakrdl-cmdrsp-func Run PeakRDL-to-CmdRsp (REG_LEVEL=FUNC)"
	@echo "    make run-peakrdl-cmdrsp-full Run PeakRDL-to-CmdRsp (REG_LEVEL=FULL)"
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
	@echo "DIAGNOSTIC TARGETS:"
	@echo "  make check-env            Verify environment setup"
	@echo "  make verify               Verify targets exist and work"
	@echo ""
	@echo "EXAMPLES:"
	@echo "  make run-all-parallel          # Default: FUNC level, 48 workers"
	@echo "  make run-all-gate-parallel     # Quick smoke test, 48 workers"
	@echo "  make run-all-full-parallel     # Comprehensive test, 48 workers"
	@echo "  make run-wr-converter-func     # Write converter, FUNC level"
	@echo ""
	@echo "TROUBLESHOOTING:"
	@echo "  If you get 'target not found', run: make verify"
	@echo "  This will check your environment and show instructions"
	@echo ""
	@echo "================================================================================"
	@echo "Prerequisites: source $(REPO_ROOT)/env_python"
	@echo "Current REPO_ROOT: $(REPO_ROOT)"
	@echo "================================================================================"

# ==============================================================================
# REG_LEVEL Control for All Tests
# ==============================================================================

.PHONY: run-all-gate
run-all-gate:
	@echo "================================================================================"
	@echo "Running AXI4 Converter Tests - GATE level (quick smoke test)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-gate-parallel
run-all-gate-parallel:
	@echo "================================================================================"
	@echo "Running AXI4 Converter Tests - GATE level (parallel, 48 workers)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_*.py

.PHONY: run-all-func
run-all-func:
	@echo "================================================================================"
	@echo "Running AXI4 Converter Tests - FUNC level (functional coverage)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-func-parallel
run-all-func-parallel:
	@echo "================================================================================"
	@echo "Running AXI4 Converter Tests - FUNC level (parallel, 48 workers)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_*.py

.PHONY: run-all-full
run-all-full:
	@echo "================================================================================"
	@echo "Running AXI4 Converter Tests - FULL level (comprehensive validation)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-full-parallel
run-all-full-parallel:
	@echo "================================================================================"
	@echo "Running AXI4 Converter Tests - FULL level (parallel, 48 workers)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_*.py

# ==============================================================================
# Individual Test Targets (Read Converter)
# ==============================================================================

.PHONY: run-rd-converter
run-rd-converter:
	@echo "Running AXI4 read data width converter tests (REG_LEVEL=FUNC)..."
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_dwidth_converter_rd.py

.PHONY: run-rd-converter-gate
run-rd-converter-gate:
	@echo "Running AXI4 read data width converter tests (REG_LEVEL=GATE)..."
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_dwidth_converter_rd.py

.PHONY: run-rd-converter-func
run-rd-converter-func:
	@echo "Running AXI4 read data width converter tests (REG_LEVEL=FUNC)..."
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_dwidth_converter_rd.py

.PHONY: run-rd-converter-full
run-rd-converter-full:
	@echo "Running AXI4 read data width converter tests (REG_LEVEL=FULL)..."
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_dwidth_converter_rd.py

# ==============================================================================
# Individual Test Targets (Write Converter)
# ==============================================================================

.PHONY: run-wr-converter
run-wr-converter:
	@echo "Running AXI4 write data width converter tests (REG_LEVEL=FUNC)..."
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_dwidth_converter_wr.py

.PHONY: run-wr-converter-gate
run-wr-converter-gate:
	@echo "Running AXI4 write data width converter tests (REG_LEVEL=GATE)..."
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_dwidth_converter_wr.py

.PHONY: run-wr-converter-func
run-wr-converter-func:
	@echo "Running AXI4 write data width converter tests (REG_LEVEL=FUNC)..."
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_dwidth_converter_wr.py

.PHONY: run-wr-converter-full
run-wr-converter-full:
	@echo "Running AXI4 write data width converter tests (REG_LEVEL=FULL)..."
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_dwidth_converter_wr.py

# ==============================================================================
# Individual Test Targets (Protocol Converters - PeakRDL to CmdRsp)
# ==============================================================================

.PHONY: run-peakrdl-cmdrsp
run-peakrdl-cmdrsp:
	@echo "Running PeakRDL-to-CmdRsp adapter tests (REG_LEVEL=FUNC)..."
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_peakrdl_to_cmdrsp.py

.PHONY: run-peakrdl-cmdrsp-gate
run-peakrdl-cmdrsp-gate:
	@echo "Running PeakRDL-to-CmdRsp adapter tests (REG_LEVEL=GATE)..."
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_peakrdl_to_cmdrsp.py

.PHONY: run-peakrdl-cmdrsp-func
run-peakrdl-cmdrsp-func:
	@echo "Running PeakRDL-to-CmdRsp adapter tests (REG_LEVEL=FUNC)..."
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_peakrdl_to_cmdrsp.py

.PHONY: run-peakrdl-cmdrsp-full
run-peakrdl-cmdrsp-full:
	@echo "Running PeakRDL-to-CmdRsp adapter tests (REG_LEVEL=FULL)..."
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_peakrdl_to_cmdrsp.py

# ==============================================================================
# Legacy Run Targets (backwards compatibility)
# ==============================================================================

.PHONY: run-all
run-all:
	@echo "================================================================================"
	@echo "Running ALL AXI4 Converter Tests (REG_LEVEL=FUNC, serial)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-parallel
run-all-parallel:
	@echo "================================================================================"
	@echo "Running ALL AXI4 Converter Tests (REG_LEVEL=FUNC, parallel - 48 workers)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_*.py

# ==============================================================================
# Collection Targets (verify tests without running)
# ==============================================================================

.PHONY: collect-all
collect-all:
	@echo "Collecting ALL AXI4 converter tests..."
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
	@echo "Starting pytest-watch for Converters tests"
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
	@echo "✓ All AXI4 converter test artifacts cleaned"
	@echo "================================================================================"

# ==============================================================================
# Utility Targets
# ==============================================================================

.PHONY: list-all
list-all:
	@echo "All AXI4 Converter Test Modules:"
	@ls test_*.py 2>/dev/null | sort

.PHONY: status
status:
	@echo "================================================================================"
	@echo "Converters Test Status"
	@echo "================================================================================"
	@echo "Test directories:"
	@echo "  CONVERTERS Tests:  $(REPO_ROOT)/projects/components/converters/dv/tests/"
	@echo ""
	@echo "Test modules found:"
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
	@echo ""
	@echo "Test Coverage Summary:"
	@echo "  Data Width Converters: Read/Write (up/down conversion)"
	@echo "  Protocol Converters: PeakRDL-to-CmdRsp adapter"
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
# Diagnostic Targets
# ==============================================================================

.PHONY: check-env
check-env:
	@echo "================================================================================"
	@echo "Environment Check"
	@echo "================================================================================"
	@echo "REPO_ROOT: $(REPO_ROOT)"
	@echo "Current directory: $(shell pwd)"
	@echo "Expected directory: $(REPO_ROOT)projects/components/converters/dv/tests"
	@echo ""
	@CLEAN_REPO=$$(echo "$(REPO_ROOT)" | sed 's|/*$$||'); \
	EXPECTED_DIR="$$CLEAN_REPO/projects/components/converters/dv/tests"; \
	if [ "$(shell pwd)" != "$$EXPECTED_DIR" ]; then \
		echo "❌ WARNING: You are not in the correct directory!"; \
		echo "   Run: cd $$EXPECTED_DIR"; \
	else \
		echo "✓ Directory is correct"; \
	fi
	@echo ""
	@if [ -z "$(REPO_ROOT)" ]; then \
		echo "❌ ERROR: REPO_ROOT not set!"; \
		echo "   Run: source $(shell pwd | sed 's|/projects/.*||')/env_python"; \
	else \
		echo "✓ REPO_ROOT is set"; \
	fi
	@echo ""
	@echo "Available test files:"
	@ls -1 test_*.py 2>/dev/null || echo "  No test files found"
	@echo ""
	@echo "GNU Make version:"
	@$(MAKE) --version | head -1
	@echo "================================================================================"

.PHONY: verify
verify: check-env
	@echo ""
	@echo "Verifying run-all-full-parallel target exists..."
	@$(MAKE) -n run-all-full-parallel > /dev/null 2>&1 && \
		echo "✓ Target 'run-all-full-parallel' found and working" || \
		echo "❌ ERROR: Target 'run-all-full-parallel' not found"
	@echo ""
	@echo "To run full parallel tests:"
	@CLEAN_REPO=$$(echo "$(REPO_ROOT)" | sed 's|/*$$||'); \
	echo "  1. source $$CLEAN_REPO/env_python"; \
	echo "  2. cd $$CLEAN_REPO/projects/components/converters/dv/tests"; \
	echo "  3. make run-all-full-parallel"
	@echo "================================================================================"

# ==============================================================================
# End of Makefile
# ==============================================================================
