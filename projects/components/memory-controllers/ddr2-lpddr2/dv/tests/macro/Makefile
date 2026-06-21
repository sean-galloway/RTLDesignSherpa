# ==============================================================================
# DDR2/LPDDR2 Memory-Controller Macro Tests Makefile
# ==============================================================================
#
# Local test runner for macro-level (integration) tests
#
# Usage:
#   cd $REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/dv/tests/macro
#   make <target>
#
# Quick start:
#   make help           - Show available targets
#   make run-all        - Run macro tests (FUNC level, default)
#   make run-gate       - Run macro tests at GATE level (quick)
#   make run-func       - Run macro tests at FUNC level (default)
#   make run-full       - Run macro tests at FULL level (comprehensive)
#   make ptw            - Run pytest-watch (auto-rerun on file changes)
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

# Pytest-watch options
PTW = ptw
PTW_FLAGS = --runner "pytest --maxfail=1"

# Test file
TEST_FILE = test_axi_frontend_macro.py

# Default target
.DEFAULT_GOAL := help

# ==============================================================================
# Help Target
# ==============================================================================

.PHONY: help
help:
	@echo "================================================================================"
	@echo "DDR2/LPDDR2 Memory-Controller Macro Tests Makefile"
	@echo "================================================================================"
	@echo ""
	@echo "QUICK RUN TARGETS:"
	@echo "  make run-all                      Run macro tests (FUNC level)"
	@echo "  make run-all-parallel             Run macro tests in parallel"
	@echo "  make ptw                          Run pytest-watch (auto-rerun on changes)"
	@echo ""
	@echo "MACRO TARGETS (test_axi_frontend_macro.py):"
	@echo "  make run-gate                     Run macro tests at GATE level"
	@echo "  make run-gate-waves               Run macro tests at GATE level with waveforms"
	@echo "  make run-gate-parallel            Run macro tests at GATE level in parallel"
	@echo "  make run-gate-parallel-waves      Run macro tests at GATE level parallel + waves"
	@echo "  make run-func                     Run macro tests at FUNC level (default)"
	@echo "  make run-func-waves               Run macro tests at FUNC level with waveforms"
	@echo "  make run-func-parallel            Run macro tests at FUNC level in parallel"
	@echo "  make run-func-parallel-waves      Run macro tests at FUNC level parallel + waves"
	@echo "  make run-full                     Run macro tests at FULL level"
	@echo "  make run-full-waves               Run macro tests at FULL level with waveforms"
	@echo "  make run-full-parallel            Run macro tests at FULL level in parallel"
	@echo "  make run-full-parallel-waves      Run macro tests at FULL level parallel + waves"
	@echo ""
	@echo "BY BUILD CONFIG (orthogonal to level):"
	@echo "  make run-single                   Single-rank (NUM_RANKS=1) only"
	@echo "  make run-multi                    Multi-rank  (NUM_RANKS=2) only"
	@echo ""
	@echo "BY CATEGORY (pytest -k filters; runs FULL set):"
	@echo "  make run-sanity                   smoke / miss / partial_strb / len_mismatch"
	@echo "  make run-stream                   wr_stream / rd_stream / mixed_stream"
	@echo "  make run-snarf                    snarf_stream / last_write_wins / issued_then_snarf"
	@echo "  make run-ordering                 same_id_in_order / mixed_id_ooo"
	@echo "  make run-lifecycle                wr_full_lifecycle / rd_full_lifecycle"
	@echo "  make run-backpressure             cam_full / forwarded_backpressure"
	@echo "  make run-sched                    scheduler_query / b_complete / mark_issued"
	@echo "  make run-misc                     concurrent_aw_ar / addr_scheme_sweep / multirank"
	@echo ""
	@echo "INDIVIDUAL SCENARIO (SCENARIO=<name>):"
	@echo "  make run-one SCENARIO=smoke"
	@echo "  make run-one-waves SCENARIO=snarf_stream"
	@echo ""
	@echo "UTILITY TARGETS:"
	@echo "  make collect                      Collect (don't run) tests at current TEST_LEVEL"
	@echo "  make list                         Print scenarios in current TEST_LEVEL"
	@echo "  make clean                        Clean local artifacts"
	@echo "  make clean-all                    Clean all test artifacts"
	@echo ""
	@echo "ENV VARS:"
	@echo "  TEST_LEVEL = GATE | FUNC | FULL   (default FUNC; selects matrix density)"
	@echo "  WAVES      = 0 | 1                (default 0; -waves recipes set WAVES=1)"
	@echo "  SCENARIO   = <scenario name>      (for run-one targets)"
	@echo ""
	@echo "================================================================================"

# ==============================================================================
# Quick Run Targets (Default FUNC level)
# ==============================================================================

.PHONY: run-all
run-all:
	@echo "Running axi_frontend_macro tests (FUNC level)..."
	TEST_LEVEL=FUNC $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-all-parallel
run-all-parallel:
	@echo "Running axi_frontend_macro tests (FUNC level) in parallel..."
	TEST_LEVEL=FUNC $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: ptw
ptw:
	@echo "Running pytest-watch (auto-rerun on file changes)..."
	TEST_LEVEL=FUNC $(PTW) $(PTW_FLAGS) -- $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

# ==============================================================================
# Macro Targets (test_axi_frontend_macro.py)
# ==============================================================================

# GATE level
.PHONY: run-gate
run-gate:
	@echo "Running axi_frontend_macro tests at GATE level..."
	TEST_LEVEL=GATE $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-gate-waves
run-gate-waves:
	@echo "Running axi_frontend_macro tests at GATE level with waveforms..."
	WAVES=1 TEST_LEVEL=GATE $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-gate-parallel
run-gate-parallel:
	@echo "Running axi_frontend_macro tests at GATE level in parallel..."
	TEST_LEVEL=GATE $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-gate-parallel-waves
run-gate-parallel-waves:
	@echo "Running axi_frontend_macro tests at GATE level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=GATE $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FUNC level
.PHONY: run-func
run-func:
	@echo "Running axi_frontend_macro tests at FUNC level..."
	TEST_LEVEL=FUNC $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-func-waves
run-func-waves:
	@echo "Running axi_frontend_macro tests at FUNC level with waveforms..."
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-func-parallel
run-func-parallel:
	@echo "Running axi_frontend_macro tests at FUNC level in parallel..."
	TEST_LEVEL=FUNC $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-func-parallel-waves
run-func-parallel-waves:
	@echo "Running axi_frontend_macro tests at FUNC level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FULL level
.PHONY: run-full
run-full:
	@echo "Running axi_frontend_macro tests at FULL level..."
	TEST_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-full-waves
run-full-waves:
	@echo "Running axi_frontend_macro tests at FULL level with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-full-parallel
run-full-parallel:
	@echo "Running axi_frontend_macro tests at FULL level in parallel..."
	TEST_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-full-parallel-waves
run-full-parallel-waves:
	@echo "Running axi_frontend_macro tests at FULL level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# Build Config Targets (orthogonal to TEST_LEVEL; runs FULL set within scope)
# ==============================================================================

.PHONY: run-single
run-single:
	@echo "Running single-rank scenarios (NUM_RANKS=1)..."
	TEST_LEVEL=FULL $(PYTEST) $(TEST_FILE)::test_axi_frontend_macro $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-multi
run-multi:
	@echo "Running multi-rank scenarios (NUM_RANKS=2)..."
	TEST_LEVEL=FULL $(PYTEST) $(TEST_FILE)::test_axi_frontend_macro_multirank $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

# ==============================================================================
# Category Targets (pytest -k filters; run within FULL set)
# ==============================================================================

.PHONY: run-sanity
run-sanity:
	@echo "Running sanity scenarios..."
	TEST_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
	  -k "smoke or miss or partial_strb or len_mismatch"

.PHONY: run-stream
run-stream:
	@echo "Running streaming scenarios..."
	TEST_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
	  -k "wr_stream or rd_stream or mixed_stream"

.PHONY: run-snarf
run-snarf:
	@echo "Running snarf scenarios..."
	TEST_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
	  -k "snarf or last_write_wins or issued_then_snarf"

.PHONY: run-ordering
run-ordering:
	@echo "Running ordering scenarios..."
	TEST_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
	  -k "same_id_in_order or mixed_id_ooo"

.PHONY: run-lifecycle
run-lifecycle:
	@echo "Running lifecycle scenarios..."
	TEST_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
	  -k "full_lifecycle"

.PHONY: run-backpressure
run-backpressure:
	@echo "Running backpressure scenarios..."
	TEST_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
	  -k "cam_full or forwarded_backpressure"

.PHONY: run-sched
run-sched:
	@echo "Running scheduler-interface scenarios..."
	TEST_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
	  -k "scheduler_query or b_complete_clears or mark_issued"

.PHONY: run-misc
run-misc:
	@echo "Running misc scenarios..."
	TEST_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
	  -k "concurrent_aw_ar or addr_scheme_sweep or multirank"

# ==============================================================================
# Single-Scenario Targets
# ==============================================================================

.PHONY: run-one
run-one:
	@if [ -z "$(SCENARIO)" ]; then \
	  echo "Error: SCENARIO=<name> is required."; \
	  echo "  e.g. make run-one SCENARIO=snarf_stream"; \
	  exit 1; \
	fi
	@echo "Running scenario '$(SCENARIO)'..."
	TEST_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) -k "$(SCENARIO)"

.PHONY: run-one-waves
run-one-waves:
	@if [ -z "$(SCENARIO)" ]; then \
	  echo "Error: SCENARIO=<name> is required."; \
	  echo "  e.g. make run-one-waves SCENARIO=snarf_stream"; \
	  exit 1; \
	fi
	@echo "Running scenario '$(SCENARIO)' with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) -k "$(SCENARIO)"

# ==============================================================================
# Utility Targets
# ==============================================================================

.PHONY: collect
collect:
	@echo "Collecting axi_frontend_macro tests..."
	$(PYTEST) $(TEST_FILE) --collect-only

.PHONY: list
list:
	@echo "Scenarios at TEST_LEVEL=$${TEST_LEVEL:-FUNC} (override with TEST_LEVEL=GATE|FUNC|FULL):"
	@$(PYTEST) $(TEST_FILE) --collect-only -q 2>/dev/null \
	   | grep -E '\[.*\]$$' \
	   | sed 's/.*\[/  /' \
	   | sed 's/\]$$//'

.PHONY: clean
clean:
	@echo "Cleaning local artifacts..."
	rm -rf __pycache__ .pytest_cache *.pyc

.PHONY: clean-all
clean-all: clean
	@echo "Cleaning all test artifacts..."
	rm -rf local_sim_build logs
	find . -name "*.vcd" -delete
	find . -name "*.fst" -delete
	find . -name "*.fst.hier" -delete
	find . -name "*.log" -delete
