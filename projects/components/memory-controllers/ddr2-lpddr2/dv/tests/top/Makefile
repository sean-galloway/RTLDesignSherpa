# ==============================================================================
# DDR2/LPDDR2 Memory-Controller Top-Level Tests Makefile
# ==============================================================================
#
# Local test runner for top-level (full ddr2_lpddr2_top DUT) tests.
#
# Usage:
#   cd $REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/dv/tests/top
#   make <target>
#
# Quick start:
#   make help           - Show available targets
#   make run-all        - Run top tests (FUNC level, default)
#   make run-gate       - Run top tests at GATE level (quick smoke)
#   make run-func       - Run top tests at FUNC level (default)
#   make run-full       - Run top tests at FULL level (comprehensive)
#   make ptw            - Run pytest-watch (auto-rerun on file changes)
#   make clean          - Clean local artifacts
#
# NOTE: the top test file selects its scenario matrix from TEST_LEVEL
#       (GATE | FUNC | FULL). FULL == FUNC for the top tier today, so
#       run-func and run-full exercise the same set; GATE is a quick subset.
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

# Test file. Default `.` so pytest discovers every test_*.py in this
# directory (currently test_ddr2_lpddr2_top.py). Override to focus, e.g.
#   make run-full TEST_FILE=test_ddr2_lpddr2_top.py
TEST_FILE = .

# Default target
.DEFAULT_GOAL := help

# ==============================================================================
# Help Target
# ==============================================================================

.PHONY: help
help:
	@echo "================================================================================"
	@echo "DDR2/LPDDR2 Memory-Controller Top-Level Tests Makefile"
	@echo "================================================================================"
	@echo ""
	@echo "QUICK RUN TARGETS:"
	@echo "  make run-all                      Run top tests (FUNC level)"
	@echo "  make run-all-parallel             Run top tests in parallel"
	@echo "  make ptw                          Run pytest-watch (auto-rerun on changes)"
	@echo ""
	@echo "LEVEL TARGETS:"
	@echo "  make run-gate                     Run top tests at GATE level (quick smoke)"
	@echo "  make run-gate-waves               GATE level with waveforms"
	@echo "  make run-gate-parallel            GATE level in parallel"
	@echo "  make run-gate-parallel-waves      GATE level parallel + waves"
	@echo "  make run-func                     Run top tests at FUNC level (default)"
	@echo "  make run-func-waves               FUNC level with waveforms"
	@echo "  make run-func-parallel            FUNC level in parallel"
	@echo "  make run-func-parallel-waves      FUNC level parallel + waves"
	@echo "  make run-full                     Run top tests at FULL level"
	@echo "  make run-full-waves               FULL level with waveforms"
	@echo "  make run-full-parallel            FULL level in parallel"
	@echo "  make run-full-parallel-waves      FULL level parallel + waves"
	@echo ""
	@echo "BY CATEGORY (pytest -k filters; run within FULL set):"
	@echo "  make run-smoke                    smoke / configure_via_apb"
	@echo "  make run-b2b                      wr_rd_b2b_* (pipelined write->read)"
	@echo "  make run-engine                   engine_mirror_kbN (pattern-gen engines)"
	@echo "  make run-profile                  profile_sweep (AW/W/B/AR/R timing profiles)"
	@echo ""
	@echo "INDIVIDUAL SCENARIO (SCENARIO=<name>):"
	@echo "  make run-one SCENARIO=wr_rd_b2b_truly_pipelined"
	@echo "  make run-one-waves SCENARIO=engine_mirror"
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
	@echo "Running ddr2_lpddr2_top tests (FUNC level)..."
	TEST_LEVEL=FUNC $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-all-parallel
run-all-parallel:
	@echo "Running ddr2_lpddr2_top tests (FUNC level) in parallel..."
	TEST_LEVEL=FUNC $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: ptw
ptw:
	@echo "Running pytest-watch (auto-rerun on file changes)..."
	TEST_LEVEL=FUNC $(PTW) $(PTW_FLAGS) -- $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

# ==============================================================================
# Level Targets
# ==============================================================================

# GATE level
.PHONY: run-gate
run-gate:
	@echo "Running ddr2_lpddr2_top tests at GATE level..."
	TEST_LEVEL=GATE $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-gate-waves
run-gate-waves:
	@echo "Running ddr2_lpddr2_top tests at GATE level with waveforms..."
	WAVES=1 TEST_LEVEL=GATE $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-gate-parallel
run-gate-parallel:
	@echo "Running ddr2_lpddr2_top tests at GATE level in parallel..."
	TEST_LEVEL=GATE $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-gate-parallel-waves
run-gate-parallel-waves:
	@echo "Running ddr2_lpddr2_top tests at GATE level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=GATE $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FUNC level
.PHONY: run-func
run-func:
	@echo "Running ddr2_lpddr2_top tests at FUNC level..."
	TEST_LEVEL=FUNC $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-func-waves
run-func-waves:
	@echo "Running ddr2_lpddr2_top tests at FUNC level with waveforms..."
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-func-parallel
run-func-parallel:
	@echo "Running ddr2_lpddr2_top tests at FUNC level in parallel..."
	TEST_LEVEL=FUNC $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-func-parallel-waves
run-func-parallel-waves:
	@echo "Running ddr2_lpddr2_top tests at FUNC level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FULL level
.PHONY: run-full
run-full:
	@echo "Running ddr2_lpddr2_top tests at FULL level..."
	TEST_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-full-waves
run-full-waves:
	@echo "Running ddr2_lpddr2_top tests at FULL level with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-full-parallel
run-full-parallel:
	@echo "Running ddr2_lpddr2_top tests at FULL level in parallel..."
	TEST_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-full-parallel-waves
run-full-parallel-waves:
	@echo "Running ddr2_lpddr2_top tests at FULL level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# Category Targets (pytest -k filters; run within FULL set)
# ==============================================================================

.PHONY: run-smoke
run-smoke:
	@echo "Running smoke scenarios..."
	TEST_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
	  -k "smoke or configure_via_apb"

.PHONY: run-b2b
run-b2b:
	@echo "Running back-to-back write->read scenarios..."
	TEST_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
	  -k "wr_rd_b2b"

.PHONY: run-engine
run-engine:
	@echo "Running engine-mirror (pattern-gen engine) scenarios..."
	TEST_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
	  -k "engine_mirror"

.PHONY: run-profile
run-profile:
	@echo "Running profile-sweep (AXI timing profile) scenarios..."
	TEST_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
	  -k "profile_sweep"

# ==============================================================================
# Single-Scenario Targets
# ==============================================================================

.PHONY: run-one
run-one:
	@if [ -z "$(SCENARIO)" ]; then \
	  echo "Error: SCENARIO=<name> is required."; \
	  echo "  e.g. make run-one SCENARIO=wr_rd_b2b_truly_pipelined"; \
	  exit 1; \
	fi
	@echo "Running scenario '$(SCENARIO)'..."
	TEST_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) -k "$(SCENARIO)"

.PHONY: run-one-waves
run-one-waves:
	@if [ -z "$(SCENARIO)" ]; then \
	  echo "Error: SCENARIO=<name> is required."; \
	  echo "  e.g. make run-one-waves SCENARIO=engine_mirror"; \
	  exit 1; \
	fi
	@echo "Running scenario '$(SCENARIO)' with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) -k "$(SCENARIO)"

# ==============================================================================
# Utility Targets
# ==============================================================================

.PHONY: collect
collect:
	@echo "Collecting ddr2_lpddr2_top tests..."
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
