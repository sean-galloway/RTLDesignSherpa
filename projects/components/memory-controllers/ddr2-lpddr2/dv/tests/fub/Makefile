# ==============================================================================
# DDR2/LPDDR2 Memory-Controller FUB Tests Makefile
# ==============================================================================
#
# Local test runner for FUB (unit) tests under this directory.
#
# Usage:
#   cd $REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/dv/tests/fub
#   make <target>
#
# Quick start:
#   make help           - Show available targets
#   make run-all        - Run all FUB tests (FUNC level, default)
#   make run-gate       - Run all FUB tests at GATE level (quick)
#   make run-func       - Run all FUB tests at FUNC level (default)
#   make run-full       - Run all FUB tests at FULL level (comprehensive)
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

# Test files (one per FUB)
WR_TEST   = test_wr_cmd_cam.py
RD_TEST   = test_rd_cmd_cam.py
WBS_TEST  = test_wr_beat_sequencer.py
RCL_TEST  = test_rd_cl_aligner.py
DCF_TEST  = test_dfi_cmd_formatter.py
DSP_TEST  = test_dfi_signal_pack.py
MR_TEST   = test_mode_register.py
RF_TEST   = test_refresh_ctrl.py
PD_TEST   = test_powerdown_ctrl.py
INIT_TEST = test_init_sequencer.py
XT_TEST   = test_xbank_timers.py
GT_TEST   = test_global_timers.py
SCH_TEST  = test_scheduler.py
PP_TEST   = test_page_predictor.py

ALL_TESTS = $(WR_TEST) $(RD_TEST) $(WBS_TEST) $(RCL_TEST) $(DCF_TEST) $(DSP_TEST) \
            $(MR_TEST) $(RF_TEST) $(PD_TEST) $(INIT_TEST) \
            $(XT_TEST) $(GT_TEST) $(SCH_TEST) $(PP_TEST)

# Default target
.DEFAULT_GOAL := help

# ==============================================================================
# Help Target
# ==============================================================================

.PHONY: help
help:
	@echo "================================================================================"
	@echo "DDR2/LPDDR2 Memory-Controller FUB Tests Makefile"
	@echo "================================================================================"
	@echo ""
	@echo "QUICK RUN TARGETS:"
	@echo "  make run-all                      Run all FUB tests (FUNC level)"
	@echo "  make run-all-parallel             Run all FUB tests in parallel"
	@echo "  make ptw                          Run pytest-watch (auto-rerun on changes)"
	@echo ""
	@echo "GLOBAL LEVEL TARGETS (all 13 FUB tests):"
	@echo "  make run-gate                     GATE level"
	@echo "  make run-gate-waves               GATE + waveforms"
	@echo "  make run-gate-parallel            GATE + xdist + reruns"
	@echo "  make run-gate-parallel-waves      GATE + xdist + reruns + waves"
	@echo "  make run-func                     FUNC level (default)"
	@echo "  make run-func-waves               FUNC + waveforms"
	@echo "  make run-func-parallel            FUNC + xdist + reruns"
	@echo "  make run-func-parallel-waves      FUNC + xdist + reruns + waves"
	@echo "  make run-full                     FULL level"
	@echo "  make run-full-waves               FULL + waveforms"
	@echo "  make run-full-parallel            FULL + xdist + reruns"
	@echo "  make run-full-parallel-waves      FULL + xdist + reruns + waves"
	@echo ""
	@echo "PER-FUB TARGETS (FUNC + variants):"
	@echo "  make run-wr / run-wr-gate / run-wr-full / run-wr-waves / run-wr-parallel"
	@echo "  make run-rd / run-rd-gate / run-rd-full / run-rd-waves / run-rd-parallel"
	@echo "  make run-wbs / run-wbs-gate / run-wbs-full / run-wbs-waves / run-wbs-parallel"
	@echo "  make run-rcl / run-rcl-gate / run-rcl-full / run-rcl-waves / run-rcl-parallel"
	@echo "  make run-dcf / run-dcf-gate / run-dcf-full / run-dcf-waves"
	@echo "  make run-dsp / run-dsp-gate / run-dsp-full / run-dsp-waves"
	@echo "  make run-mr  / run-mr-parallel       mode_register"
	@echo "  make run-rf  / run-rf-parallel       refresh_ctrl"
	@echo "  make run-pd  / run-pd-parallel       powerdown_ctrl"
	@echo "  make run-init / run-init-parallel    init_sequencer"
	@echo "  make run-xt  / run-xt-parallel       xbank_timers"
	@echo "  make run-gt  / run-gt-parallel       global_timers"
	@echo "  make run-sch / run-sch-parallel      scheduler"
	@echo ""
	@echo "INDIVIDUAL SCENARIO (SCENARIO=<name>):"
	@echo "  make run-one SCENARIO=smoke"
	@echo "  make run-one-waves SCENARIO=smoke"
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
# Quick Run Targets (Default FUNC level, all FUBs)
# ==============================================================================

.PHONY: run-all
run-all:
	@echo "Running all FUB tests (FUNC level)..."
	TEST_LEVEL=FUNC $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-all-parallel
run-all-parallel:
	@echo "Running all FUB tests (FUNC level) in parallel..."
	TEST_LEVEL=FUNC $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: ptw
ptw:
	@echo "Running pytest-watch (auto-rerun on file changes)..."
	TEST_LEVEL=FUNC $(PTW) $(PTW_FLAGS) -- $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

# ==============================================================================
# Global Level Targets (all 13 FUB tests)
# ==============================================================================

# GATE level
.PHONY: run-gate
run-gate:
	@echo "Running all FUB tests at GATE level..."
	TEST_LEVEL=GATE $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-gate-waves
run-gate-waves:
	@echo "Running all FUB tests at GATE level with waveforms..."
	WAVES=1 TEST_LEVEL=GATE $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-gate-parallel
run-gate-parallel:
	@echo "Running all FUB tests at GATE level in parallel..."
	TEST_LEVEL=GATE $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-gate-parallel-waves
run-gate-parallel-waves:
	@echo "Running all FUB tests at GATE level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=GATE $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FUNC level
.PHONY: run-func
run-func:
	@echo "Running all FUB tests at FUNC level..."
	TEST_LEVEL=FUNC $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-func-waves
run-func-waves:
	@echo "Running all FUB tests at FUNC level with waveforms..."
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-func-parallel
run-func-parallel:
	@echo "Running all FUB tests at FUNC level in parallel..."
	TEST_LEVEL=FUNC $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-func-parallel-waves
run-func-parallel-waves:
	@echo "Running all FUB tests at FUNC level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FULL level
.PHONY: run-full
run-full:
	@echo "Running all FUB tests at FULL level..."
	TEST_LEVEL=FULL $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-full-waves
run-full-waves:
	@echo "Running all FUB tests at FULL level with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-full-parallel
run-full-parallel:
	@echo "Running all FUB tests at FULL level in parallel..."
	TEST_LEVEL=FULL $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-full-parallel-waves
run-full-parallel-waves:
	@echo "Running all FUB tests at FULL level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# Per-FUB Targets (CAMs + data path)
# ==============================================================================

# wr_cmd_cam
.PHONY: run-wr run-wr-gate run-wr-full run-wr-waves run-wr-parallel
run-wr:
	TEST_LEVEL=FUNC $(PYTEST) $(WR_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)
run-wr-gate:
	TEST_LEVEL=GATE $(PYTEST) $(WR_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)
run-wr-full:
	TEST_LEVEL=FULL $(PYTEST) $(WR_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)
run-wr-waves:
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) $(WR_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)
run-wr-parallel:
	TEST_LEVEL=FUNC $(PYTEST) $(WR_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# rd_cmd_cam
.PHONY: run-rd run-rd-gate run-rd-full run-rd-waves run-rd-parallel
run-rd:
	TEST_LEVEL=FUNC $(PYTEST) $(RD_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)
run-rd-gate:
	TEST_LEVEL=GATE $(PYTEST) $(RD_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)
run-rd-full:
	TEST_LEVEL=FULL $(PYTEST) $(RD_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)
run-rd-waves:
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) $(RD_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)
run-rd-parallel:
	TEST_LEVEL=FUNC $(PYTEST) $(RD_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# wr_beat_sequencer
.PHONY: run-wbs run-wbs-gate run-wbs-full run-wbs-waves run-wbs-parallel
run-wbs:
	TEST_LEVEL=FUNC $(PYTEST) $(WBS_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)
run-wbs-gate:
	TEST_LEVEL=GATE $(PYTEST) $(WBS_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)
run-wbs-full:
	TEST_LEVEL=FULL $(PYTEST) $(WBS_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)
run-wbs-waves:
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) $(WBS_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)
run-wbs-parallel:
	TEST_LEVEL=FUNC $(PYTEST) $(WBS_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# rd_cl_aligner
.PHONY: run-rcl run-rcl-gate run-rcl-full run-rcl-waves run-rcl-parallel
run-rcl:
	TEST_LEVEL=FUNC $(PYTEST) $(RCL_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)
run-rcl-gate:
	TEST_LEVEL=GATE $(PYTEST) $(RCL_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)
run-rcl-full:
	TEST_LEVEL=FULL $(PYTEST) $(RCL_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)
run-rcl-waves:
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) $(RCL_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)
run-rcl-parallel:
	TEST_LEVEL=FUNC $(PYTEST) $(RCL_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# dfi_cmd_formatter
.PHONY: run-dcf run-dcf-gate run-dcf-full run-dcf-waves
run-dcf:
	TEST_LEVEL=FUNC $(PYTEST) $(DCF_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)
run-dcf-gate:
	TEST_LEVEL=GATE $(PYTEST) $(DCF_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)
run-dcf-full:
	TEST_LEVEL=FULL $(PYTEST) $(DCF_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)
run-dcf-waves:
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) $(DCF_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

# dfi_signal_pack
.PHONY: run-dsp run-dsp-gate run-dsp-full run-dsp-waves
run-dsp:
	TEST_LEVEL=FUNC $(PYTEST) $(DSP_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)
run-dsp-gate:
	TEST_LEVEL=GATE $(PYTEST) $(DSP_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)
run-dsp-full:
	TEST_LEVEL=FULL $(PYTEST) $(DSP_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)
run-dsp-waves:
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) $(DSP_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

# ==============================================================================
# Per-FUB Targets (control plane / timers / scheduler)
# ==============================================================================

.PHONY: run-mr run-mr-parallel run-rf run-rf-parallel run-pd run-pd-parallel \
        run-init run-init-parallel run-xt run-xt-parallel run-gt run-gt-parallel \
        run-sch run-sch-parallel

run-mr:
	TEST_LEVEL=FUNC $(PYTEST) $(MR_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)
run-mr-parallel:
	TEST_LEVEL=FUNC $(PYTEST) $(MR_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

run-rf:
	TEST_LEVEL=FUNC $(PYTEST) $(RF_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)
run-rf-parallel:
	TEST_LEVEL=FUNC $(PYTEST) $(RF_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

run-pd:
	TEST_LEVEL=FUNC $(PYTEST) $(PD_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)
run-pd-parallel:
	TEST_LEVEL=FUNC $(PYTEST) $(PD_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

run-init:
	TEST_LEVEL=FUNC $(PYTEST) $(INIT_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)
run-init-parallel:
	TEST_LEVEL=FUNC $(PYTEST) $(INIT_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

run-xt:
	TEST_LEVEL=FUNC $(PYTEST) $(XT_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)
run-xt-parallel:
	TEST_LEVEL=FUNC $(PYTEST) $(XT_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

run-gt:
	TEST_LEVEL=FUNC $(PYTEST) $(GT_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)
run-gt-parallel:
	TEST_LEVEL=FUNC $(PYTEST) $(GT_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

run-sch:
	TEST_LEVEL=FUNC $(PYTEST) $(SCH_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)
run-sch-parallel:
	TEST_LEVEL=FUNC $(PYTEST) $(SCH_TEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# Single-Scenario Targets
# ==============================================================================

.PHONY: run-one
run-one:
	@if [ -z "$(SCENARIO)" ]; then \
	  echo "Error: SCENARIO=<name> is required."; \
	  echo "  e.g. make run-one SCENARIO=smoke"; \
	  exit 1; \
	fi
	@echo "Running scenario '$(SCENARIO)' across all FUB tests..."
	TEST_LEVEL=FULL $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) -k "$(SCENARIO)"

.PHONY: run-one-waves
run-one-waves:
	@if [ -z "$(SCENARIO)" ]; then \
	  echo "Error: SCENARIO=<name> is required."; \
	  echo "  e.g. make run-one-waves SCENARIO=smoke"; \
	  exit 1; \
	fi
	@echo "Running scenario '$(SCENARIO)' with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) -k "$(SCENARIO)"

# ==============================================================================
# Utility Targets
# ==============================================================================

.PHONY: collect
collect:
	@echo "Collecting FUB tests..."
	$(PYTEST) $(ALL_TESTS) --collect-only

.PHONY: list
list:
	@echo "Scenarios at TEST_LEVEL=$${TEST_LEVEL:-FUNC} (override with TEST_LEVEL=GATE|FUNC|FULL):"
	@$(PYTEST) $(ALL_TESTS) --collect-only -q 2>/dev/null \
	   | grep -E '\[.*\]$$' \
	   | sed 's/.*\[/  /' \
	   | sed 's/\]$$//'

.PHONY: clean
clean:
	@echo "Cleaning local artifacts..."
	rm -rf __pycache__ .pytest_cache *.pyc
	rm -rf local_sim_build logs
	find . -name '*.pyc' -delete

.PHONY: clean-all
clean-all: clean
	@echo "Cleaning all test artifacts..."
	find . -name "*.vcd" -delete
	find . -name "*.fst" -delete
	find . -name "*.fst.hier" -delete
	find . -name "*.log" -delete
