# ==============================================================================
# DDR2/LPDDR2 Memory-Controller FUB Tests Makefile
# ==============================================================================
# Local runner for fub (unit) tests under this directory.
#
# Usage:
#   cd $REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/dv/tests/fub
#   make help                    Show available targets
#   make run-wr                  Run wr_cmd_cam tests at FUNC level
#   make run-rd                  Run rd_cmd_cam tests at FUNC level
#   make run-all                 Run both
#   make run-wr-waves            Run wr CAM tests with FST dump
#   make run-rd-waves            Run rd CAM tests with FST dump
#   make clean / clean-all       Clean local artifacts
#
# Prefer the env_python alias for ad-hoc use:
#   ptw  test_wr_cmd_cam.py -k smoke
#   ptwp test_rd_cmd_cam.py
# ==============================================================================

SHELL := /bin/bash

ifndef REPO_ROOT
$(error REPO_ROOT is not set. Please run: source $$REPO_ROOT/env_python)
endif

PYTEST = python3 -m pytest
VFLAGS = -v --tb=short
XDIST  = -n logical

WR_TEST  = test_wr_cmd_cam.py
RD_TEST  = test_rd_cmd_cam.py
WBS_TEST = test_wr_beat_sequencer.py
RCL_TEST = test_rd_cl_aligner.py
DCF_TEST = test_dfi_cmd_formatter.py
DSP_TEST = test_dfi_signal_pack.py

.DEFAULT_GOAL := help

# ------------------------------------------------------------------------------
# Help
# ------------------------------------------------------------------------------
.PHONY: help
help:
	@echo "============================================================"
	@echo "DDR2/LPDDR2 FUB tests"
	@echo "============================================================"
	@echo ""
	@echo "wr_cmd_cam_fub:"
	@echo "  make run-wr             FUNC level"
	@echo "  make run-wr-gate        GATE level (quick)"
	@echo "  make run-wr-full        FULL level"
	@echo "  make run-wr-waves       FUNC + FST waveforms"
	@echo "  make run-wr-parallel    FUNC + xdist"
	@echo ""
	@echo "rd_cmd_cam_fub:"
	@echo "  make run-rd             FUNC level"
	@echo "  make run-rd-gate        GATE level (quick)"
	@echo "  make run-rd-full        FULL level"
	@echo "  make run-rd-waves       FUNC + FST waveforms"
	@echo "  make run-rd-parallel    FUNC + xdist"
	@echo ""
	@echo "wr_beat_sequencer_fub:"
	@echo "  make run-wbs            FUNC level (rate-2 + rate-4)"
	@echo "  make run-wbs-gate       GATE level (rate-2 quick)"
	@echo "  make run-wbs-full       FULL level"
	@echo "  make run-wbs-waves      FUNC + FST waveforms"
	@echo "  make run-wbs-parallel   FUNC + xdist"
	@echo ""
	@echo "rd_cl_aligner_fub:"
	@echo "  make run-rcl            FUNC level (rate-2 + rate-4)"
	@echo "  make run-rcl-gate       GATE level"
	@echo "  make run-rcl-full       FULL level"
	@echo "  make run-rcl-waves      FUNC + FST waveforms"
	@echo "  make run-rcl-parallel   FUNC + xdist"
	@echo ""
	@echo "dfi_cmd_formatter_fub:"
	@echo "  make run-dcf            FUNC level"
	@echo "  make run-dcf-gate       GATE level"
	@echo "  make run-dcf-full       FULL level"
	@echo "  make run-dcf-waves      FUNC + FST waveforms"
	@echo ""
	@echo "dfi_signal_pack_fub:"
	@echo "  make run-dsp            FUNC level"
	@echo "  make run-dsp-gate       GATE level"
	@echo "  make run-dsp-full       FULL level"
	@echo "  make run-dsp-waves      FUNC + FST waveforms"
	@echo ""
	@echo "Combined:"
	@echo "  make run-all            All FUBs, FUNC level"
	@echo "  make run-all-parallel   All FUBs, FUNC level, xdist"
	@echo ""
	@echo "Cleanup:"
	@echo "  make clean              Remove local sim/build/logs"
	@echo "  make clean-all          + traces"
	@echo ""

# ------------------------------------------------------------------------------
# wr_cmd_cam targets
# ------------------------------------------------------------------------------
.PHONY: run-wr run-wr-gate run-wr-full run-wr-waves run-wr-parallel
run-wr:
	TEST_LEVEL=FUNC $(PYTEST) $(VFLAGS) $(WR_TEST)

run-wr-gate:
	TEST_LEVEL=GATE $(PYTEST) $(VFLAGS) $(WR_TEST)

run-wr-full:
	TEST_LEVEL=FULL $(PYTEST) $(VFLAGS) $(WR_TEST)

run-wr-waves:
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) $(VFLAGS) $(WR_TEST)

run-wr-parallel:
	TEST_LEVEL=FUNC $(PYTEST) $(VFLAGS) $(XDIST) $(WR_TEST)

# ------------------------------------------------------------------------------
# rd_cmd_cam targets
# ------------------------------------------------------------------------------
.PHONY: run-rd run-rd-gate run-rd-full run-rd-waves run-rd-parallel
run-rd:
	TEST_LEVEL=FUNC $(PYTEST) $(VFLAGS) $(RD_TEST)

run-rd-gate:
	TEST_LEVEL=GATE $(PYTEST) $(VFLAGS) $(RD_TEST)

run-rd-full:
	TEST_LEVEL=FULL $(PYTEST) $(VFLAGS) $(RD_TEST)

run-rd-waves:
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) $(VFLAGS) $(RD_TEST)

run-rd-parallel:
	TEST_LEVEL=FUNC $(PYTEST) $(VFLAGS) $(XDIST) $(RD_TEST)

# ------------------------------------------------------------------------------
# wr_beat_sequencer targets
# ------------------------------------------------------------------------------
.PHONY: run-wbs run-wbs-gate run-wbs-full run-wbs-waves run-wbs-parallel
run-wbs:
	TEST_LEVEL=FUNC $(PYTEST) $(VFLAGS) $(WBS_TEST)

run-wbs-gate:
	TEST_LEVEL=GATE $(PYTEST) $(VFLAGS) $(WBS_TEST)

run-wbs-full:
	TEST_LEVEL=FULL $(PYTEST) $(VFLAGS) $(WBS_TEST)

run-wbs-waves:
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) $(VFLAGS) $(WBS_TEST)

run-wbs-parallel:
	TEST_LEVEL=FUNC $(PYTEST) $(VFLAGS) $(XDIST) $(WBS_TEST)

# ------------------------------------------------------------------------------
# rd_cl_aligner targets
# ------------------------------------------------------------------------------
.PHONY: run-rcl run-rcl-gate run-rcl-full run-rcl-waves run-rcl-parallel
run-rcl:
	TEST_LEVEL=FUNC $(PYTEST) $(VFLAGS) $(RCL_TEST)

run-rcl-gate:
	TEST_LEVEL=GATE $(PYTEST) $(VFLAGS) $(RCL_TEST)

run-rcl-full:
	TEST_LEVEL=FULL $(PYTEST) $(VFLAGS) $(RCL_TEST)

run-rcl-waves:
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) $(VFLAGS) $(RCL_TEST)

run-rcl-parallel:
	TEST_LEVEL=FUNC $(PYTEST) $(VFLAGS) $(XDIST) $(RCL_TEST)

# ------------------------------------------------------------------------------
# dfi_cmd_formatter targets
# ------------------------------------------------------------------------------
.PHONY: run-dcf run-dcf-gate run-dcf-full run-dcf-waves
run-dcf:
	TEST_LEVEL=FUNC $(PYTEST) $(VFLAGS) $(DCF_TEST)

run-dcf-gate:
	TEST_LEVEL=GATE $(PYTEST) $(VFLAGS) $(DCF_TEST)

run-dcf-full:
	TEST_LEVEL=FULL $(PYTEST) $(VFLAGS) $(DCF_TEST)

run-dcf-waves:
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) $(VFLAGS) $(DCF_TEST)

# ------------------------------------------------------------------------------
# dfi_signal_pack targets
# ------------------------------------------------------------------------------
.PHONY: run-dsp run-dsp-gate run-dsp-full run-dsp-waves
run-dsp:
	TEST_LEVEL=FUNC $(PYTEST) $(VFLAGS) $(DSP_TEST)

run-dsp-gate:
	TEST_LEVEL=GATE $(PYTEST) $(VFLAGS) $(DSP_TEST)

run-dsp-full:
	TEST_LEVEL=FULL $(PYTEST) $(VFLAGS) $(DSP_TEST)

run-dsp-waves:
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) $(VFLAGS) $(DSP_TEST)

# ------------------------------------------------------------------------------
# Combined
# ------------------------------------------------------------------------------
.PHONY: run-all run-all-parallel
run-all:
	TEST_LEVEL=FUNC $(PYTEST) $(VFLAGS) $(WR_TEST) $(RD_TEST) $(WBS_TEST) $(RCL_TEST) $(DCF_TEST) $(DSP_TEST)

run-all-parallel:
	TEST_LEVEL=FUNC $(PYTEST) $(VFLAGS) $(XDIST) $(WR_TEST) $(RD_TEST) $(WBS_TEST) $(RCL_TEST) $(DCF_TEST) $(DSP_TEST)

# ------------------------------------------------------------------------------
# Cleanup
# ------------------------------------------------------------------------------
.PHONY: clean clean-all
clean:
	rm -rf local_sim_build logs __pycache__
	find . -name '*.pyc' -delete

clean-all: clean
	rm -f *.vcd *.fst *.fst.hier
