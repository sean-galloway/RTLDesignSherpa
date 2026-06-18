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

WR_TEST = test_wr_cmd_cam.py
RD_TEST = test_rd_cmd_cam.py

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
	@echo "Both:"
	@echo "  make run-all            Both CAMs, FUNC level"
	@echo "  make run-all-parallel   Both CAMs, FUNC level, xdist"
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
# Combined
# ------------------------------------------------------------------------------
.PHONY: run-all run-all-parallel
run-all:
	TEST_LEVEL=FUNC $(PYTEST) $(VFLAGS) $(WR_TEST) $(RD_TEST)

run-all-parallel:
	TEST_LEVEL=FUNC $(PYTEST) $(VFLAGS) $(XDIST) $(WR_TEST) $(RD_TEST)

# ------------------------------------------------------------------------------
# Cleanup
# ------------------------------------------------------------------------------
.PHONY: clean clean-all
clean:
	rm -rf local_sim_build logs __pycache__
	find . -name '*.pyc' -delete

clean-all: clean
	rm -f *.vcd *.fst *.fst.hier
