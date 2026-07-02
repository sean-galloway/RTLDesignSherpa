# ==============================================================================
# NexysA7 project aggregator Makefile
# ==============================================================================
#
# Convenience wrapper that fans out clean / status commands across every
# NexysA7 sub-project's Makefile. Motivation: a full DDR2 char + timing
# char + stream char build cycle leaves ~32 GB of verilator sim_build /
# precompiled-header / FST artifacts scattered across half a dozen dirs.
# `make clean-all` here reclaims all of them in one shot.
#
# PREREQUISITES:
#   source $REPO_ROOT/env_python
#   cd $REPO_ROOT/projects/NexysA7
#   make <target>
#
# TARGETS:
#   make status         Show sim_build / logs disk usage per sub-project
#   make clean          Run `make clean` in every sub-project that has one
#   make clean-all      Run `make clean-all` in every sub-project that has one
#   make list           List which sub-Makefiles will be visited
#   make help           This text
#
# The list of visited Makefiles is EXPLICIT (not `find`) so the behavior
# is predictable and vendor / external checkouts (e.g. iDMA's Bender
# workspace under flows-idma-bridge/external/) are never touched.
# ==============================================================================

SHELL := /bin/bash

# ------------------------------------------------------------------------------
# Sub-project Makefile directories.
#
# Order = depth-first: leaf test dirs first (so they get cleaned before any
# aggregator above them re-visits them). Every entry MUST have a Makefile
# with the corresponding target — see `make list` output for verification.
# ------------------------------------------------------------------------------

# Sub-projects that support `clean-all` (the aggressive cleanup):
CLEAN_ALL_DIRS = \
    ddr2-characterization/ddr2_char_framework/dv/tests \
    stream_characterization/flows-stream-bridge/dv/tests \
    stream_characterization/flows-stream-bridge \
    stream_characterization/flows-vivado-mcdma \
    stream_characterization/stream_char_framework/rtl/bridges/dv/tests \
    timing_characterization/dv/tests/fub \
    timing_characterization/dv/tests/top \
    timing_characterization/dv/tests \
    timing_characterization/fpga

# Sub-projects that support only `clean` (lighter cleanup or single-target):
CLEAN_ONLY_DIRS = \
    cdc_counter_display

# All dirs that we'll visit for the light `clean` target (superset of both).
CLEAN_DIRS = $(CLEAN_ALL_DIRS) $(CLEAN_ONLY_DIRS)

# Directories to check for disk usage on `make status`.
STATUS_ROOTS = \
    ddr2-characterization \
    stream_characterization \
    timing_characterization \
    cdc_counter_display \
    boards

# ==============================================================================
# Targets
# ==============================================================================

.DEFAULT_GOAL := help

.PHONY: help
help:
	@echo "================================================================================"
	@echo "NexysA7 aggregator Makefile"
	@echo "================================================================================"
	@echo ""
	@echo "CLEAN:"
	@echo "  make clean        Light clean (pycache, .pyc, logs) in every sub-project"
	@echo "  make clean-all    Full clean incl. local_sim_build, waves — reclaims ~32 GB"
	@echo ""
	@echo "INFO:"
	@echo "  make status       Show disk usage per sub-project + total"
	@echo "  make list         List sub-Makefiles that will be visited"
	@echo ""

.PHONY: list
list:
	@echo "clean-all will visit:"
	@for d in $(CLEAN_ALL_DIRS); do echo "  $$d"; done
	@echo ""
	@echo "clean-only will visit:"
	@for d in $(CLEAN_ONLY_DIRS); do echo "  $$d"; done

# ------------------------------------------------------------------------------
# clean-all — fan out to every sub-project. Runs sequentially so one
# noisy sub-project's output stays readable; the operation is I/O bound
# on rm, not CPU, so parallelism buys little.
# ------------------------------------------------------------------------------
.PHONY: clean-all
clean-all:
	@echo "================================================================================"
	@echo "NexysA7 clean-all — reclaiming sim_build / waves / precompiled headers"
	@echo "================================================================================"
	@BEFORE=$$(du -sh . 2>/dev/null | cut -f1); \
	 echo "  Before: $$BEFORE"; \
	 echo ""
	@for d in $(CLEAN_ALL_DIRS); do \
	     if [ -f "$$d/Makefile" ]; then \
	         echo ">>> $$d (clean-all)"; \
	         $(MAKE) --no-print-directory -C "$$d" clean-all || \
	             echo "    (clean-all failed, continuing)"; \
	     else \
	         echo "!!! $$d — no Makefile, skipping"; \
	     fi; \
	 done
	@for d in $(CLEAN_ONLY_DIRS); do \
	     if [ -f "$$d/Makefile" ]; then \
	         echo ">>> $$d (clean — no clean-all target)"; \
	         $(MAKE) --no-print-directory -C "$$d" clean || \
	             echo "    (clean failed, continuing)"; \
	     fi; \
	 done
	@echo ""
	@AFTER=$$(du -sh . 2>/dev/null | cut -f1); \
	 echo "  After:  $$AFTER"
	@echo "================================================================================"
	@echo "Done."
	@echo "================================================================================"

# ------------------------------------------------------------------------------
# clean — lighter fan-out: only `clean` (never clean-all). Safe to run
# between test iterations to trim pycache / logs without nuking sim_build.
# ------------------------------------------------------------------------------
.PHONY: clean
clean:
	@echo "NexysA7 clean (light — pycache / logs only)"
	@for d in $(CLEAN_DIRS); do \
	     if [ -f "$$d/Makefile" ]; then \
	         echo ">>> $$d (clean)"; \
	         $(MAKE) --no-print-directory -C "$$d" clean 2>/dev/null || \
	             echo "    (clean not available, skipping)"; \
	     fi; \
	 done

# ------------------------------------------------------------------------------
# status — human-readable disk footprint per sub-project. Useful when
# you're wondering why /mnt/data is filling up.
# ------------------------------------------------------------------------------
.PHONY: status
status:
	@echo "================================================================================"
	@echo "NexysA7 disk footprint"
	@echo "================================================================================"
	@for r in $(STATUS_ROOTS); do \
	     if [ -d "$$r" ]; then \
	         printf "  %-32s %s\n" "$$r" "$$(du -sh $$r 2>/dev/null | cut -f1)"; \
	     fi; \
	 done
	@echo ""
	@echo "  local_sim_build dirs (individual):"
	@find . -type d -name local_sim_build 2>/dev/null | while read d; do \
	     printf "    %-70s %s\n" "$$d" "$$(du -sh $$d 2>/dev/null | cut -f1)"; \
	 done
	@echo ""
	@echo "  Total (this directory): $$(du -sh . 2>/dev/null | cut -f1)"
