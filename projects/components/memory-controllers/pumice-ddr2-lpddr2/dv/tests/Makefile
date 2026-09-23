# ==============================================================================
# pumice DV Makefile - run one target across fub / macro / top, in series
# ==============================================================================
#
#   source $REPO_ROOT/env_python
#   cd $REPO_ROOT/projects/components/memory-controllers/pumice-ddr2-lpddr2/dv/tests
#   make <target>                    # forwarded to every area below
#   make <target> AREAS="fub top"    # ...or only the ones you name
#
# Each area (fub/, macro/, top/) is a four-line Makefile including
# make/tests.mk (TOOL-008), same as the val/ areas and stream. This file adds no
# test logic of its own -- it forwards whatever target you give to each area
# with `$(MAKE) -C <area> <target>`.
#
# WHY THIS REPLACED 1057 LINES OF HAND-WRITTEN TARGETS (2026-08-31). The three
# tier Makefiles had drifted badly and two of the differences were not cosmetic:
#
#   * They hardcoded `-n 48`. make/tests.mk DERIVES the worker count from cores
#     and memory, and says why in its own header: a fixed 48 on an 8-core box is
#     a 6x oversubscription that "has already forced a hard machine kill". On
#     THIS box the derived value happens to be 48 too (48 cores, memory allows
#     94), so converging changes nothing here today -- it changes what happens
#     on a smaller machine. Note pumice is NOT the last area still hardcoding
#     it: rapids, converters, apbx-xbar, retro_legacy_blocks, misc and the
#     components master Makefile all still do.
#   * Their clean removed local_sim_build with a plain `rm -rf`. tests.mk cleans
#     through bin/clean_sim_builds.py, which is MARKER-AWARE: it skips build
#     directories a live run is using and names the owner. Deleting another
#     session's in-flight build does not fail like a deletion -- it surfaces as
#     a corrupt model or a missing file inside Verilator, and it cost three
#     separate debugging sessions before the cause was found. In a shared
#     worktree with several agents running regressions, that is not theoretical.
#
# They had also rotted: the per-FUB targets named test_wr_cmd_cam.py,
# test_scheduler.py and test_axi_intake.py, none of which have existed since the
# rearchitecture. tests.mk DISCOVERS targets by globbing test_*.py, so the
# grammar cannot drift from the files again.
#
# Areas run IN SERIES and every one runs even if an earlier fails, so a
# regression sweep reports all three rather than stopping at the first. Exit is
# nonzero if any area failed and the summary names which.
#
# Target grammar comes from make/tests.mk:
#   make run-all-<gate|func|full>[-serial|-parallel][-waves]
#   make run-<testglob>-<level>       e.g. make 'run-pumice_rd*-full' AREAS=fub
#   make clean-all | list | status | jobs | help
#
# ALWAYS clean-all before a regression you intend to trust -- a stale sim_build
# passes against old RTL. See vault/handbook/dv/running-regressions.md.
# ==============================================================================

SHELL := /bin/bash

RDS_ROOT ?= $(shell git rev-parse --show-toplevel)
export REPO_ROOT ?= $(RDS_ROOT)

# pumice test areas, in run order. Override to narrow: make run-all-gate AREAS=fub
AREAS ?= fub macro top phy

GREEN  := \033[0;32m
RED    := \033[0;31m
YELLOW := \033[0;33m
RESET  := \033[0m

.DEFAULT_GOAL := help

# ------------------------------------------------------------------------------
# The dispatcher. Anything not defined below lands here.
# ------------------------------------------------------------------------------
.PHONY: _dispatch
_dispatch:
	@echo "================================================================================"
	@echo "pumice: '$(TARGET)' across: $(AREAS)"
	@echo "================================================================================"
	@failed=""; skipped=""; \
	for area in $(AREAS); do \
	    if [ ! -f "$$area/Makefile" ]; then \
	        echo -e "$(YELLOW)SKIP $$area: no Makefile$(RESET)"; \
	        skipped="$$skipped $$area"; continue; \
	    fi; \
	    echo ""; \
	    echo "---- $$area ----"; \
	    if $(MAKE) --no-print-directory -C "$$area" $(TARGET); then :; else \
	        failed="$$failed $$area"; \
	    fi; \
	done; \
	echo ""; \
	echo "================================================================================"; \
	if [ -n "$$skipped" ]; then echo -e "$(YELLOW)skipped:$$skipped$(RESET)"; fi; \
	if [ -n "$$failed" ]; then \
	    echo -e "$(RED)FAILED:$$failed$(RESET)"; \
	    echo "================================================================================"; \
	    exit 1; \
	fi; \
	echo -e "$(GREEN)OK: '$(TARGET)' passed in every area$(RESET)"; \
	echo "================================================================================"

# ------------------------------------------------------------------------------
# Targets that belong to this level rather than to an area
# ------------------------------------------------------------------------------
.PHONY: help
help:
	@echo "================================================================================"
	@echo "pumice DV Makefile - one target, every area (fub/macro/top), in series"
	@echo "================================================================================"
	@echo ""
	@echo "  make <target>                  forward <target> to every area"
	@echo "  make <target> AREAS=\"fub top\"  ...or only to the areas you name"
	@echo ""
	@echo "Regression sweeps (clean first -- a stale sim_build passes against old RTL):"
	@echo "  make clean-all"
	@echo "  make run-all-gate              quick smoke over fub/macro/top"
	@echo "  make run-all-func              the usual regression"
	@echo "  make run-all-full              sign-off (the 210-test suite)"
	@echo "  make run-all-func-both         BOTH geometries (default + board BL4/x16)"
	@echo "  make run-board-geom            board geometry only (PUMICE-028)"
	@echo ""
	@echo "Per area, from make/tests.mk:"
	@echo "  run-all-<gate|func|full>[-serial|-parallel][-waves]"
	@echo "  run-<testglob>-<level>         e.g. make 'run-pumice_rd*-full' AREAS=fub"
	@echo "  list | status | jobs | clean-all"
	@echo ""
	@echo "  Worker count is DERIVED from cores and memory -- never hardcode -n."
	@echo "  Override with: make JOBS=16 run-all-full-parallel"
	@echo ""
	@echo "This level only:"
	@echo "  make help                      this text"
	@echo "  make areas                     list areas and test-root counts"
	@echo ""
	@echo "AREAS = $(AREAS)"
	@echo "================================================================================"

# ------------------------------------------------------------------------------
# BOARD GEOMETRY (PUMICE-028)
# ------------------------------------------------------------------------------
# The suite's defaults are DRAM_BEAT=64 / BL8 / device==beat. The shipping board
# is DRAM_BEAT=32 / BL4 / x16, where one DRAM burst is ONE AXI beat instead of
# four. That difference is not cosmetic: every per-sub-command rate limit is
# divided by four before a bandwidth assertion can see it, which is how a 2x
# read throttle once shipped green (PUMICE-025), and it is why PUMICE-041's
# pinned burst length went unnoticed -- the suite could not express the
# geometry it ships.
#
# It has to be a SECOND INVOCATION, not a pytest parametrization: the geometry
# is read at import time into module constants that size the elaborated RTL, so
# one process holds exactly one geometry. That is the same property that made
# PUMICE-041 invisible, used deliberately here.
BOARD_GEOM := TEST_DRAM_BEAT=32 TEST_DRAM_BL=4 TEST_DRAM_DEVICE_W=16

.PHONY: run-board-geom
run-board-geom:     ## the top suite at the SHIPPING geometry (BL4 / x16 / 32b beat)
	@echo "---- board geometry: $(BOARD_GEOM) ----"
	@$(BOARD_GEOM) $(MAKE) --no-print-directory -C top run-all-func

# Both geometries, in series, both reported. This is the target a regression
# sweep should use for pumice: default alone cannot see a board-geometry
# regression, and board alone cannot see a default one.
.PHONY: run-all-func-both
run-all-func-both:  ## default geometry AND board geometry, both reported
	@rc=0; 	echo "==== 1/2 default geometry ===="; 	$(MAKE) --no-print-directory run-all-func || rc=1; 	echo "==== 2/2 board geometry ===="; 	$(MAKE) --no-print-directory run-board-geom || rc=1; 	if [ $$rc -ne 0 ]; then 	    echo -e "$(RED)FAILED: at least one geometry$(RESET)"; exit 1; fi; 	echo -e "$(GREEN)OK: both geometries passed$(RESET)"

.PHONY: areas
areas:
	@printf "%-16s %s\n" AREA "TEST ROOTS"
	@printf -- "---------------- ----------\n"
	@for area in $(AREAS); do \
	    if [ -f "$$area/Makefile" ]; then \
	        n=$$(ls $$area/test_*.py 2>/dev/null | wc -l); \
	    else n="(no Makefile)"; fi; \
	    printf "%-16s %s\n" "$$area" "$$n"; \
	done

# Forward any goal not defined above. Must stay LAST: a match-anything rule
# shadows anything defined after it.
# ------------------------------------------------------------------------------
# BOARD GEOMETRY IS PART OF THE DEFAULT REGRESSION (PUMICE-028)
# ------------------------------------------------------------------------------
# These three names are what projects/components/Makefile invokes, so they are
# the only place "covered by default" can mean anything. Each runs the normal
# pass and then re-runs the TOP area at the shipping geometry.
#
# Why top only: the geometry constants live in dv/tests/top and size the
# elaborated RTL there. fub/ and macro/ do not read them, so a second pass over
# those areas would rebuild identical designs and double the runtime for no
# coverage.
#
# Why a second invocation: the geometry is read at IMPORT time into module
# constants, so one process holds exactly one geometry. That is the property
# that made PUMICE-041 invisible -- a per-test value that reached the testbench
# but not the elaborated RTL -- used deliberately here.
#
# The cost is real (top/ is ~20 min per geometry) and it is the point: the
# default suite could not express the shape that ships, so a 2x read throttle
# shipped green (PUMICE-025) and a pinned burst length went unnoticed
# (PUMICE-041). Use run-all-gate for the quick loop.
.PHONY: run-all-gate run-all-func run-all-full
run-all-gate run-all-func run-all-full:
	@rc=0; 	echo "==== 1/2 default geometry ($@) ===="; 	$(MAKE) --no-print-directory _dispatch TARGET=$@ || rc=1; 	echo "==== 2/2 board geometry ($@, top only): $(BOARD_GEOM) ===="; 	$(BOARD_GEOM) $(MAKE) --no-print-directory -C top $@ || rc=1; 	if [ $$rc -ne 0 ]; then 	    echo -e "$(RED)FAILED: at least one geometry$(RESET)"; exit 1; fi; 	echo -e "$(GREEN)OK: $@ passed at BOTH geometries$(RESET)"

%:
	@$(MAKE) --no-print-directory _dispatch TARGET=$@
