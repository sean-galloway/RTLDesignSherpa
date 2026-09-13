# ==============================================================================
# RAPIDS DV Makefile - run one target across every area, in series
# ==============================================================================
#
#   source $REPO_ROOT/env_python
#   cd $REPO_ROOT/projects/components/dmas/rapids/dv/tests
#   make <target>                              # forwarded to every area below
#   make <target> AREAS="fub_beats top_beats"  # ...or only the ones you name
#
# Each area is a four-line Makefile including make/tests.mk (TOOL-008), the
# same as pumice, stream and the val/ areas. This file adds no test logic.
#
# WHY THIS REPLACED ~600 LINES OF HAND-WRITTEN TARGETS (2026-09-13). Those
# targets invoked names the areas do not define, so RAPIDS COULD NOT BE RUN
# FROM ITS TOP LEVEL AT ALL:
#
#     make run-gate-parallel
#     ==> fub (run-gate-parallel)
#     make[1]: *** No rule to make target 'run-gate-parallel'.  Stop.
#
# tests.mk defines run-all[-<level>][-serial|-parallel][-waves]; the old file
# called `run`, `run-gate`, `run-func`, `run-full`, `run-waves`, `collect` and
# `ptw`. Of everything it forwarded, only `clean-all` and `run-parallel`
# existed. It also hardcoded `-n 48`, which tests.mk DERIVES from cores and
# memory (a fixed 48 on an 8-core box is a 6x oversubscription that has
# already forced a hard machine kill), and its clean used plain `rm -rf` on
# local_sim_build instead of the marker-aware bin/clean_sim_builds.py, which
# skips directories a live run is using.
#
# Target grammar comes from make/tests.mk:
#   make run-all-<gate|func|full>[-serial|-parallel][-waves]
#   make run-<testglob>-<level>      e.g. make 'run-scheduler*-full' AREAS=fub_beats
#   make clean-all | list | status | jobs | help
#
# ALWAYS clean-all before a regression you intend to trust -- a stale sim_build
# passes against old RTL. See vault/handbook/dv/running-regressions.md.
# ==============================================================================

SHELL := /bin/bash

RDS_ROOT ?= $(shell git rev-parse --show-toplevel)
export REPO_ROOT ?= $(RDS_ROOT)

# RAPIDS test areas, in run order. fub/ and macro/ are the pre-beats tiers;
# the beats areas are the current RTL. Override to narrow:
#   make run-all-gate AREAS="fub_beats macro_beats top_beats"
AREAS ?= fub fub_beats macro macro_beats top_beats

GREEN  := \033[0;32m
RED    := \033[0;31m
YELLOW := \033[0;33m
RESET  := \033[0m

.DEFAULT_GOAL := help

.PHONY: _dispatch
_dispatch:
	@echo "================================================================================"
	@echo "rapids: '$(TARGET)' across: $(AREAS)"
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

.PHONY: help
help:
	@echo "================================================================================"
	@echo "RAPIDS DV Makefile - one target, every area, in series"
	@echo "================================================================================"
	@echo ""
	@echo "  make <target>                        forward <target> to every area"
	@echo "  make <target> AREAS=\"fub_beats\"      ...or only the areas you name"
	@echo ""
	@echo "Regression sweeps (clean first -- a stale sim_build passes against old RTL):"
	@echo "  make clean-all"
	@echo "  make run-all-gate                    quick smoke over every area"
	@echo "  make run-all-func                    the usual regression"
	@echo "  make run-all-full                    sign-off"
	@echo ""
	@echo "Per area, from make/tests.mk:"
	@echo "  run-all-<gate|func|full>[-serial|-parallel][-waves]"
	@echo "  run-<testglob>-<level>   e.g. make 'run-scheduler*-full' AREAS=fub_beats"
	@echo "  list | status | jobs | clean-all"
	@echo ""
	@echo "  Worker count is DERIVED from cores and memory -- never hardcode -n."
	@echo "  Override with: make JOBS=16 run-all-full-parallel"
	@echo ""
	@echo "This level only:"
	@echo "  make help                            this text"
	@echo "  make areas                           list areas and test-root counts"
	@echo ""
	@echo "AREAS = $(AREAS)"
	@echo "================================================================================"

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
%:
	@$(MAKE) --no-print-directory _dispatch TARGET=$@
