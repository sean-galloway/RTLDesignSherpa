# ==============================================================================
# Misc DV Makefile - run one target across every area, in series
# ==============================================================================
#
#   source $REPO_ROOT/env_python
#   cd $REPO_ROOT/projects/components/timing-char/dv/tests
#   make <target>                  # forwarded to every area below
#   make <target> AREAS="fub"      # ...or only the ones you name
#
# Each area (today just fub/) is a four-line Makefile including make/tests.mk
# (TOOL-008), the same as the val/ areas, stream, rapids and pumice. This file
# adds no test logic of its own -- it forwards whatever target you give to each
# area with `$(MAKE) -C <area> <target>`, exactly like val/Makefile.
#
# WHY THIS REPLACED A HAND-WRITTEN UMBRELLA. The previous version enumerated
# run-fub / run-fub-parallel / run-fub-waves / fub-% by hand and mapped the
# standard run-all-* names onto fub/'s same-named targets. That works only
# while there is exactly one area and only for the targets someone remembered
# to list; a dispatcher forwards EVERY target make/tests.mk defines, including
# the run-<testglob>-<level> forms, and gains new areas by adding a word to
# AREAS. The same drift is what retired ~600 lines in rapids, 1057 in pumice
# and 405 in val.
#
# Areas run IN SERIES and every one runs even if an earlier fails, so a sweep
# reports all of them rather than stopping at the first. Exit is nonzero if any
# area failed and the summary names which.
#
# Target grammar comes from make/tests.mk:
#   make run-all-<gate|func|full>[-serial|-parallel][-waves]
#   make run-<testglob>-<level>    e.g. make 'run-mux_tree*-full'
#   make clean-all | list | status | jobs | help
#
# ALWAYS clean-all before a regression you intend to trust -- a stale sim_build
# passes against old RTL. See vault/handbook/dv/running-regressions.md.
# ==============================================================================

SHELL := /bin/bash

RDS_ROOT ?= $(shell git rev-parse --show-toplevel)
export REPO_ROOT ?= $(RDS_ROOT)

# timing-char test areas, in run order. Override to narrow: make run-all-gate AREAS=fub
AREAS ?= fub top

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
	@echo "timing-char: '$(TARGET)' across: $(AREAS)"
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
	@echo "timing-char DV Makefile - one target, every area, in series"
	@echo "================================================================================"
	@echo ""
	@echo "  make <target>                  forward <target> to every area"
	@echo "  make <target> AREAS=\"fub\"      ...or only the areas you name"
	@echo ""
	@echo "Regression sweeps (clean first -- a stale sim_build passes against old RTL):"
	@echo "  make clean-all"
	@echo "  make run-all-gate              quick smoke over every area"
	@echo "  make run-all-func              the usual regression"
	@echo "  make run-all-full              sign-off"
	@echo ""
	@echo "Per area, from make/tests.mk:"
	@echo "  run-all-<gate|func|full>[-serial|-parallel][-waves]"
	@echo "  run-<testglob>-<level>         e.g. make 'run-mux_tree*-full'"
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
