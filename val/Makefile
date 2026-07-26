# ==============================================================================
# Master Validation Makefile - run one target across every test area, in series
# ==============================================================================
#
#   source $REPO_ROOT/env_python
#   cd $REPO_ROOT/val
#   make <target>                  # forwarded to every area below
#   make <target> AREAS="cdc math" # ...or only the ones you name
#
# Every area under val/ is a four-line Makefile including make/tests.mk
# (TOOL-008). This file adds no test logic of its own -- it forwards whatever
# target you give to each area with `$(MAKE) -C <area> <target>`.
#
# There is deliberately no per-target wiring here. The previous version
# enumerated run-amba / run-common / run-integ-amba / run-integ-common by hand
# across 405 lines, so val/cdc and val/math -- 132 test roots between them --
# were unreachable from this level and, in cdc's case, did not exist when it was
# written. A dispatcher cannot go stale that way.
#
# Areas run IN SERIES and every one runs even if an earlier fails, so a
# regression sweep reports all six rather than stopping at the first. Exit is
# nonzero if any area failed and the summary names which.
#
# Target grammar comes from make/tests.mk:
#   make run-all-<gate|func|full>[-serial|-parallel][-waves]
#   make clean-all | list | status | jobs | help
#
# ALWAYS clean-all before a regression you intend to trust -- see
# vault/handbook/dv/running-regressions.md.
# ==============================================================================

SHELL := /bin/bash

RDS_ROOT ?= $(shell git rev-parse --show-toplevel)
export REPO_ROOT ?= $(RDS_ROOT)

# Every test area. Override to narrow a sweep: make run-all-gate AREAS=cdc
AREAS ?= common cdc math amba integ_common integ_amba

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
	@echo "val: '$(TARGET)' across: $(AREAS)"
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
	@echo "Master Validation Makefile - one target, every area, in series"
	@echo "================================================================================"
	@echo ""
	@echo "  make <target>                forward <target> to every area"
	@echo "  make <target> AREAS=\"a b\"    ...or only to the areas you name"
	@echo ""
	@echo "Regression sweeps (clean first -- a stale sim_build passes against old RTL):"
	@echo "  make clean-all"
	@echo "  make run-all-gate            quick smoke over every area"
	@echo "  make run-all-func            the usual regression"
	@echo "  make run-all-full            sign-off"
	@echo ""
	@echo "Per area, from make/tests.mk:"
	@echo "  run-all-<gate|func|full>[-serial|-parallel][-waves]"
	@echo "  run-<testglob>-<level>       e.g. make 'run-arbiter*-gate' AREAS=common"
	@echo "  list | status | jobs | clean-all"
	@echo ""
	@echo "This level only:"
	@echo "  make help                    this text"
	@echo "  make areas                   list areas and test-root counts"
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
