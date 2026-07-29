# ==============================================================================
# STREAM DV Makefile - run one target across fub / macro / top, in series
# ==============================================================================
#
#   source $REPO_ROOT/env_python
#   cd $REPO_ROOT/projects/components/dmas/stream/dv/tests
#   make <target>                    # forwarded to every area below
#   make <target> AREAS="fub top"    # ...or only the ones you name
#
# Each area (fub/, macro/, top/) is a four-line Makefile including
# make/tests.mk (TOOL-008), same as the val/ areas. This file adds no test
# logic of its own -- it forwards whatever target you give to each area with
# `$(MAKE) -C <area> <target>`, exactly like val/Makefile.
#
# Areas run IN SERIES and every one runs even if an earlier fails, so a
# regression sweep reports all three rather than stopping at the first. Exit is
# nonzero if any area failed and the summary names which.
#
# Target grammar comes from make/tests.mk:
#   make run-all-<gate|func|full>[-serial|-parallel][-waves]
#   make clean-all | list | status | jobs | help
#
# Coverage: the stream conftests read the COVERAGE env, so run any level with
#   COVERAGE=1 make run-all-full-parallel
# then merge with `make coverage-report` (a local, stream-specific target below).
#
# ALWAYS clean-all before a regression you intend to trust -- see
# vault/handbook/dv/running-regressions.md.
# ==============================================================================

SHELL := /bin/bash

RDS_ROOT ?= $(shell git rev-parse --show-toplevel)
export REPO_ROOT ?= $(RDS_ROOT)

# STREAM test areas, in run order. Override to narrow: make run-all-gate AREAS=fub
AREAS ?= fub macro top

COVERAGE_REPORTS_DIR := coverage_reports

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
	@echo "stream: '$(TARGET)' across: $(AREAS)"
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
	@echo "STREAM DV Makefile - one target, every area (fub/macro/top), in series"
	@echo "================================================================================"
	@echo ""
	@echo "  make <target>                  forward <target> to every area"
	@echo "  make <target> AREAS=\"fub top\"  ...or only to the areas you name"
	@echo ""
	@echo "Regression sweeps (clean first -- a stale sim_build passes against old RTL):"
	@echo "  make clean-all"
	@echo "  make run-all-gate              quick smoke over fub/macro/top"
	@echo "  make run-all-func              the usual regression"
	@echo "  make run-all-full              sign-off"
	@echo ""
	@echo "Per area, from make/tests.mk:"
	@echo "  run-all-<gate|func|full>[-serial|-parallel][-waves]"
	@echo "  run-<testglob>-<level>         e.g. make 'run-stream_top*-gate' AREAS=top"
	@echo "  list | status | jobs | clean-all"
	@echo ""
	@echo "Coverage (stream conftests read COVERAGE):"
	@echo "  COVERAGE=1 make run-all-full-parallel"
	@echo "  make coverage-report           merge per-level coverage -> $(COVERAGE_REPORTS_DIR)/"
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

# Stream-specific post-processing: merge the per-level coverage data the
# COVERAGE=1 runs emit. Defined here (not forwarded to areas) because it is a
# single merge across all areas, not a per-area action.
.PHONY: coverage-report
coverage-report:
	@echo "Generating merged coverage report..."
	@mkdir -p $(COVERAGE_REPORTS_DIR)
	@python3 $(REPO_ROOT)/bin/cov_utils/merge_testlevel_coverage.py $(COVERAGE_REPORTS_DIR) stream
	@echo "Report: $(COVERAGE_REPORTS_DIR)/latest_coverage_report.md"

# Forward any goal not defined above. Must stay LAST: a match-anything rule
# shadows anything defined after it.
%:
	@$(MAKE) --no-print-directory _dispatch TARGET=$@
