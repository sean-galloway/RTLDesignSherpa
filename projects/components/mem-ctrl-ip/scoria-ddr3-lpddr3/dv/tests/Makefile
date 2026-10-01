# ==============================================================================
# scoria DV Makefile - forward one target to every test area, in series
# ==============================================================================
#
#   source $REPO_ROOT/env_python
#   cd $REPO_ROOT/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3/dv/tests
#   make run-all-gate                # quick smoke
#   make clean-all && make run-all-func
#
# There was no Makefile here until 2026-09-30, which is why
# projects/components/Makefile lists scoria under "exists but doesn't expose
# run-all-* targets": the suite could only be run as a raw pytest, so it was in
# nobody's regression and nothing cleaned its sim_build directories.
#
# Each area is a four-line Makefile including make/tests.mk, same as pumice and
# the val/ areas. This file adds NO test logic: it forwards whatever target you
# give it with `$(MAKE) -C <area> <target>`.
#
# Two things that come from tests.mk and must not be reintroduced here:
#   * the worker count is DERIVED from cores and memory. A hardcoded -n has
#     already forced a hard machine kill on a smaller box.
#   * clean goes through bin/clean_sim_builds.py, which is MARKER-AWARE and
#     skips build directories a live run is using. A plain `rm -rf` of another
#     session's in-flight build surfaces as a corrupt model inside Verilator,
#     not as a deletion error -- it cost three debugging sessions to find once.
#
# Target grammar (make/tests.mk):
#   make run-all-<gate|func|full>[-serial|-parallel][-waves]
#   make run-<testglob>-<level>      e.g. make 'run-scoria_global*-full'
#   make clean-all | list | status | jobs | help
#
# ALWAYS clean-all before a regression you intend to trust -- a stale sim_build
# passes against old RTL. See vault/handbook/dv/running-regressions.md.
# ==============================================================================

SHELL := /bin/bash

RDS_ROOT ?= $(shell git rev-parse --show-toplevel)
export REPO_ROOT ?= $(RDS_ROOT)

# scoria test areas, in run order. Unit suites first, so a composition failure
# is read against a known-good FUB tier rather than alongside it.
#
# `top/` was held out of this list while it was empty -- pytest exits 5 ("no
# tests ran") on an empty area and make turns that into a failure, so including
# it made the whole sweep red for a structural reason, and a regression that is
# red for a reason nobody acts on is a regression people learn to ignore. It
# joined the list with its first test (test_scoria_core.py, AXI in / DFI out).
AREAS ?= fub macro top

GREEN  := \033[0;32m
RED    := \033[0;31m
YELLOW := \033[0;33m
RESET  := \033[0m

.DEFAULT_GOAL := help

.PHONY: _dispatch
_dispatch:
	@echo "================================================================================"
	@echo "scoria: '$(TARGET)' across: $(AREAS)"
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
	@echo "scoria DV Makefile - one target, every area, in series"
	@echo "================================================================================"
	@echo ""
	@echo "  make <target>                  forward <target> to every area"
	@echo "  make <target> AREAS=fub        ...or only the areas you name"
	@echo ""
	@echo "Regression sweeps (clean first -- a stale sim_build passes against old RTL):"
	@echo "  make clean-all"
	@echo "  make run-all-gate              quick smoke"
	@echo "  make run-all-func              the usual regression"
	@echo "  make run-all-full              sign-off"
	@echo ""
	@echo "Per area, from make/tests.mk:"
	@echo "  run-all-<gate|func|full>[-serial|-parallel][-waves]"
	@echo "  run-<testglob>-<level>         e.g. make 'run-scoria_global*-full'"
	@echo "  list | status | jobs | clean-all"
	@echo ""
	@echo "  Worker count is DERIVED from cores and memory -- never hardcode -n."
	@echo "  Override with: make JOBS=16 run-all-full-parallel"
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
