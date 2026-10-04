# ==============================================================================
# bch DV Makefile - run one target across every area, in series
# ==============================================================================
#
#   source $REPO_ROOT/env_python
#   cd $REPO_ROOT/projects/components/ecc-ip/bch/dv/tests
#   make <target>                  # forwarded to every area below
#   make <target> AREAS="fub"      # ...or only the ones you name
#
# Each area (today just fub/) is a four-line Makefile including make/tests.mk.
# This file adds no test logic of its own -- it forwards whatever target you
# give to each area with `$(MAKE) -C <area> <target>`.
#
# Target grammar comes from make/tests.mk:
#   make run-all-<gate|func|full>[-serial|-parallel][-waves]
#   make run-<testglob>-<level>    e.g. make 'run-bch_encoder*-full'
#   make clean-all | list | status | jobs | help
#
# ALWAYS clean-all before a regression you intend to trust -- a stale sim_build
# passes against old RTL.
# ==============================================================================

SHELL := /bin/bash

RDS_ROOT ?= $(shell git rev-parse --show-toplevel)
export REPO_ROOT ?= $(RDS_ROOT)

AREAS ?= fub

GREEN  := \033[0;32m
RED    := \033[0;31m
YELLOW := \033[0;33m
RESET  := \033[0m

.DEFAULT_GOAL := help

.PHONY: _dispatch
_dispatch:
	@echo "================================================================================"
	@echo "bch: '$(TARGET)' across: $(AREAS)"
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
	@echo "bch DV Makefile - one target, every area, in series"
	@echo "================================================================================"
	@echo ""
	@echo "  make <target>                  forward <target> to every area"
	@echo "  make <target> AREAS=\"fub\"      ...or only the areas you name"
	@echo ""
	@echo "Regression sweeps:"
	@echo "  make clean-all"
	@echo "  make run-all-gate              quick smoke over every area"
	@echo "  make run-all-func              the usual regression"
	@echo "  make run-all-full              sign-off"
	@echo ""
	@echo "Per area, from make/tests.mk:"
	@echo "  run-all-<gate|func|full>[-serial|-parallel][-waves]"
	@echo "  run-<testglob>-<level>         e.g. make 'run-bch_encoder*-full'"
	@echo "  list | status | jobs | clean-all"
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

%:
	@$(MAKE) --no-print-directory _dispatch TARGET=$@
