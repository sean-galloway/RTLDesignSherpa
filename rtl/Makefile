# ==============================================================================
# RTL Master Makefile - run one target across every RTL area, in series
# ==============================================================================
#
#   source $REPO_ROOT/env_python
#   cd $REPO_ROOT/rtl
#   make <target>            # <target> is forwarded to every area below
#   make <target> AREAS=cdc  # ...or to just the ones you name
#
# Any target you give is dispatched to each area's own Makefile with
# `$(MAKE) -C <area> <target>`. There is no per-target wiring here, so an area
# that grows a new target is reachable from this level the moment it lands --
# the previous version of this file enumerated lint-common/lint-amba/... by
# hand and therefore covered only two of the six areas.
#
# Areas run IN SERIES and every one runs even if an earlier one fails, so a
# sweep tells you about all six rather than stopping at the first. The exit
# status is nonzero if any area failed, and the summary names which.
#
# Two kinds of area Makefile, deliberately:
#   common, amba              hand-written; carry per-category targets
#                             (verilator-counters, verilator-axi4, ...) that
#                             come from knowing the area's structure
#   cdc, math, integ_common   four-liners including rtl/make/area.mk
# Both expose the same target names, which is what makes this dispatch work.
#
# Common targets: lint-all  verilator  verible  yosys  status  clean-all
# ==============================================================================

SHELL := /bin/bash

RDS_ROOT ?= $(shell git rev-parse --show-toplevel)
export REPO_ROOT ?= $(RDS_ROOT)

# Every directory under rtl/ that owns modules. Override on the command line to
# narrow a sweep: make lint-all AREAS="cdc common"
AREAS ?= common cdc math amba integ_common integ_amba

GREEN  := \033[0;32m
RED    := \033[0;31m
YELLOW := \033[0;33m
RESET  := \033[0m

.DEFAULT_GOAL := help

# ------------------------------------------------------------------------------
# The dispatcher. Anything not matched by an explicit target below lands here.
# ------------------------------------------------------------------------------
.PHONY: _dispatch
_dispatch:
	@echo "================================================================================"
	@echo "rtl: '$(TARGET)' across: $(AREAS)"
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
	@echo "RTL Master Makefile - one target, every area, in series"
	@echo "================================================================================"
	@echo ""
	@echo "  make <target>               forward <target> to every area"
	@echo "  make <target> AREAS=\"a b\"   ...or only to the areas you name"
	@echo ""
	@echo "Targets every area understands:"
	@echo "  lint-all       every lint tool available for the area"
	@echo "  verilator      Verilator lint over the area's master filelist"
	@echo "  verible        Verible style lint"
	@echo "  status         module and filelist counts"
	@echo "  clean-all      remove lint artifacts"
	@echo ""
	@echo "This level only:"
	@echo "  make help      this text"
	@echo "  make areas     list the areas and which kind of Makefile each has"
	@echo ""
	@echo "AREAS = $(AREAS)"
	@echo "================================================================================"

.PHONY: areas
areas:
	@printf "%-14s %-22s %s\n" AREA MAKEFILE MODULES
	@printf -- "-------------- ---------------------- -------\n"
	@for area in $(AREAS); do \
	    if [ ! -f "$$area/Makefile" ]; then kind="(none)"; \
	    elif grep -q 'rtl/make/area.mk' "$$area/Makefile" 2>/dev/null; then kind="generic (area.mk)"; \
	    else kind="hand-written"; fi; \
	    n=$$(ls $$area/*.sv $$area/*/*.sv 2>/dev/null | wc -l); \
	    printf "%-14s %-22s %s\n" "$$area" "$$kind" "$$n"; \
	done

# Forward any goal not defined above. `make lint-all` becomes
# `make _dispatch TARGET=lint-all`, which is what keeps this file
# target-agnostic. Must stay LAST: a match-anything rule shadows anything
# defined after it.
%:
	@$(MAKE) --no-print-directory _dispatch TARGET=$@
