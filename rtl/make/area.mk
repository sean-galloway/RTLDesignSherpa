# ==============================================================================
# RTL area Makefile - shared body
# ==============================================================================
#
# The counterpart of make/tests.mk (TOOL-008) for the RTL side. An area whose
# lint is "run the tools over my filelist" needs a four-line Makefile:
#
#     AREA     := cdc
#     RDS_ROOT := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))
#     include $(RDS_ROOT)/rtl/make/area.mk
#
# EVERY area uses this body -- there are no hand-written area Makefiles left.
# The per-category targets that used to justify them (verilator-counters,
# verilator-axi4, ...) fall out of a glob for free, the same way make/tests.mk
# replaced run-apb/run-axi4 with `run-axi4*-gate`:
#
#     make verilator-counter     every path matching *counter*  (was verilator-counters)
#     make verilator-arbiter     ...                            (was verilator-arbiters)
#     make verilator-axi4        every path matching *axi4*      (was verilator-axi4)
#
# A new category needs no edit anywhere, and a category that is renamed cannot
# leave a dead target behind.
#
# The source list comes from filelists/$(AREA)_all.f -- the same compile closure
# the tests and CI use. Never a `find`: a find lints files nothing includes and
# silently misses generate-gated deps. See vault/handbook/design/filelists.md.
# ==============================================================================

SHELL := /bin/bash

ifndef AREA
$(error AREA is not set. An RTL area Makefile must set AREA before including rtl/make/area.mk)
endif

RDS_ROOT ?= $(shell git rev-parse --show-toplevel)
export REPO_ROOT ?= $(RDS_ROOT)

MASTER_FILELIST := filelists/$(AREA)_all.f

# Recursive: rtl/common is flat but rtl/amba nests by protocol (axi4/, apb/...),
# so a plain $(wildcard *.sv) would report zero modules for half the areas.
SV_FILES        := $(shell find . -name '*.sv' -not -path './lint_reports/*' | sort)
SV_COUNT        := $(words $(SV_FILES))

LINT_DIR      := lint_reports
VERILATOR_DIR := $(LINT_DIR)/verilator
VERIBLE_DIR   := $(LINT_DIR)/verible
YOSYS_DIR     := $(LINT_DIR)/yosys

# EXTRA_INCLUDES lets an area add its own -I/-y without a hand-written file.
EXTRA_INCLUDES  ?=
INCLUDES        := -I$(RDS_ROOT)/rtl/amba/includes $(EXTRA_INCLUDES)

# Module search paths, used ONLY by the per-file glob targets below. The
# authoritative `verilator` target never uses them: a search path resolves a
# dependency the filelist forgot, which is exactly the failure --check exists to
# catch. For a single-file spot check it is the difference between useful output
# and a wall of "cannot find module".
SEARCH_DIRS     := -y . -y $(RDS_ROOT)/rtl/common -y $(RDS_ROOT)/rtl/math \
                   -y $(RDS_ROOT)/rtl/cdc -y $(RDS_ROOT)/rtl/amba/gaxi \
                   -y $(RDS_ROOT)/rtl/amba/shared
VERILATOR       := verilator
VERILATOR_FLAGS := --lint-only -Wall -Wno-TIMESCALEMOD -Wno-fatal $(INCLUDES)
VERIBLE         := verible-verilog-lint
VERIBLE_FLAGS   := --rules_config_search --rules=-parameter-name-style,-line-length

GREEN  := \033[0;32m
RED    := \033[0;31m
YELLOW := \033[0;33m
RESET  := \033[0m

.DEFAULT_GOAL := help

.PHONY: verilator
verilator: ## Verilator lint over the area's master filelist
	@if [ ! -f $(MASTER_FILELIST) ]; then \
	    echo -e "$(YELLOW)SKIP $(AREA): no $(MASTER_FILELIST)$(RESET)"; exit 0; \
	fi
	@mkdir -p $(VERILATOR_DIR)
	@echo "=== $(AREA): Verilator lint ($(SV_COUNT) files) ==="
	@if $(VERILATOR) $(VERILATOR_FLAGS) -f $(MASTER_FILELIST) > $(VERILATOR_DIR)/$(AREA)_all.log 2>&1; then \
	    echo -e "$(GREEN)PASS $(AREA): Verilator lint$(RESET)"; \
	else \
	    echo -e "$(RED)FAIL $(AREA): Verilator lint$(RESET)"; \
	    tail -30 $(VERILATOR_DIR)/$(AREA)_all.log; \
	    exit 1; \
	fi

.PHONY: verible
verible: ## Verible style lint, file by file
	@# ONE shell for the whole recipe: an `exit 0` on its own recipe line only
	@# leaves that line's subshell, so the guard used to print "not installed"
	@# and then run the loop anyway.
	@if ! command -v $(VERIBLE) >/dev/null 2>&1; then \
	    echo -e "$(YELLOW)SKIP $(AREA): $(VERIBLE) not installed$(RESET)"; \
	else \
	    mkdir -p $(VERIBLE_DIR); \
	    echo "=== $(AREA): Verible lint ($(SV_COUNT) files) ==="; \
	    fail=0; for f in $(SV_FILES); do \
	        $(VERIBLE) $(VERIBLE_FLAGS) $$f > $(VERIBLE_DIR)/$$(basename $$f .sv).log 2>&1 || fail=$$((fail+1)); \
	    done; \
	    if [ $$fail -eq 0 ]; then echo -e "$(GREEN)PASS $(AREA): Verible$(RESET)"; \
	    else echo -e "$(YELLOW)$(AREA): $$fail file(s) with Verible findings -- see $(VERIBLE_DIR)/$(RESET)"; fi; \
	fi

.PHONY: yosys
yosys: ## Yosys elaboration check (no generic flow -- see formal/)
	@echo -e "$(YELLOW)SKIP $(AREA): no generic yosys flow; per-module proofs live in formal/$(RESET)"

# Per-category lint by glob: `make verilator-counter` lints every .sv whose PATH
# contains "counter", which covers a flat area (common/counter*.sv) and a nested
# one (amba/axi4/*.sv) with one rule. Replaces the hand-written
# verilator-counters / verilator-arbiters / verilator-axi4 / ... targets.
#
# INFORMATIONAL, and it does not gate. Files are linted one at a time, so a
# module that imports a package cannot resolve it: package compile ORDER is real
# (amba's apb5_pkg imports apb_pkg) and only the area's master filelist encodes
# it. The old hand-written targets ended every line with `|| true` for the same
# reason. `make verilator` over the filelist is the authoritative check; this is
# for looking at one corner while you work on it.
verilator-%:
	@mkdir -p $(VERILATOR_DIR)
	@files=$$(find . -name '*.sv' -path "*$**" -not -path './lint_reports/*' | sort); \
	if [ -z "$$files" ]; then echo -e "$(YELLOW)$(AREA): no .sv path matches '$*'$(RESET)"; exit 0; fi; \
	n=$$(echo "$$files" | wc -l); echo "=== $(AREA): Verilator on $$n file(s) matching '$*' (informational) ==="; \
	bad=0; for f in $$files; do \
	    if ! $(VERILATOR) $(VERILATOR_FLAGS) $(SEARCH_DIRS) $$f \
	         > $(VERILATOR_DIR)/$$(basename $$f .sv).log 2>&1; then bad=$$((bad+1)); fi; \
	done; \
	if [ $$bad -eq 0 ]; then echo -e "$(GREEN)clean: all $$n matched file(s)$(RESET)"; \
	else \
	    echo -e "$(YELLOW)$$bad of $$n file(s) have findings -- logs in $(VERILATOR_DIR)/$(RESET)"; \
	    echo    "  standalone lint cannot resolve package imports; run 'make verilator' for the real check"; \
	fi

.PHONY: lint-all
lint-all: verilator verible ## Every lint tool available for this area

.PHONY: status
status: ## Module and filelist counts for this area
	@echo "=== $(AREA) ==="
	@echo "  modules:    $(SV_COUNT)"
	@echo "  filelists:  $(words $(wildcard filelists/*.f))"
	@echo "  master:     $(MASTER_FILELIST)$(if $(wildcard $(MASTER_FILELIST)),, [MISSING])"

.PHONY: clean-all
clean-all: ## Remove this area's lint artifacts
	@rm -rf $(LINT_DIR)
	@echo "$(AREA): lint artifacts cleaned"

.PHONY: lint
lint: lint-all

.PHONY: clean
clean: clean-all

.PHONY: all
all: lint-all

.PHONY: help
help: ## Show the targets this area understands
	@echo "$(AREA) (generic area Makefile -- rtl/make/area.mk)"
	@echo "  make verilator | verible | yosys | lint-all | status | clean-all"
	@echo "  sources come from $(MASTER_FILELIST)"
