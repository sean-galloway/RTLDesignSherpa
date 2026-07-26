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
# rtl/common and rtl/amba keep their own hand-written Makefiles: they carry
# per-category targets (verilator-counters, verilator-axi4, ...) that come from
# knowing the area's structure, which a generic body cannot invent. They expose
# the same target NAMES as this file, which is what lets rtl/Makefile dispatch
# one target across every area without caring which kind it is.
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
SV_FILES        := $(wildcard *.sv)
SV_COUNT        := $(words $(SV_FILES))

LINT_DIR      := lint_reports
VERILATOR_DIR := $(LINT_DIR)/verilator
VERIBLE_DIR   := $(LINT_DIR)/verible
YOSYS_DIR     := $(LINT_DIR)/yosys

INCLUDES        := -I$(RDS_ROOT)/rtl/amba/includes
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
	@command -v $(VERIBLE) >/dev/null 2>&1 || { \
	    echo -e "$(YELLOW)SKIP $(AREA): $(VERIBLE) not installed$(RESET)"; exit 0; }
	@mkdir -p $(VERIBLE_DIR)
	@echo "=== $(AREA): Verible lint ($(SV_COUNT) files) ==="
	@fail=0; for f in $(SV_FILES); do \
	    $(VERIBLE) $(VERIBLE_FLAGS) $$f > $(VERIBLE_DIR)/$$(basename $$f .sv).log 2>&1 || fail=$$((fail+1)); \
	done; \
	if [ $$fail -eq 0 ]; then echo -e "$(GREEN)PASS $(AREA): Verible$(RESET)"; \
	else echo -e "$(YELLOW)$(AREA): $$fail file(s) with Verible findings -- see $(VERIBLE_DIR)/$(RESET)"; fi

.PHONY: yosys
yosys: ## Yosys elaboration check
	@command -v yosys >/dev/null 2>&1 || { \
	    echo -e "$(YELLOW)SKIP $(AREA): yosys not installed$(RESET)"; exit 0; }
	@mkdir -p $(YOSYS_DIR)
	@echo "=== $(AREA): Yosys (not implemented generically -- needs a top per module) ==="
	@echo -e "$(YELLOW)SKIP $(AREA): no generic yosys flow; see formal/ for per-module proofs$(RESET)"

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
