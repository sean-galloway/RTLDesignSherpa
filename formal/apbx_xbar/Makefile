# ==============================================================================
# Formal Verification - APB crossbar family (projects/components/fabric-gen-ip/apbx-xbar)
# ==============================================================================
# Five generated fixed-configuration crossbars, one proof directory each. This
# Makefile did not exist until 2026-09-29 (tooling TASK-018): the five proofs
# passed, and `make formal` never ran them, because nothing here gave the
# top-level formal/Makefile an entry point. A proof nobody runs reports nothing
# when the RTL moves underneath it.
#
# Usage:
#   make prove-all      Prove all configurations
#   make cover-all      Run all cover traces
#   make all            Prove + cover everything
#   make prove-<cfg> / cover-<cfg>   One configuration (full directory name)
#   make clean          Remove generated artifacts
# ==============================================================================

SHELL := /bin/bash

.DEFAULT_GOAL := help

# DISCOVERED, not listed (same pattern as formal/cdc/Makefile): every directory
# holding a .sby is covered, so a new configuration cannot be added-but-unrun.
# <dir>/<dir>.sby only: sby writes a config.sby into every work directory it
# creates, so a bare */*.sby would pick up any stray top-level run.
MODULES := $(sort $(foreach d,$(patsubst %/,%,$(dir $(wildcard */*.sby))),$(if $(wildcard $d/$d.sby),$d)))

.PHONY: help
help:
	@echo "================================================================================"
	@echo "Formal Verification - APB crossbar family ($(words $(MODULES)) configurations)"
	@echo "================================================================================"
	@echo ""
	@echo "  make prove-all             Prove ALL configurations"
	@echo "  make cover-all             Cover ALL configurations"
	@echo "  make all                   Prove + cover everything"
	@echo "  make prove-<cfg>           One configuration's prove (full directory name)"
	@echo "  make cover-<cfg>           One configuration's cover"
	@echo "  make clean                 Remove all artifacts"
	@echo ""
	@echo "  Configurations: $(MODULES)"
	@echo "================================================================================"

.PHONY: $(addprefix prove-,$(MODULES))
$(addprefix prove-,$(MODULES)): prove-%:
	@echo "=== Proving $* ==="
	@cd $* && sby -f $*.sby prove

.PHONY: $(addprefix cover-,$(MODULES))
$(addprefix cover-,$(MODULES)): cover-%:
	@echo "=== Cover $* ==="
	@cd $* && sby -f $*.sby cover

.PHONY: prove-all
prove-all: $(addprefix prove-,$(MODULES))
	@echo "=== All $(words $(MODULES)) apbx_xbar proofs complete ==="

.PHONY: cover-all
cover-all: $(addprefix cover-,$(MODULES))
	@echo "=== All $(words $(MODULES)) apbx_xbar covers complete ==="

.PHONY: all
all: prove-all cover-all

.PHONY: clean
clean:
	@for m in $(MODULES); do rm -rf $$m/$${m}_prove $$m/$${m}_cover; done
