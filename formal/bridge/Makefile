# ==============================================================================
# Formal Verification - Bridge (projects/components/fabric-gen-ip/bridge)
# ==============================================================================
# Two kinds of collateral live here, and they are not the same thing:
#
#   bridge_cam/       A DUT proof: the RTL is in [files], assumptions on inputs,
#                     assertions on outputs.
#   bridge_1x2_rd/    A PROTOCOL MODEL with no DUT -- every port is an assumption
#                     and the assertions check the AXI4 rules and the decode
#                     constraints against each other. It passes in under a second
#                     and says nothing about the generated bridge RTL. Kept for
#                     its cover traces; do not read its PASS as bridge coverage.
#                     (Moved from the area root 2026-09-29 so its work dirs and
#                     status.sqlite stop landing beside the Makefile, where
#                     bin/formal_status.py read them as broken tasks.)
#
# Both are DISCOVERED as <dir>/<dir>.sby so a new proof cannot be added-but-unrun
# (tooling TASK-018, 2026-09-29).
#
# Usage:
#   make prove-all      Prove everything discovered
#   make cover-all      Cover traces for the same
#   make all            Prove + cover everything
#   make prove-<mod> / cover-<mod>   One task (full directory name)
#   make clean          Remove generated artifacts
# ==============================================================================

SHELL := /bin/bash

.DEFAULT_GOAL := help

# <dir>/<dir>.sby only: sby writes a config.sby into every work directory it
# creates, so a bare */*.sby would also pick up bridge_1x2_rd_prove/ (it did).
MODULES := $(sort $(foreach d,$(patsubst %/,%,$(dir $(wildcard */*.sby))),$(if $(wildcard $d/$d.sby),$d)))

.PHONY: help
help:
	@echo "================================================================================"
	@echo "Formal Verification - Bridge ($(words $(MODULES)) tasks; bridge_1x2_rd is a DUT-less model)"
	@echo "================================================================================"
	@echo ""
	@echo "  make prove-all             Prove ALL"
	@echo "  make cover-all             Cover ALL"
	@echo "  make all                   Prove + cover everything"
	@echo "  make prove-<module>        One task's prove (full directory name)"
	@echo "  make cover-<module>        One task's cover"
	@echo "  make clean                 Remove all artifacts"
	@echo ""
	@echo "  Tasks: $(MODULES)"
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
	@echo "=== All $(words $(MODULES)) bridge proofs complete ==="

.PHONY: cover-all
cover-all: $(addprefix cover-,$(MODULES))
	@echo "=== All bridge covers complete ==="

.PHONY: all
all: prove-all cover-all

.PHONY: clean
clean:
	@for m in $(MODULES); do rm -rf $$m/$${m}_prove $$m/$${m}_cover; done
