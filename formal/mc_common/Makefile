# ==============================================================================
# Formal Verification - mc_common: the memory-controller family's shared FUBs
# ==============================================================================
# The blocks in projects/components/mem-ctrl-ip/common-ip/rtl/fub/ (mc_*) that
# pumice, scoria and andesite all instantiate. These proofs started life as
# formal/pumice/<block> (2026-09-28) and moved here 2026-10-19: 23cfc54e9 and
# its follow-ups extracted the FUBs into common-ip as mc_*, and the pumice
# (and the duplicate scoria) proofs had pointed at deleted files ever since.
# pumice was the reference logic for the extraction and scoria adopted it with
# zero parameterization, so one proof per mc_* block covers all three rocks.
#
# EVERY proof here uses the sv2v-flatten flavour, not the direct
# `read -formal -sv` one: each module directory carries its own Makefile that
# runs sv2v first and the .sby reads the resulting _flat.v. That is why the
# dispatch below prefers a per-module Makefile: going straight to `sby` would
# skip the flatten and read a stale (or absent) _flat.v. Flats are built, not
# committed (.gitignore).
#
# Usage:
#   make prove-all      Prove all safety properties
#   make cover-all      Run all cover traces
#   make all            Prove + cover everything
#   make prove-<mod> / cover-<mod>   One module (full module name)
#   make clean          Remove generated artifacts
# ==============================================================================

SHELL := /bin/bash

.DEFAULT_GOAL := help

# DISCOVERED, not listed -- same reason as formal/cdc/Makefile: a hand-kept list
# silently drops a renamed module and the area still reports success.
MODULES := $(sort $(patsubst %/,%,$(dir $(wildcard */*.sby))))

.PHONY: help
help:
	@echo "================================================================================"
	@echo "Formal Verification - mc_common ($(words $(MODULES)) modules)"
	@echo "================================================================================"
	@echo ""
	@echo "  make prove-all             Prove ALL modules"
	@echo "  make cover-all             Cover ALL modules"
	@echo "  make all                   Prove + cover everything"
	@echo "  make prove-<module>        One module's prove (full module name)"
	@echo "  make cover-<module>        One module's cover"
	@echo "  make clean                 Remove all artifacts"
	@echo ""
	@echo "  Modules: $(MODULES)"
	@echo "================================================================================"

.PHONY: $(addprefix prove-,$(MODULES))
$(addprefix prove-,$(MODULES)): prove-%:
	@echo "=== Proving $* ==="
	@if [ -f $*/Makefile ]; then $(MAKE) -C $* prove; else cd $* && sby -f $*.sby prove; fi

.PHONY: $(addprefix cover-,$(MODULES))
$(addprefix cover-,$(MODULES)): cover-%:
	@echo "=== Cover $* ==="
	@if [ -f $*/Makefile ]; then $(MAKE) -C $* cover; else cd $* && sby -f $*.sby cover; fi

.PHONY: prove-all
prove-all: $(addprefix prove-,$(MODULES))
	@echo "=== All $(words $(MODULES)) mc_common proofs complete ==="

.PHONY: cover-all
cover-all: $(addprefix cover-,$(MODULES))
	@echo "=== All $(words $(MODULES)) mc_common covers complete ==="

.PHONY: all
all: prove-all cover-all

# The per-module Makefiles own the flat files; delegate so a renamed flat file
# is still removed by the rule that creates it.
.PHONY: clean
clean:
	@for m in $(MODULES); do \
	    if [ -f $$m/Makefile ]; then $(MAKE) -C $$m clean; \
	    else rm -rf $$m/$${m}_prove $$m/$${m}_cover 2>/dev/null; fi; \
	done
