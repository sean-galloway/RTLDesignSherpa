# ==============================================================================
# Formal Verification - scoria DDR3/LPDDR3 memory controller
# ==============================================================================
# The blocks here are the ones where a wrong answer damages a DEVICE rather than
# a measurement, or where the invariant is one simulation structurally cannot
# observe. scoria's first entry is the command arbiter, and it earned its place
# twice over: it carries the fix for scoria BUG-001 (rank-global tRRD/tFAW
# windows checked two pipeline stages before the fire), which simulation could
# only show on 3 seeds, and proving it found BUG-002 -- the same shape on the
# tZQCS window -- which simulation could not reproduce at all, in 10 alignments.
#
# EVERY scoria proof uses the sv2v-flatten flavour, not the direct
# `read -formal -sv` one, for the same reason pumice does: yosys cannot parse
# the package. So each module directory carries its own Makefile that runs sv2v
# first and the .sby reads the resulting _flat.v. That is why the dispatch below
# prefers a per-module Makefile -- going straight to `sby` would skip the
# flatten and read a stale (or absent) _flat.v.
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

# DISCOVERED, not listed -- a hand-kept list silently drops a renamed module
# and the area still reports success.
MODULES := $(sort $(patsubst %/,%,$(dir $(wildcard */*.sby))))

.PHONY: help
help:
	@echo "================================================================================"
	@echo "Formal Verification - scoria ($(words $(MODULES)) modules)"
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
	@echo "=== All $(words $(MODULES)) scoria proofs complete ==="

.PHONY: cover-all
cover-all: $(addprefix cover-,$(MODULES))
	@echo "=== All $(words $(MODULES)) scoria covers complete ==="

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
