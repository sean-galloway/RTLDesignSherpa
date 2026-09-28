# ==============================================================================
# Formal Verification - pumice DDR2/LPDDR2 memory controller
# ==============================================================================
# pumice had ZERO formal coverage while 366 blocks elsewhere in the repo were
# proven. The blocks here are the ones where a wrong answer damages a device
# rather than a measurement, or where the invariant is one simulation
# structurally cannot observe.
#
# EVERY pumice proof uses the sv2v-flatten flavour, not the direct
# `read -formal -sv` one. yosys cannot parse pumice_pkg.sv -- a multi-line
# `return` in a package function stops its Verilog frontend at pumice_pkg.sv:131
# -- so each module directory carries its own Makefile that runs sv2v first and
# the .sby reads the resulting _flat.v. That is why the dispatch below prefers a
# per-module Makefile: going straight to `sby` would skip the flatten and read a
# stale (or absent) _flat.v.
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
	@echo "Formal Verification - pumice ($(words $(MODULES)) modules)"
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
	@echo "=== All $(words $(MODULES)) pumice proofs complete ==="

.PHONY: cover-all
cover-all: $(addprefix cover-,$(MODULES))
	@echo "=== All $(words $(MODULES)) pumice covers complete ==="

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
