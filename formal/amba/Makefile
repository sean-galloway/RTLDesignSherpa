# ==============================================================================
# Formal Verification - AMBA blocks (rtl/amba/**)
# ==============================================================================
# There was no Makefile here at all until 2026-09-11, and no `formal-amba`
# target at the top level, so `make formal` never ran a single AMBA proof:
# sixty task directories with no entry point. A proof nobody runs is a proof
# nobody notices breaking, which is how twelve flat files drifted from their
# RTL and two monitor proofs sat un-elaborable.
#
# MODULES IS DISCOVERED, NOT LISTED. formal/common/Makefile hardcoded its
# list and ran 34 of its 222 proofs; a list that must be edited by hand is a
# list that goes stale the first time someone forgets. Adding a task
# directory with a .sby in it is all it takes to be covered here.
#
# Two flows live side by side:
#   * flatten flow - the task has its own Makefile (sv2v -> plain Verilog).
#     Needed wherever yosys's own SystemVerilog frontend cannot read the RTL:
#     package-typed ports, casts, unpacked array ports, elaboration $error.
#   * direct flow  - the .sby reads the SystemVerilog itself.
# `make prove-<task>` does the right thing for either.
#
# Usage:
#   make all            Every task, both flows
#   make prove-all / cover-all
#   make prove-<task> / cover-<task>
#   make list           Show what was discovered, and which flow each uses
#   make clean
# ==============================================================================

SHELL := /bin/bash
.DEFAULT_GOAL := help

# Every directory holding a .sby, derived from the tree.
MODULES := $(sort $(patsubst %/,%,$(dir $(wildcard */*.sby))))
# Those that carry their own Makefile use the sv2v flatten flow.
FLATTEN := $(sort $(patsubst %/,%,$(dir $(wildcard */Makefile))))
DIRECT  := $(filter-out $(FLATTEN),$(MODULES))

.PHONY: help
help:
	@echo "================================================================================"
	@echo "Formal Verification - AMBA ($(words $(MODULES)) tasks: $(words $(FLATTEN)) flatten, $(words $(DIRECT)) direct)"
	@echo "================================================================================"
	@echo "  make all                Prove + cover every task"
	@echo "  make prove-all          Prove every task"
	@echo "  make cover-all          Cover every task"
	@echo "  make prove-<task>       One task"
	@echo "  make list               What was discovered, and each task's flow"
	@echo "  make clean              Remove artifacts"
	@echo "================================================================================"

.PHONY: list
list:
	@echo "flatten flow ($(words $(FLATTEN))):"; for m in $(FLATTEN); do echo "    $$m"; done
	@echo "direct flow  ($(words $(DIRECT))):"; for m in $(DIRECT); do echo "    $$m"; done

# A task with its own Makefile knows how to build its flat file first.
.PHONY: $(addprefix prove-,$(MODULES))
$(addprefix prove-,$(MODULES)): prove-%:
	@echo "=== prove $* ==="
	@if [ -f $*/Makefile ]; then $(MAKE) -C $* prove; else cd $* && sby -f $*.sby prove; fi

.PHONY: $(addprefix cover-,$(MODULES))
$(addprefix cover-,$(MODULES)): cover-%:
	@echo "=== cover $* ==="
	@if [ -f $*/Makefile ]; then $(MAKE) -C $* cover; else cd $* && sby -f $*.sby cover; fi

.PHONY: prove-all cover-all all
prove-all: $(addprefix prove-,$(MODULES))
cover-all: $(addprefix cover-,$(MODULES))
all: prove-all cover-all

# clean removes sby OUTPUT only. The *_flat.v files are TRACKED (20 of them
# here), so wiping them area-wide would show up as twenty deleted files in
# git and invite someone to commit the deletion. `make distclean` is the
# opt-in that also drops them; a plain `make` regenerates any that are gone.
.PHONY: clean
clean:
	@for m in $(MODULES); do \
	    rm -rf $$m/$${m}_prove $$m/$${m}_cover $$m/$${m}_prove_deep \
	           $$m/$${m}_cover_deep $$m/$$m; \
	done
	@echo "amba: sby output removed (flat files kept -- see distclean)"

.PHONY: distclean
distclean: clean
	@for m in $(MODULES); do rm -f $$m/*_flat.v; done
	@echo "amba: flattened Verilog removed too; 'make' regenerates it"
