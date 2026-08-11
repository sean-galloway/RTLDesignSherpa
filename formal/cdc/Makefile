# ==============================================================================
# Formal Verification - CDC Building Blocks
# ==============================================================================
# Everything that crosses a clock domain lives in rtl/cdc/, and its formal
# collateral lives here - consolidated 2026-08-10 (the dirs existed since the
# CDC reorg, but no Makefile ran them: `make formal` never touched a CDC
# proof, and the stale formal/common twins were output debris that made the
# area look covered).
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

# All module directories with proofs (each holds <module>.sby)
MODULES = \
	bin2gray \
	cdc_handshake \
	cdc_synchronizer \
	counter_bingray \
	counter_johnson \
	fifo_async \
	gaxi_fifo_async \
	gaxi_skid_buffer_async \
	glitch_free_n_dff_arn \
	gray2bin \
	johnson2bin \
	sync_pulse

.PHONY: help
help:
	@echo "================================================================================"
	@echo "Formal Verification - CDC Building Blocks ($(words $(MODULES)) modules)"
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
	cd $* && sby -f $*.sby prove

.PHONY: $(addprefix cover-,$(MODULES))
$(addprefix cover-,$(MODULES)): cover-%:
	@echo "=== Cover $* ==="
	cd $* && sby -f $*.sby cover

.PHONY: prove-all
prove-all: $(addprefix prove-,$(MODULES))
	@echo "=== All $(words $(MODULES)) CDC proofs complete ==="

.PHONY: cover-all
cover-all: $(addprefix cover-,$(MODULES))
	@echo "=== All $(words $(MODULES)) CDC covers complete ==="

.PHONY: all
all: prove-all cover-all

.PHONY: clean
clean:
	@for m in $(MODULES); do \
		rm -rf $$m/$${m}_prove $$m/$${m}_cover 2>/dev/null; \
	done
