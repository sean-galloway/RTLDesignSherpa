# ==============================================================================
# Formal Verification - RAPIDS DMA blocks (dmas/rapids *_beats RTL)
# ==============================================================================
# Usage:
#   make prove-all             Prove ALL blocks
#   make cover-all             Cover ALL blocks
#   make all                   Prove + cover everything
#   make prove-<block>         One block (e.g. make prove-scheduler_beats)
#   make clean                 Remove generated artifacts
#
# Each block is self-contained: its Makefile flattens the current RTL via sv2v
# (make <block>_flat.v) before sby reads the plain Verilog. This aggregator just
# delegates to each block's own Makefile.
# ==============================================================================

SHELL := /bin/bash
.DEFAULT_GOAL := help

MODULES := \
	alloc_ctrl_beats \
	axi_read_engine_beats \
	axi_write_engine_beats \
	descriptor_engine_beats \
	drain_ctrl_beats \
	latency_bridge_beats \
	scheduler_beats \
	snk_sram_controller_beats \
	snk_sram_controller_unit_beats \
	src_sram_controller_beats \
	src_sram_controller_unit_beats

.PHONY: help all prove-all cover-all clean \
	$(addprefix prove-,$(MODULES)) $(addprefix cover-,$(MODULES))

help:
	@echo "================================================================================"
	@echo "Formal Verification - RAPIDS DMA blocks ($(words $(MODULES)) modules)"
	@echo "================================================================================"
	@echo ""
	@echo "  make prove-all             Prove ALL blocks"
	@echo "  make cover-all             Cover ALL blocks"
	@echo "  make all                   Prove + cover everything"
	@echo "  make prove-<block>         One block (e.g. prove-scheduler_beats)"
	@echo "  make clean                 Remove artifacts"
	@echo ""
	@echo "  Blocks: $(MODULES)"
	@echo "================================================================================"

# Dispatch: Makefile-driven block -> delegate; else run sby on <block>.sby directly.
define RUN
	if [ -f "$(1)/Makefile" ]; then $(MAKE) -C "$(1)" $(2); \
	else ( cd "$(1)" && sby -f "$(1).sby" $(2) ); fi
endef

$(addprefix prove-,$(MODULES)): prove-%:
	@echo "=== prove $* ==="
	@$(call RUN,$*,prove)

$(addprefix cover-,$(MODULES)): cover-%:
	@echo "=== cover $* ==="
	@$(call RUN,$*,cover)

prove-all: $(addprefix prove-,$(MODULES))
	@echo "=== RAPIDS: $(words $(MODULES)) proofs complete ==="

cover-all: $(addprefix cover-,$(MODULES))
	@echo "=== RAPIDS: $(words $(MODULES)) covers complete ==="

all: prove-all cover-all

clean:
	@for m in $(MODULES); do \
		if [ -f "$$m/Makefile" ]; then $(MAKE) -C "$$m" clean >/dev/null 2>&1 || true; \
		else rm -rf "$$m/$${m}_prove" "$$m/$${m}_cover" "$$m/$$m" 2>/dev/null || true; fi; \
	done
	@echo "=== RAPIDS formal artifacts cleaned ==="
