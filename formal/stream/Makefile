# ==============================================================================
# Formal Verification - STREAM DMA blocks (dmas/stream RTL)
# ==============================================================================
# Usage:
#   make prove-all             Prove ALL active blocks (excludes DEFERRED)
#   make cover-all             Cover ALL active blocks
#   make all                   Prove + cover everything
#   make prove-<block>         One block (e.g. make prove-scheduler)
#   make clean                 Remove generated artifacts
#
# Blocks come in two flavours, both handled by the dispatch rule below:
#   - Makefile-driven: sv2v flattens current RTL, then sby reads the flat.
#   - sby-only:        the <block>.sby reads the RTL directly (no flatten).
#
# DEFERRED blocks (yosys flatten collision / state space too large) are excluded
# from prove-all/cover-all but remain runnable individually, e.g.
#   make prove-stream_core
# ==============================================================================

SHELL := /bin/bash
.DEFAULT_GOAL := help

# Active blocks (prove PASS today)
MODULES := \
	apb4todescr \
	axi_read_engine \
	axi_write_engine \
	cmdrsp_router \
	datapath_rd_test \
	datapath_wr_test \
	descriptor_engine \
	monbus_axil_group \
	perf_profiler \
	scheduler \
	scheduler_group \
	scheduler_group_array \
	sram_controller \
	sram_controller_unit \
	stream_config_block \
	stream_alloc_ctrl \
	stream_drain_ctrl \
	stream_latency_bridge

# Deferred (excluded from *-all; still runnable via prove-<block>)
DEFERRED := stream_core stream_top_ch8

.PHONY: help all prove-all cover-all clean \
	$(addprefix prove-,$(MODULES) $(DEFERRED)) $(addprefix cover-,$(MODULES) $(DEFERRED))

help:
	@echo "================================================================================"
	@echo "Formal Verification - STREAM DMA blocks ($(words $(MODULES)) active, $(words $(DEFERRED)) deferred)"
	@echo "================================================================================"
	@echo ""
	@echo "  make prove-all             Prove ALL active blocks"
	@echo "  make cover-all             Cover ALL active blocks"
	@echo "  make all                   Prove + cover everything"
	@echo "  make prove-<block>         One block (e.g. prove-scheduler)"
	@echo "  make clean                 Remove artifacts"
	@echo ""
	@echo "  Active:   $(MODULES)"
	@echo "  Deferred: $(DEFERRED)"
	@echo "================================================================================"

# Dispatch: Makefile-driven block -> delegate; else run sby on <block>.sby directly.
define RUN
	if [ -f "$(1)/Makefile" ]; then $(MAKE) -C "$(1)" $(2); \
	else ( cd "$(1)" && sby -f "$(1).sby" $(2) ); fi
endef

$(addprefix prove-,$(MODULES) $(DEFERRED)): prove-%:
	@echo "=== prove $* ==="
	@$(call RUN,$*,prove)

$(addprefix cover-,$(MODULES) $(DEFERRED)): cover-%:
	@echo "=== cover $* ==="
	@$(call RUN,$*,cover)

prove-all: $(addprefix prove-,$(MODULES))
	@echo "=== STREAM: $(words $(MODULES)) proofs complete ==="

cover-all: $(addprefix cover-,$(MODULES))
	@echo "=== STREAM: $(words $(MODULES)) covers complete ==="

all: prove-all cover-all

clean:
	@for m in $(MODULES) $(DEFERRED); do \
		if [ -f "$$m/Makefile" ]; then $(MAKE) -C "$$m" clean >/dev/null 2>&1 || true; \
		else rm -rf "$$m/$${m}_prove" "$$m/$${m}_cover" "$$m/$$m" 2>/dev/null || true; fi; \
	done
	@echo "=== STREAM formal artifacts cleaned ==="
