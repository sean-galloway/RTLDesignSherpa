# ==============================================================================
# Formal Verification - Retro Legacy Blocks (projects/components/retro_legacy_blocks)
# ==============================================================================
# Usage:
#   make prove-all             Prove ALL blocks
#   make cover-all             Cover ALL blocks
#   make all                   Prove + cover everything
#   make prove-<block>         One block (e.g. make prove-rtc_config_regs)
#   make clean                 Remove generated artifacts
#
# Each block is self-contained: its Makefile flattens the current RTL via sv2v
# before sby reads the plain Verilog. This aggregator just delegates.
#
# Raised by RLB-010: this area did not exist, and the RTC_STATUS W1C strobe and
# the seconds-read latch alignment were guarded only by the DV suite after the
# in-module SVA was removed in c67e9c31a (no-assertions-in-rtl is a standing
# rule; properties live here instead).
# ==============================================================================

SHELL := /bin/bash
.DEFAULT_GOAL := help

MODULES := rtc_config_regs

define RUN
	$(MAKE) -C $(1) $(2)
endef

.PHONY: help all prove-all cover-all clean \
	$(addprefix prove-,$(MODULES)) $(addprefix cover-,$(MODULES))

help:
	@echo "================================================================================"
	@echo "Formal Verification - Retro Legacy Blocks ($(words $(MODULES)) module(s))"
	@echo "================================================================================"
	@echo ""
	@echo "  make prove-all             Prove ALL blocks"
	@echo "  make cover-all             Cover ALL blocks"
	@echo "  make all                   Prove + cover everything"
	@echo "  make prove-<block>         One block (e.g. prove-rtc_config_regs)"
	@echo "  make clean                 Remove artifacts"
	@echo ""
	@echo "Modules: $(MODULES)"

$(addprefix prove-,$(MODULES)): prove-%:
	@echo "=== prove $* ==="
	@$(call RUN,$*,prove)

$(addprefix cover-,$(MODULES)): cover-%:
	@echo "=== cover $* ==="
	@$(call RUN,$*,cover)

prove-all: $(addprefix prove-,$(MODULES))
	@echo "=== RLB: $(words $(MODULES)) proof(s) complete ==="

cover-all: $(addprefix cover-,$(MODULES))
	@echo "=== RLB: $(words $(MODULES)) cover run(s) complete ==="

all: prove-all cover-all

clean:
	@for m in $(MODULES); do $(MAKE) -C $$m clean; done
