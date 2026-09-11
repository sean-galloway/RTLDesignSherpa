# ==============================================================================
# Formal Verification - Top Level
# ==============================================================================
#
# Usage:
#   make formal         Run all formal proofs (common + cdc + amba + converters
#                       + integ_common + stream + rapids)
#   make formal-common  Common building blocks only
#   make formal-cdc     CDC blocks only
#   make formal-amba    AMBA blocks (rtl/amba/**)
#   make formal-converters  Protocol converters (projects/components/converters)
#   make formal-bridge  Bridge AXI4 protocol only (requires SVA-AXI4-FVIP)
#   make formal-quick   Just counter_bin (fastest proof, ~seconds)
#   make clean          Remove all formal artifacts
# ==============================================================================

SHELL := /bin/bash

.DEFAULT_GOAL := help

.PHONY: help
help:
	@echo "================================================================================"
	@echo "Formal Verification - RTL Design Sherpa"
	@echo "================================================================================"
	@echo ""
	@echo "  make formal           Run ALL formal proofs"
	@echo "  make formal-rtl       Everything under repo-root rtl/ (common + cdc + amba)"
	@echo "  make formal-common    Common building blocks (arbiter, counter, FIFO)"
	@echo "  make formal-cdc       CDC blocks (rtl/cdc: async FIFOs, gray, handshakes)"
	@echo "  make formal-amba      AMBA blocks (rtl/amba/**)"
	@echo "  make formal-converters  Protocol converters"
	@echo "  make formal-stream    STREAM DMA blocks (dmas/stream)"
	@echo "  make formal-rapids    RAPIDS DMA blocks (dmas/rapids *_beats)"
	@echo "  make formal-dma       STREAM + RAPIDS"
	@echo "  make formal-bridge    Bridge AXI4 protocol (requires SVA-AXI4-FVIP submodule)"
	@echo "  make formal-quick     Quick check: counter_bin only (~seconds)"
	@echo ""
	@echo "  make check-tools      Verify formal tools are installed"
	@echo "  make clean            Remove all formal artifacts"
	@echo "================================================================================"

.PHONY: check-tools
check-tools:
	@echo "Checking formal verification tools..."
	@which yosys > /dev/null 2>&1 && echo "  yosys:     $$(yosys --version 2>/dev/null | head -1)" || echo "  yosys:     NOT FOUND"
	@which sby > /dev/null 2>&1 && echo "  sby:       $$(sby --version 2>/dev/null | head -1)" || echo "  sby:       NOT FOUND (install: pip install sby)"
	@which boolector > /dev/null 2>&1 && echo "  boolector: found" || echo "  boolector: NOT FOUND (install: see docs/FORMAL_VERIFICATION_GUIDE.md)"
	@which z3 > /dev/null 2>&1 && echo "  z3:        found" || echo "  z3:        NOT FOUND (optional fallback solver)"

# formal-amba and formal-converters were MISSING from this list until
# 2026-09-11: `make formal` ran neither, so ninety task directories had no
# entry point and nobody noticed twelve flat files drifting from their RTL.
.PHONY: formal
formal: formal-rtl formal-converters formal-stream formal-rapids

# Everything whose RTL lives in repo-root rtl/.
.PHONY: formal-rtl
formal-rtl: formal-common formal-cdc formal-amba
	@echo "================================================================================"
	@echo "All formal proofs complete"
	@echo "================================================================================"

.PHONY: formal-common
formal-common:
	$(MAKE) -C common all

.PHONY: formal-cdc
formal-cdc:
	$(MAKE) -C cdc all

.PHONY: formal-amba
formal-amba:
	$(MAKE) -C amba all

.PHONY: formal-converters
formal-converters:
	@for d in converters/*/; do \
	    if [ -f $$d/Makefile ]; then $(MAKE) -C $$d all || exit 1; fi; \
	done

.PHONY: formal-stream
formal-stream:
	$(MAKE) -C stream prove-all

.PHONY: formal-rapids
formal-rapids:
	$(MAKE) -C rapids prove-all

.PHONY: formal-dma
formal-dma: formal-stream formal-rapids

.PHONY: formal-bridge
formal-bridge:
	@if [ -d bridge ]; then \
		$(MAKE) -C bridge all; \
	else \
		echo "Bridge formal not yet set up. See docs/FORMAL_VERIFICATION_GUIDE.md"; \
	fi

.PHONY: formal-quick
formal-quick:
	$(MAKE) -C common prove-counter

.PHONY: clean
clean:
	$(MAKE) -C common clean
	$(MAKE) -C cdc clean
	$(MAKE) -C amba clean
	@if [ -d bridge ]; then $(MAKE) -C bridge clean 2>/dev/null; fi
