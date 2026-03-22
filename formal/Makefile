# ==============================================================================
# Formal Verification - Top Level
# ==============================================================================
#
# Usage:
#   make formal         Run all formal proofs (common + bridge)
#   make formal-common  Common building blocks only
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
	@echo "  make formal-common    Common building blocks (arbiter, counter, FIFO)"
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

.PHONY: formal
formal: formal-common
	@echo "================================================================================"
	@echo "All formal proofs complete"
	@echo "================================================================================"

.PHONY: formal-common
formal-common:
	$(MAKE) -C common all

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
	@if [ -d bridge ]; then $(MAKE) -C bridge clean 2>/dev/null; fi
