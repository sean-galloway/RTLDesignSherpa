# ==============================================================================
# Formal Verification - Bridge AXI4 Protocol Compliance
# ==============================================================================
# Verifies AXI4 protocol properties on bridge external interfaces.
# Uses blackbox approach: assumes well-formed inputs, asserts outputs comply.
#
# Usage:
#   make prove-all      Prove all bridge configs
#   make cover-all      Cover traces for all configs
#   make all            Prove + cover everything
#   make clean          Remove generated artifacts
# ==============================================================================

SHELL := /bin/bash

.DEFAULT_GOAL := help

.PHONY: help
help:
	@echo "================================================================================"
	@echo "Formal Verification - Bridge Protocol Compliance"
	@echo "================================================================================"
	@echo ""
	@echo "PROVE:"
	@echo "  make prove-1x2-rd     bridge_1x2_rd (1 master, 2 slaves, read-only)"
	@echo "  make prove-all        ALL bridge configs"
	@echo ""
	@echo "COVER:"
	@echo "  make cover-1x2-rd     Cover traces for 1x2 read bridge"
	@echo "  make cover-all        ALL bridge configs"
	@echo ""
	@echo "  make all              Prove + cover everything"
	@echo "  make clean            Remove all artifacts"
	@echo "================================================================================"

.PHONY: prove-1x2-rd
prove-1x2-rd:
	@echo "=== Proving bridge_1x2_rd protocol compliance ==="
	sby -f bridge_1x2_rd.sby prove

.PHONY: cover-1x2-rd
cover-1x2-rd:
	@echo "=== Cover bridge_1x2_rd ==="
	sby -f bridge_1x2_rd.sby cover

.PHONY: prove-all
prove-all: prove-1x2-rd
	@echo "=== All bridge proofs complete ==="

.PHONY: cover-all
cover-all: cover-1x2-rd
	@echo "=== All bridge covers complete ==="

.PHONY: all
all: prove-all cover-all

.PHONY: clean
clean:
	rm -rf bridge_1x2_rd_prove bridge_1x2_rd_cover
