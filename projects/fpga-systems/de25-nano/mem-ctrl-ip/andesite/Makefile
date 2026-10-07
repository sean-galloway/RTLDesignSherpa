#==============================================================================
# de25-nano/andesite -- area dispatcher
#==============================================================================
# One entry point for the whole component. Per-build work is delegated to the
# build's own Makefile (variables + the global make/fpga_flow.mk), so nothing
# here re-implements flow logic.
#
#   make                    this message
#   make bitstream          BUILD=andesite (default), BOARD=genesys2
#   make <target> BOARD=... any flow target against another registered board
#   make -C build-andesite help     the full per-build target list
#
# Why Genesys 2 for a de25-nano area: the DE25-Nano (Intel, LPDDR4) is the
# destination board but is not in hand. The Genesys 2 (Kintex-7, Vivado) is
# the timing/build vehicle: same controller, silicon-grade tool, so build and
# timing issues surface early. BOARD rides the shared registry
# (projects/fpga-systems/bin/boards/), so first silicon for the real board
# is a BOARD= switch plus its constraints -- not a new flow.
#
# Model after: Genesys2/scoria/Makefile (the two-build A/B shape collapses
# to a single build here; no LiteDRAM yardstick until there is a memory
# interface to compare).
#==============================================================================

SELF_DIR := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))
PYTHON   ?= python3

BUILDS   := andesite
BUILD    ?= andesite
BUILD_DIR = $(SELF_DIR)/build-$(BUILD)

BOARD    ?= genesys2

.DEFAULT_GOAL := help
.PHONY: help builds blocks-sim $(BUILDS)

help:
	@echo "andesite for the DE25-Nano (BUILD=$(BUILD), BOARD=$(BOARD))"
	@echo ""
	@echo "  The destination board is the DE25-Nano (Intel, LPDDR4); the"
	@echo "  initial build targets the Genesys 2 to shake out build and"
	@echo "  timing issues early (see README.md)."
	@echo ""
	@echo "  Builds:"
	@echo "    build-andesite/     andesite_core skeleton -- no PHY (by design)"
	@echo ""
	@echo "  Any build target:"
	@echo "    make bitstream              # BUILD=andesite by default"
	@echo "    make program lint sim utilization timing clean"
	@echo "    make -C build-andesite help # full per-build target list"
	@echo ""
	@echo "  Area-wide:"
	@echo "    make blocks-sim   Sim the shared rtl/ blocks (dv/tests)"
	@echo "    make builds       List builds"

builds:
	@for b in $(BUILDS); do echo "  $$b"; done

blocks-sim:
	@echo "[blocks-sim] $(SELF_DIR)/dv/tests"
	cd $(RDS_ROOT) && $(PYTHON) -m pytest $(SELF_DIR)/dv/tests -q
