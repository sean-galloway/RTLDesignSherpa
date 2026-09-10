#==============================================================================
# LiteDRAM apples-to-apples characterization harness -- the pumice build-perf
# harness with litedram_core behind the AXI port instead of pumice. All flow
# logic is in the global make/fpga_flow.mk; keep this file to variables only.
# `make help` lists targets.
#
#   make regen        regenerate litedram_core WITH its BIOS (./regen.sh --bios)
#   make lint         verilator --lint-only of char_engine_harness
#   make bitstream    Vivado synth/impl/bitgen (tcl/build_all.tcl)
#   make program      flash the board (JTAG serial from the board registry)
#   make host-litedram_char ARGS="--port /dev/ttyUSB1 --char"
#==============================================================================

SELF_DIR  := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT  := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git -C $(SELF_DIR) rev-parse --show-toplevel))
export REPO_ROOT := $(RDS_ROOT)

# Roots the filelist closure resolves against (converters -> uart bridge etc.).
export CONVERTERS_ROOT ?= $(RDS_ROOT)/projects/components/converters

FLOW      := litedram_char
TOP       := litedram_char_top
FILELIST  := $(SELF_DIR)/rtl/filelists/litedram_char_board.f

# Lint elaborates the harness, not the pin-level top: litedram_core.v is
# Xilinx-primitive soup that only Vivado can read. Target-specific variables
# reach lint's prerequisites (flat-filelist, lint-decl-order) as well.
lint flat-filelist lint-decl-order: TOP      := char_engine_harness
lint flat-filelist lint-decl-order: FILELIST := $(SELF_DIR)/rtl/filelists/litedram_char_harness.f

# The generated bridge must match its .toml before synthesis (build-perf's
# pattern): the same bridge_ddr2_char_axil is what keeps the address map
# identical between the two flows.
PREBUILD := bash $(RDS_ROOT)/projects/fpga-systems/NexysA7/pumice/ddr2_char_framework/bin/regen_bridges.sh

include $(RDS_ROOT)/make/fpga_flow.mk

.PHONY: regen
regen:              ## Regenerate litedram_core WITH bios (./regen.sh --bios)
	cd $(SELF_DIR) && ./regen.sh --bios
