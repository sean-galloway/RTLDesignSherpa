# ==============================================================================
# build-axi5 -- bridge stress model, AXI5 device under test (bridge_bs_axi5)
# ==============================================================================
#   make bitstream     synth + impl + bitstream + reports (fpga/ under this dir)
#   make program       load it on the Genesys 2 (BOARD=genesys2)
#   make lint          Verilator lint of bs_genesys2_top for this build
# Everything else: make help (make/fpga_flow.mk). The PREBUILD regenerates the
# bridges, regblocks and harness from their sources first (bin/regen.sh).
# ==============================================================================
SELF_DIR := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git -C $(SELF_DIR) rev-parse --show-toplevel))
AREA     := $(abspath $(SELF_DIR)/..)

export CONVERTERS_ROOT ?= $(RDS_ROOT)/projects/components/utility-ip/converters
export MISC_ROOT       ?= $(RDS_ROOT)/projects/components/utility-ip/misc
export XILINX_VIVADO   ?= /tools/Xilinx/2025.1/Vivado
VIVADO   ?= $(XILINX_VIVADO)/bin/vivado

export FLOW       := bs_axi5
export BOARD      ?= genesys2
export BS_HARNESS := bs_harness_bridge_bs_axi5
TOP       := bs_genesys2_top
FILELIST  := $(AREA)/rtl/filelists/bs_genesys2_top_axi5.f
TCL_DIR   := $(AREA)/fpga/tcl
TCL_HELPERS := filelist_utils bs_xil_ip
export FPGA_CONSTRAINTS_DIR := $(AREA)/fpga/constraints
FPGA_DIR  := $(SELF_DIR)/fpga
BITSTREAM := $(FPGA_DIR)/bitstream/$(FLOW)_genesys2.bit
SIM_TESTS := $(AREA)/dv/tests
SEQ_DIR   := $(AREA)/bin
PREBUILD  := bash $(AREA)/bin/regen.sh
# Lint the harness this build synthesizes: Vivado gets BS_HARNESS as a define
# (fpga/tcl/create_project.tcl); without it here lint checks the default one.
LINT_DEFINES := +define+USE_ASYNC_RESET +define+BS_HARNESS=$(BS_HARNESS)

include $(RDS_ROOT)/make/fpga_flow.mk
