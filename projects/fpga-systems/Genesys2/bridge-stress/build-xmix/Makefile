# ==============================================================================
# build-xmix -- bridge stress model, mixed AXI3 / AXI4 / AXI5 build with
# third-party IP (bridge_bs_xmix): build-xil's board top with BS_XMIX (the
# xmix harness; its AXI3 bram port through an AXI Protocol Converter)
# ==============================================================================
#   make bitstream     synth + impl + bitstream + reports (fpga/ under this dir)
#   make program       load it on the Genesys 2 (BOARD=genesys2)
#   make lint          Verilator lint of bs_genesys2_xil_top (BS_XMIX), the IP as
#                      port stubs (bin/gen_xil_lint_stubs.py --xmix, after a synth)
# Everything else: make help (make/fpga_flow.mk). The PREBUILD regenerates the
# bridges, regblocks, harness and MIG project file from their sources first
# (bin/regen.sh); the Vivado project then creates the AMD/Xilinx IP
# (fpga/tcl/bs_xil_ip.tcl), which needs no license beyond Vivado's own.
# ==============================================================================
SELF_DIR := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git -C $(SELF_DIR) rev-parse --show-toplevel))
AREA     := $(abspath $(SELF_DIR)/..)

export CONVERTERS_ROOT ?= $(RDS_ROOT)/projects/components/utility-ip/converters
export MISC_ROOT       ?= $(RDS_ROOT)/projects/components/utility-ip/misc
export XILINX_VIVADO   ?= /tools/Xilinx/2025.1/Vivado
VIVADO   ?= $(XILINX_VIVADO)/bin/vivado

export FLOW       := bs_xmix
export BOARD      ?= genesys2
export BS_HARNESS := bs_harness_bridge_bs_xmix
TOP       := bs_genesys2_xil_top
export BS_TOP := $(TOP)
export BS_XDC := bs_genesys2_xil_top.xdc
export BS_XIL_IP := 1
export BS_XMIX   := 1
FILELIST  := $(AREA)/rtl/filelists/bs_genesys2_top_xmix.f
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
LINT_DEFINES := +define+USE_ASYNC_RESET +define+BS_HARNESS=$(BS_HARNESS) +define+BS_XMIX

include $(RDS_ROOT)/make/fpga_flow.mk

# Lint reads the stubbed list (the IP has no RTL until Vivado creates it).
lint flat-filelist: FILELIST := $(AREA)/rtl/filelists/bs_genesys2_top_xmix_lint.f
