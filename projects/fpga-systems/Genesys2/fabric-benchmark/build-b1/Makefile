# ==============================================================================
# build-b1 -- fabric benchmark board build, leg B1 (Xilinx AXI Crossbar, HDL wrapper)
# ==============================================================================
#   make bitstream     synth + impl + bitstream + reports (fpga/ under this dir)
#   make program       load it on the Genesys 2 (BOARD=genesys2)
#   make lint          Verilator lint of fb_genesys2_top for this leg
# Everything else: make help (make/fpga_flow.mk). Each leg has its own build
# directory, so legs build in parallel; fb_mig is created inside each project.
# ==============================================================================
SELF_DIR := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git -C $(SELF_DIR) rev-parse --show-toplevel))
AREA     := $(abspath $(SELF_DIR)/..)

# Filelist anchors (STREAM is the DMA in every leg)
export STREAM_ROOT                ?= $(RDS_ROOT)/projects/components/dma-ip/stream
export CONVERTERS_ROOT            ?= $(RDS_ROOT)/projects/components/utility-ip/converters
export MISC_ROOT                  ?= $(RDS_ROOT)/projects/components/utility-ip/misc
export STREAM_CHAR_FRAMEWORK_ROOT := $(RDS_ROOT)/projects/fpga-systems/Genesys2/dma-ip/stream
export XILINX_VIVADO              ?= /tools/Xilinx/2025.1/Vivado
VIVADO   ?= $(XILINX_VIVADO)/bin/vivado

export FLOW  := fb_b1
export BOARD ?= genesys2
TOP       := fb_genesys2_top
FILELIST  := $(AREA)/rtl/filelists/fb_genesys2_top_xbar.f
TCL_DIR   := $(AREA)/fpga/tcl
TCL_HELPERS := filelist_utils fb_mig_ip
export FPGA_CONSTRAINTS_DIR := $(AREA)/fpga/constraints
FPGA_DIR  := $(SELF_DIR)/fpga
BITSTREAM := $(FPGA_DIR)/bitstream/$(FLOW)_genesys2.bit
SIM_TESTS := $(AREA)/dv/tests
# Regenerate the bridges, fabric wrappers and MIG .prj before every build.
PREBUILD  := bash $(AREA)/bin/regen.sh

include $(RDS_ROOT)/make/fpga_flow.mk
