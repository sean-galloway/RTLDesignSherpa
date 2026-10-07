#==============================================================================
# reed-solomon build-loop -- the RS loop harness on the Nexys A7-100T
# (rs_loop_top: UART/AXIL bridge + PeakRDL CSRs + generator -> encoder ->
# injector -> two decoders -> checkers). Flow logic is make/fpga_flow.mk;
# this file is variables only. `make help` lists targets.
#==============================================================================

SELF_DIR := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))

export CONVERTERS_ROOT ?= $(RDS_ROOT)/projects/components/utility-ip/converters

FLOW       := rs_loop
RS_TARGET ?= nexys_a7_100t
RS_PROFILE ?= board
export RS_TARGET
export RS_PROFILE

ifeq ($(RS_TARGET),genesys2)
  TOP       := rs_loop_genesys2_top
  FILELIST  := $(SELF_DIR)/rtl/filelists/rs_loop_genesys2_top.f
  ifeq ($(RS_PROFILE),small)
    BITSTREAM     := $(SELF_DIR)/fpga/bitstream/$(FLOW)_small_genesys2.bit
    ILA_BITSTREAM := $(SELF_DIR)/fpga/bitstream/$(FLOW)_small_genesys2_ila.bit
  else
    BITSTREAM     := $(SELF_DIR)/fpga/bitstream/$(FLOW)_genesys2.bit
    ILA_BITSTREAM := $(SELF_DIR)/fpga/bitstream/$(FLOW)_genesys2_ila.bit
  endif
else
  TOP       := rs_loop_top
  ifeq ($(RS_PROFILE),small)
    FILELIST      := $(SELF_DIR)/rtl/filelists/rs_loop_top_small.f
    BITSTREAM     := $(SELF_DIR)/fpga/bitstream/$(FLOW)_small.bit
    ILA_BITSTREAM := $(SELF_DIR)/fpga/bitstream/$(FLOW)_small_ila.bit
  else
    FILELIST      := $(SELF_DIR)/rtl/filelists/rs_loop_top.f
    BITSTREAM     := $(SELF_DIR)/fpga/bitstream/$(FLOW).bit
    ILA_BITSTREAM := $(SELF_DIR)/fpga/bitstream/$(FLOW)_ila.bit
  endif
endif

# UART-equivalence cocotb sim: the REAL uart_axil_bridge + harness driving the
# UNMODIFIED host programs (host/rs_loop_programs.py) over make_uart_channel.
SIM_TESTS := $(SELF_DIR)/dv/tests
SEQ_DIR   := $(SELF_DIR)/../bin

# Keep the generated 1x3 fabric in lockstep with its .toml/.csv before any
# synthesis, but CHECK by default rather than regenerate: a board build has to
# be reproducible, and silently taking a new bridge mid-campaign changes the
# design under the measurement. Take a new one deliberately:
#   REGEN_BRIDGES=1 make bitstream
REGEN_BRIDGES ?= 0
BRIDGE_REGEN  := bash $(SELF_DIR)/../bin/regen_bridges.sh
PREBUILD := $(BRIDGE_REGEN) $(if $(filter-out 0,$(REGEN_BRIDGES)),,--check)

include $(RDS_ROOT)/make/fpga_flow.mk

# AFTER the include, because fpga_flow.mk assigns LINT_GENERICS with `=` and
# would otherwise discard these. Same env vars fpga/tcl/create_project.tcl
# turns into Vivado generics -- keep the two lists in step, because a gate
# that checks a different configuration than the one being built cannot catch
# a configuration-specific fault.
LINT_GENERICS += \
    $(if $(RS_IFACE),-GIFACE=\"$(RS_IFACE)\") \
    $(if $(RS_ENABLE_COMPARE),-GENABLE_COMPARE=$(RS_ENABLE_COMPARE)) \
    $(if $(RS_KES_ALGO_A),-GKES_ALGO_A=\"$(RS_KES_ALGO_A)\")
