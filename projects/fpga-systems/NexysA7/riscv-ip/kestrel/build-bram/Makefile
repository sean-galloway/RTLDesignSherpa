#==============================================================================
# kestrel build-bram -- kestrel RV32I on the Nexys A7-100T behind kestrel_mem_bram
# (block RAM, registered read; UART -> AXI4-Lite loader + run/status).
# Flow logic is make/fpga_flow.mk; this file is variables only.
#==============================================================================

SELF_DIR := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))

export CONVERTERS_ROOT ?= $(RDS_ROOT)/projects/components/utility-ip/converters
export KESTREL_ROOT    ?= $(RDS_ROOT)/projects/components/riscv-ip/kestrel-rv32i

BOARD     ?= nexys_a7_100t
FLOW      := kestrel_bram
TOP       := kestrel_nexysa7_top
FILELIST  := $(SELF_DIR)/rtl/filelists/kestrel_nexysa7_top.f

# IMPL=explore (the default here): timing-driven implementation directives +
# phys_opt passes (fpga/tcl/create_project.tcl), ~0.8 ns better on this core;
# IMPL=default keeps Vivado's defaults.
IMPL      ?= explore
export KESTREL_IMPL := $(IMPL)
ifeq ($(filter $(IMPL),default explore),)
  $(error IMPL must be default or explore, got '$(IMPL)')
endif

# The UART-equivalence sim lives with the Genesys 2 build (same bridge, memory
# system and core; only the board clock differs) -- run it there.

include $(RDS_ROOT)/make/fpga_flow.mk
