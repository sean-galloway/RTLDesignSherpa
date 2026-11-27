#==============================================================================
# gatling build-tetrad -- gatling_tetrad (the barrel core, the Xcell unit and
# four cells on alu-infer, bf16 profile) on the Nexys A7-100T at 4.6875 MHz,
# behind gatling_mem_bram (programs, run/status) and the cell harness (cfg,
# fill, drain, FLUSH/KICK observers); UART -> AXI4-Lite.
# Flow logic is make/fpga_flow.mk; this file is variables only.
#==============================================================================

SELF_DIR := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))

export CONVERTERS_ROOT ?= $(RDS_ROOT)/projects/components/utility-ip/converters
export GATLING_ROOT    ?= $(RDS_ROOT)/projects/components/riscv-ip/gatling-rv32i
# gatling's decode/imm_gen/alu and ISA package are common-rv32i's.
export RV32I_COMMON_ROOT ?= $(RDS_ROOT)/projects/components/riscv-ip/common-rv32i

BOARD     ?= nexys_a7_100t
FLOW      := gatling_tetrad
TOP       := gatling_tetrad_nexysa7_top
FILELIST  := $(SELF_DIR)/rtl/filelists/gatling_tetrad_nexysa7_top.f

# IMPL=explore (the default here): timing-driven implementation directives +
# phys_opt passes (fpga/tcl/create_project.tcl), ~0.8 ns better on this core;
# IMPL=default keeps Vivado's defaults.
IMPL      ?= default
export GATLING_IMPL := $(IMPL)
ifeq ($(filter $(IMPL),default explore),)
  $(error IMPL must be default or explore, got '$(IMPL)')
endif

# UART-equivalence cocotb sim: the REAL uart_axil_bridge + gatling_mem_bram +
# core driving the UNMODIFIED host programs (../bin/gatling_programs.py).
SIM_TESTS := $(SELF_DIR)/../dv/tests/test_gatling_tetrad_board_uart.py
SEQ_DIR   := $(SELF_DIR)/../bin

include $(RDS_ROOT)/make/fpga_flow.mk
