#==============================================================================
# kestrel build-bram -- kestrel RV32I on the Genesys 2 behind kestrel_mem_bram
# (block RAM, registered read; UART -> AXI4-Lite loader + run/status).
# Flow logic is make/fpga_flow.mk; this file is variables only.
#==============================================================================

SELF_DIR := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))

export CONVERTERS_ROOT ?= $(RDS_ROOT)/projects/components/utility-ip/converters
export KESTREL_ROOT    ?= $(RDS_ROOT)/projects/components/riscv-ip/kestrel-rv32i

BOARD     ?= genesys2
FLOW      := kestrel_bram
# ALU_DSP=1: seven ALU rows in one DSP48E1 (kestrel_alu USE_DSP); own name.
ALU_DSP   ?= 0
export KESTREL_ALU_DSP := $(ALU_DSP)
ifeq ($(filter $(ALU_DSP),0 1),)
  $(error ALU_DSP must be 0 or 1, got '$(ALU_DSP)')
endif
TOP       := kestrel_genesys2_top
FILELIST  := $(SELF_DIR)/rtl/filelists/kestrel_genesys2_top.f

# UART-equivalence cocotb sim: the REAL uart_axil_bridge + kestrel_mem_bram +
# core driving the UNMODIFIED host programs (../bin/kestrel_programs.py).
SIM_TESTS := $(SELF_DIR)/../dv/tests
SEQ_DIR   := $(SELF_DIR)/../bin

BITSTREAM := $(SELF_DIR)/fpga/bitstream/$(FLOW)$(if $(filter 1,$(ALU_DSP)),_dsp).bit

include $(RDS_ROOT)/make/fpga_flow.mk

# AFTER the include (fpga_flow.mk assigns LINT_GENERICS with `=`).
LINT_GENERICS += -GALU_USE_DSP=$(ALU_DSP)
