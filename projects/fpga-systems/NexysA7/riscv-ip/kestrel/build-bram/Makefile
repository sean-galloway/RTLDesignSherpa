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

# ALU_DSP=1: the ALU's add/sub/logic rows in DSP48 slices (kestrel_alu
# USE_DSP).  Own bitstream name so the two variants can sit side by side.
ALU_DSP   ?= 0
export KESTREL_ALU_DSP := $(ALU_DSP)
ifeq ($(filter $(ALU_DSP),0 1),)
  $(error ALU_DSP must be 0 or 1, got '$(ALU_DSP)')
endif
BITSTREAM := $(SELF_DIR)/fpga/bitstream/$(FLOW)$(if $(filter 1,$(ALU_DSP)),_dsp).bit

# The UART-equivalence sim lives with the Genesys 2 build (same bridge, memory
# system and core; only the board clock differs) -- run it there.

include $(RDS_ROOT)/make/fpga_flow.mk

# AFTER the include (fpga_flow.mk assigns LINT_GENERICS with `=`): the same
# generic create_project.tcl hands Vivado, so lint checks what is built.
LINT_GENERICS += -GALU_USE_DSP=$(ALU_DSP)
