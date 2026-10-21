#==============================================================================
# alu-infer build-infer -- alu_infer_top in the ALU harness on the Nexys A7-100T
# (alu_nexysa7_top: UART/AXIL -> APB -> PeakRDL CSRs, command RAM -> ALU slot
# -> result RAM). Flow logic is make/fpga_flow.mk; this file is variables
# only. `make help` lists targets.
#
#   ALU_PROFILE=lean   every EN_* off: the v1 bf16 ALU (the first timing number)
#   ALU_PROFILE=full   the RTL defaults: every format and row family (default)
#==============================================================================

SELF_DIR := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))

export CONVERTERS_ROOT ?= $(RDS_ROOT)/projects/components/utility-ip/converters

BOARD       ?= nexys_a7_100t
FLOW        := alu_infer
TOP         := alu_nexysa7_top
FILELIST    := $(SELF_DIR)/rtl/filelists/alu_nexysa7_top.f
ALU_PROFILE ?= full
export ALU_PROFILE

ifeq ($(filter $(ALU_PROFILE),lean full),)
  $(error ALU_PROFILE must be lean or full, got '$(ALU_PROFILE)')
endif

BITSTREAM     := $(SELF_DIR)/fpga/bitstream/$(FLOW)_$(ALU_PROFILE).bit
ILA_BITSTREAM := $(SELF_DIR)/fpga/bitstream/$(FLOW)_$(ALU_PROFILE)_ila.bit
REPORTS       := $(SELF_DIR)/fpga/reports/$(ALU_PROFILE)
export ALU_REPORTS := $(REPORTS)

# The UART-equivalence sim lives with the Genesys 2 build (same bridge,
# harness and ALU slot; only the board clock differs) -- run it there.

include $(RDS_ROOT)/make/fpga_flow.mk

# AFTER the include (fpga_flow.mk assigns LINT_GENERICS with `=`). The SAME
# value create_project.tcl hands Vivado, so lint checks the configuration
# being built.
LINT_GENERICS += -GPROFILE=\"$(shell echo $(ALU_PROFILE) | tr a-z A-Z)\"
