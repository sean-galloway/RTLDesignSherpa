#==============================================================================
# granite target -- Granite DDR2/LPDDR2 v2 on Nexys A7 side-by-side with pumice.
# All flow logic is in the global make/fpga_flow.mk; keep this file to variables
# only. `make help` lists targets.
#==============================================================================

SELF_DIR  := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT  := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))

export CONVERTERS_ROOT ?= $(RDS_ROOT)/projects/components/utility-ip/converters

FLOW      := ddr2_char
TOP       := granite_char_top
FILELIST  := $(SELF_DIR)/rtl/filelists/granite_char_harness.f
SEQ_DIR   := $(SELF_DIR)/../bin

# The whole-harness sim still lives with the framework; dv/ here is scaffold.
SIM_TESTS ?= $(REPO_ROOT)/projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2_char_framework/dv/tests/test_ddr2_char_uart.py

REGEN_BRIDGES ?= 0
BRIDGE_REGEN  := bash $(RDS_ROOT)/projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2_char_framework/bin/regen_bridges.sh
PREBUILD := $(BRIDGE_REGEN) $(if $(filter-out 0,$(REGEN_BRIDGES)),,--check)

include $(RDS_ROOT)/make/fpga_flow.mk
