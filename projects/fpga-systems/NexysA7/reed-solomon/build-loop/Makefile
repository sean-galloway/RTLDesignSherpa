#==============================================================================
# reed-solomon build-loop -- the RS loop harness on the Nexys A7-100T
# (rs_loop_top: UART/AXIL bridge + PeakRDL CSRs + generator -> encoder ->
# injector -> two decoders -> checkers). Flow logic is make/fpga_flow.mk;
# this file is variables only. `make help` lists targets.
#==============================================================================

SELF_DIR := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))

export CONVERTERS_ROOT ?= $(RDS_ROOT)/projects/components/utility-ip/converters

FLOW      := rs_loop
TOP       := rs_loop_top
FILELIST  := $(SELF_DIR)/rtl/filelists/rs_loop_top.f

# UART-equivalence cocotb sim: the REAL uart_axil_bridge + harness driving the
# UNMODIFIED host programs (host/rs_loop_programs.py) over make_uart_channel.
SIM_TESTS := $(SELF_DIR)/dv/tests
SEQ_DIR   := $(SELF_DIR)/../bin

include $(RDS_ROOT)/make/fpga_flow.mk
