#==============================================================================
# cdc_counter_display build-demo -- the phase-2 UART-harness CDC demo
# (cdc_demo_top: UART/AXIL bridge + harness CSRs + 4x cdc_counter_domain).
# All flow logic is in the global make/fpga_flow.mk; keep this file to
# variables only. `make help` lists targets.
#==============================================================================

SELF_DIR := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))

# Root the filelist closure resolves against beyond REPO_ROOT. env_python
# defines it too, but exporting it here means lint/synth work in a bare shell
# with only REPO_ROOT set.
export CONVERTERS_ROOT ?= $(RDS_ROOT)/projects/components/converters

FLOW      := cdc_demo
TOP       := cdc_demo_top
FILELIST  := $(SELF_DIR)/rtl/filelists/cdc_demo_top.f

# UART-equivalence cocotb sim: the REAL uart_axil_bridge + harness, driving the
# UNMODIFIED host programs (host/cdc_programs.py) over make_uart_channel.
SIM_TESTS := $(SELF_DIR)/dv/tests

include $(RDS_ROOT)/make/fpga_flow.mk
