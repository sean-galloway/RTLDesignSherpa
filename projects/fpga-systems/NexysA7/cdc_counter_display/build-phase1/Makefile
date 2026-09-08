#==============================================================================
# cdc_counter_display build-phase1 -- the button-only starter demo
# (cdc_counter_display_top: BTNC increments, 4-phase CDC to the display
# domain, no UART). All flow logic is in the global make/fpga_flow.mk; keep
# this file to variables only. `make help` lists targets.
#==============================================================================

SELF_DIR := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))

FLOW      := cdc_counter_display
TOP       := cdc_counter_display_top
FILELIST  := $(SELF_DIR)/rtl/filelists/cdc_counter_display_top.f
SIM_TESTS := $(SELF_DIR)/dv/tests

include $(RDS_ROOT)/make/fpga_flow.mk
