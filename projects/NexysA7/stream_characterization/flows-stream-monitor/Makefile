#==============================================================================
# Makefile -- STREAM monitor COVERAGE flow (Genesys 2 / Kintex-7 xc7k325t only)
#==============================================================================
#   make bitstream   regen bridge + full synth/impl/bitgen -> bitstream/
#   make program     JTAG-program the Genesys 2 with the current bitstream
#   make sim         cosim: direct + profile harness tests
#   make project     create the Vivado project only (no runs)
#   make clean       remove build/, reports/, bitstream/
#
# Geometry (top defaults: 8 channels, profile tally on, N_PROFILE=64) can be
# overridden on the command line, e.g.  make bitstream STREAM_NUM_CHANNELS=4
#==============================================================================
SHELL    := /bin/bash
SELF_DIR := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

ifndef REPO_ROOT
$(error REPO_ROOT is not set. Source the repo env file (env_python) first.)
endif
export REPO_ROOT
export CHAR_ROOT        := $(REPO_ROOT)/projects/NexysA7/stream_characterization
export FLOW_ROOT        := $(SELF_DIR)
export STREAM_CHAR_ROOT := $(SELF_DIR)
export FRAMEWORK_ROOT   := $(CHAR_ROOT)/stream_char_framework
export STREAM_ROOT      := $(REPO_ROOT)/projects/components/dmas/stream
export CONVERTERS_ROOT  := $(REPO_ROOT)/projects/components/converters
export MISC_ROOT        := $(REPO_ROOT)/projects/components/misc

# Coverage-build geometry (passed to the top as Vivado generics). 4 channels:
# 8ch + monitors + profile tallies overflows LUTs on the 325T; 4 fits wide.
export STREAM_NUM_CHANNELS    ?= 4
export MON_TALLY_PROFILE_MODE ?= 1
export MON_N_PROFILE          ?= 64

VIVADO       ?= vivado
VIVADO_BATCH := $(VIVADO) -mode batch
TCL          := $(SELF_DIR)/tcl
REGEN        := $(FRAMEWORK_ROOT)/bin/regen_bridges.sh
BITSTREAM    := $(SELF_DIR)/bitstream/stream_mon_genesys2.bit

.PHONY: help project bitstream program sim regen-bridges clean

help:
	@echo "STREAM monitor coverage flow (Genesys 2 / xc7k325t):"
	@echo "  make bitstream   regen bridge + synth/impl/bitgen -> $(BITSTREAM)"
	@echo "  make program     JTAG-program the Genesys 2 (serial 200300B818A0)"
	@echo "  make sim         cosim (direct + profile harness tests)"
	@echo "  make project     create the Vivado project only"
	@echo "  make clean       remove build/, reports/, bitstream/"
	@echo "  Geometry: NUM_CHANNELS=$(STREAM_NUM_CHANNELS) PROFILE=$(MON_TALLY_PROFILE_MODE) N_PROFILE=$(MON_N_PROFILE)"

# Keep the generated bridge in lockstep with its .toml/.csv before a build.
regen-bridges:
	@echo "[regen] bridge_stream_mon_axil"
	@bash $(REGEN) bridge_stream_mon_axil

project:
	cd $(SELF_DIR) && $(VIVADO_BATCH) -source $(TCL)/create_project.tcl

bitstream: regen-bridges
	cd $(SELF_DIR) && $(VIVADO_BATCH) -source $(TCL)/build_all.tcl

program:
	cd $(SELF_DIR) && $(VIVADO_BATCH) -source $(TCL)/program_fpga.tcl

sim:
	cd $(REPO_ROOT) && source env_python && \
	  python3 -m pytest $(SELF_DIR)/dv/tests/test_stream_mon.py -v

clean:
	rm -rf $(SELF_DIR)/build $(SELF_DIR)/reports $(SELF_DIR)/bitstream \
	       $(SELF_DIR)/vivado.log $(SELF_DIR)/vivado.jou
