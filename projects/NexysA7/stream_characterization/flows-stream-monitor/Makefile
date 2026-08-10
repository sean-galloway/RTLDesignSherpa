#==============================================================================
# Makefile -- STREAM monitor COVERAGE flow (Genesys 2 / Kintex-7 xc7k325t only)
#==============================================================================
#   make bitstream   regen bridge + full synth/impl/bitgen -> bitstream/
#   make program     JTAG-program the Genesys 2 with the current bitstream
#   make sim         cosim: direct + profile harness tests
#   make project     create the Vivado project only (no runs)
#   make clean       remove build/, reports/, bitstream/
#
# Geometry (top defaults: 8 channels, N_PROFILE=64) can be
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
export MON_N_PROFILE          ?= 64
# 0 = all-except-error datapath monitors (default); 1 = error-flavor bitstream
# (error cone only) for ADDR_RANGE error coverage.  make bitstream MON_ERROR_FLAVOR=1
export MON_ERROR_FLAVOR       ?= 0

VIVADO       ?= vivado
VIVADO_BATCH := $(VIVADO) -mode batch
TCL          := $(SELF_DIR)/tcl
REGEN        := $(FRAMEWORK_ROOT)/bin/regen_bridges.sh
BITSTREAM    := $(SELF_DIR)/bitstream/stream_mon_genesys2.bit

# Test area. All test-running logic lives in make/tests.mk (TOOL-008), reached
# through dv/tests/Makefile -- this file forwards, it does not reimplement.
TESTS_DIR    := $(SELF_DIR)/dv/tests

.PHONY: help project bitstream program sim regen-bridges clean clean-all \
        list status jobs collect-all

help:
	@echo "STREAM monitor coverage flow (Genesys 2 / xc7k325t):"
	@echo "Build:"
	@echo "  make bitstream   regen bridge + synth/impl/bitgen -> $(BITSTREAM)"
	@echo "  make program     JTAG-program the Genesys 2 (serial 200300B818A0)"
	@echo "  make project     create the Vivado project only"
	@echo "Sim (forwarded to dv/tests, grammar from make/tests.mk):"
	@echo "  make sim                     clean-all + the usual regression (TRUSTWORTHY)"
	@echo "  make clean-all               wipe local_sim_build/, logs/, __pycache__"
	@echo "  make run-all-<gate|func|full>[-serial|-parallel][-waves]"
	@echo "  make run-<testroot>-<level>  e.g. make run-stream_mon-func"
	@echo "  make list | status | jobs | collect-all"
	@echo "Clean:"
	@echo "  make clean       build/, reports/, bitstream/ AND all test artifacts"
	@echo ""
	@echo "  ALWAYS clean-all before a regression you intend to trust: a stale"
	@echo "  local_sim_build makes cocotb_test report PASSED in under a second"
	@echo "  without simulating anything."
	@echo "  Geometry: NUM_CHANNELS=$(STREAM_NUM_CHANNELS) N_PROFILE=$(MON_N_PROFILE) ERROR_FLAVOR=$(MON_ERROR_FLAVOR)"

# ------------------------------------------------------------------------------
# Test targets: forwarded verbatim to dv/tests. The `run-%` pattern covers the
# whole make/tests.mk grammar (levels, serial/parallel, waves, per-testroot) so
# new targets there need no change here.
# ------------------------------------------------------------------------------
run-%:
	@$(MAKE) --no-print-directory -C $(TESTS_DIR) $@

clean-all list status jobs collect-all:
	@$(MAKE) --no-print-directory -C $(TESTS_DIR) $@

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

# `sim` CLEANS FIRST on purpose. It used to be a bare pytest over
# test_stream_mon.py alone -- which both skipped test_dma_slave_monitors.py
# entirely and, on a warm build dir, reported PASSED without simulating. The
# safe thing is the default; for a fast un-cleaned iteration ask for the run
# target directly (make run-all-func).
sim: clean-all
	@$(MAKE) --no-print-directory -C $(TESTS_DIR) run-all-func

# Superset on purpose: whichever clean you reach for, no stale sim build is left
# behind to pass against.
clean: clean-all
	rm -rf $(SELF_DIR)/build $(SELF_DIR)/reports $(SELF_DIR)/bitstream \
	       $(SELF_DIR)/vivado.log $(SELF_DIR)/vivado.jou
