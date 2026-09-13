#==============================================================================
# pumice build-perf -- pumice on real DDR2. All flow logic is in the global
# make/fpga_flow.mk; keep this file to variables only. `make help` lists targets.
#==============================================================================

SELF_DIR  := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT  := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))

# Roots this build's filelist closure resolves against. env_python defines these
# too, but exporting them here means lint/synth work in a bare shell with only
# REPO_ROOT set -- which is how the old flow behaved and worth keeping.
export CONVERTERS_ROOT ?= $(RDS_ROOT)/projects/components/converters

FLOW      := ddr2_char
TOP       := ddr2_char_top
FILELIST  := $(SELF_DIR)/rtl/filelists/ddr2_char_harness.f
SEQ_DIR   := $(SELF_DIR)/../bin

# The whole-harness sim (real UART bridge + harness_csr + DFI model) still lives
# with the framework, which has not moved -- dv/ here is scaffold. Repoint at
# $(SELF_DIR)/dv/tests when the framework migration lands (NEXYS-003).
SIM_TESTS ?= $(REPO_ROOT)/projects/fpga-systems/NexysA7/pumice/ddr2_char_framework/dv/tests/test_ddr2_char_uart.py

# Keep the generated AXIL bridge in lockstep with its .toml/.csv before any
# synthesis. The bridge adapters instantiate the converters component; twice in
# one week a converters-side interface change left the checked-in generated RTL
# stale (SKID_DEPTH_* removal, header-scope import move) and the staleness
# surfaced as a mid-build compile error instead of at regen time.
#
# CHECKS by default rather than regenerating. The bridge generator is under
# active development, and regenerating in the prebuild meant this board design
# silently absorbed whatever the generator became that day: between the last
# build that closed 75 MHz and 2026-09-13, BRIDGE-016/017/018 landed and the
# config bridge grew ~650 flops with nobody asking for it. A board build has to
# be reproducible from the tree to be worth measuring. Drift still fails loudly
# at prebuild -- which was the original point -- it just no longer rewrites the
# design underneath you.
#
# Take a new bridge deliberately:  REGEN_BRIDGES=1 make bitstream
REGEN_BRIDGES ?= 0
BRIDGE_REGEN  := bash $(RDS_ROOT)/projects/fpga-systems/NexysA7/pumice/ddr2_char_framework/bin/regen_bridges.sh
PREBUILD := $(BRIDGE_REGEN) $(if $(filter-out 0,$(REGEN_BRIDGES)),,--check)

include $(RDS_ROOT)/make/fpga_flow.mk
