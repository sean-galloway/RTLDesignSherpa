# ==============================================================================
# Bridge out-of-context synthesis + implementation (BRIDGE-017 synthesis guide)
# ==============================================================================
# Characterizes ONE generated bridge on ONE part: synth -> opt -> place -> route
# with the bridge as the top (out-of-context, no pins), then utilization,
# timing and a one-line summary appended to reports/summary.csv. No bitstream:
# this is the "what does this config cost and how fast does it close" flow the
# HAS integration chapter refers to, not a board build.
#
#     make synth                              # bridge_2x2_rw on the Nexys A7 part at 10 ns
#     make synth BRIDGE=bridge_4x4_rw         # another generated fixture
#     make synth PART=xc7k325tffg900-2 CLK_NS=6.667   # Genesys 2 part at 150 MHz
#     make lint  BRIDGE=bridge_2x2_rw_cdc     # verilator on the same closure
#     bin/synth_sweep.sh                      # the reference set on both parts
#
# Everything else (lock, tcl discovery, utilization/timing printers, clean)
# comes from make/fpga_flow.mk. Handbook: fpga/cmn-infra/build-flows.
# ==============================================================================
SELF_DIR := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git -C $(SELF_DIR) rev-parse --show-toplevel))

BRIDGE  ?= bridge_2x2_rw
PART    ?= xc7a100tcsg324-1
CLK_NS  ?= 10.0

FLOW     := bridge_ooc_$(BRIDGE)
TOP      := $(BRIDGE)
FILELIST := $(SELF_DIR)/../rtl/filelists/$(BRIDGE).f

# The tcl reads these; the Makefile is the one authority for the three knobs.
export BRIDGE_TOP    := $(TOP)
export BRIDGE_PART   := $(PART)
export BRIDGE_CLK_NS := $(CLK_NS)
# The generated filelists resolve through $REPO_ROOT; some closures also pull
# the converters area.
export CONVERTERS_ROOT ?= $(RDS_ROOT)/projects/components/converters

include $(RDS_ROOT)/make/fpga_flow.mk

# Per-run report directory, so two bridges (or two parts) never overwrite
# each other's numbers. fpga_flow.mk's `utilization`/`timing` printers look
# at $(REPORTS); point them at this run's directory.
REPORTS := $(SELF_DIR)/reports/$(BRIDGE)__$(PART)
