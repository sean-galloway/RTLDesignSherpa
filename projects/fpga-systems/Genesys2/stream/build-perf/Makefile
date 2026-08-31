#==============================================================================
# stream build-perf -- the characterization harness on Genesys 2.
#
# SAME SOURCE as build-mon: one stream_harness.sv, one stream_genesys2_top.sv,
# one tcl set, one xdc, all at component level. This build differs ONLY in the
# parameters below -- there is no perf-specific RTL to keep in step.
#
# The distinction that matters: USE_AXI_MONITORS=0 drops the heavy in-core
# monitor cones (which is what lets a small part fit), while the inline
# axi4_intf_master_observer is instantiated OUTSIDE that gate and keeps producing perf
# counts. That separation regressed once -- USE_AXI_MONITORS=0 over-gated the
# cheap bus meters too and the build reported zeros -- so test_stream_mon now
# asserts the observer counters are non-zero in this flavor.
#==============================================================================

SELF_DIR  := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT  := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))

export STREAM_ROOT     ?= $(RDS_ROOT)/projects/components/dmas/stream
export CONVERTERS_ROOT ?= $(RDS_ROOT)/projects/components/converters
export MISC_ROOT       ?= $(RDS_ROOT)/projects/components/misc
# ':=' not '?=': env_python exports these pointing at the pre-migration tree.
export FRAMEWORK_ROOT  := $(SELF_DIR)/..
export STREAM_CHAR_FRAMEWORK_ROOT := $(FRAMEWORK_ROOT)
export STREAM_CHAR_ROOT := $(FRAMEWORK_ROOT)

TCL_DIR   := $(FRAMEWORK_ROOT)/fpga/tcl
export FPGA_CONSTRAINTS_DIR := $(FRAMEWORK_ROOT)/fpga/constraints

FLOW      := stream_perf
TOP       := stream_genesys2_top
FILELIST  := $(FRAMEWORK_ROOT)/rtl/filelists/stream_genesys2_top.f
BOARD     ?= genesys2
SEQ_DIR   := $(FRAMEWORK_ROOT)/bin
SIM_TESTS ?= $(SELF_DIR)/dv/tests

# stream_env selects which build's host/ layer goes on sys.path; its default is
# 'mon'. WITHOUT this, a perf host program that imports a sibling from its own
# host/ gets build-mon's copy -- and it would appear to work, because Python
# also puts the running script's own directory on sys.path first.
export STREAM_BUILD ?= perf

# ---- Build geometry: the perf flavor --------------------------------------
# Monitors OFF. The observer is not gated by this and still meters the bus.
export USE_AXI_MONITORS    ?= 0
# NOTE: no trailing comments on these lines. Make keeps the whitespace BEFORE a
# trailing '#', so `?= 8      # comment` sets the variable to "8      ". That
# value reaches create_project.tcl, which braces it to preserve the spaces, and
# Vivado is handed the generic {NUM_CHANNELS=8      }. Its elaborator then spins
# at 100% CPU forever -- which is why this build has NEVER produced a bitstream
# while build-mon, whose exports carry no inline comments, always has.
# no monitor CAMs to fit, so all 8 channels
export STREAM_NUM_CHANNELS ?= 8
export MON_N_PROFILE       ?= 64
# irrelevant with monitors off; kept explicit
export MON_ERROR_FLAVOR    ?= 0

PREBUILD := bash $(FRAMEWORK_ROOT)/bin/regen_bridges.sh bridge_stream_mon_axil

# Settings shared by every build in this component (see stream.mk).
include $(FRAMEWORK_ROOT)/stream.mk

include $(RDS_ROOT)/make/fpga_flow.mk
