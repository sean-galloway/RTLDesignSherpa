#==============================================================================
# stream build-mon -- the monitor-validation harness on Genesys 2 (XC7K325T).
# All flow logic is in the global make/fpga_flow.mk; keep this file to
# variables only. `make help` lists targets, `make targets` lists what was
# discovered on disk.
#==============================================================================

SELF_DIR  := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT  := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))

# Roots this build's filelist closure resolves against. env_python defines these
# too, but exporting them here means lint/synth work in a bare shell with only
# REPO_ROOT set.
export STREAM_ROOT     ?= $(RDS_ROOT)/projects/components/dmas/stream
export CONVERTERS_ROOT ?= $(RDS_ROOT)/projects/components/converters
export MISC_ROOT       ?= $(RDS_ROOT)/projects/components/misc
# The shared stream harness collateral (harness_csr, axi_response_delay, the
# generated bridges, instrumentation.f) is now COMPONENT-level, one directory up
# -- it is shared by build-mon and build-perf rather than owned by either.
# NOTE the ':=' -- these MUST be unconditional. env_python already exports
# STREAM_CHAR_ROOT / STREAM_CHAR_FRAMEWORK_ROOT pointing at the pre-migration
# tree, so '?=' silently keeps this build resolving its filelists against the
# OLD location and the relocation looks fine right up until a source is read
# from the wrong place.
export FRAMEWORK_ROOT  := $(SELF_DIR)/..
export STREAM_CHAR_FRAMEWORK_ROOT := $(FRAMEWORK_ROOT)
# Legacy name still used by this build's filelists and tcl for its OWN rtl/.
# The harness/top are COMPONENT level now -- one source, both builds.
export STREAM_CHAR_ROOT := $(FRAMEWORK_ROOT)

# ---- Shared collateral: ONE harness, ONE top, ONE tcl set, ONE xdc ---------
# build-mon and build-perf are the SAME design; they differ only in the
# parameters below. Anything identical between them lives at component level so
# there is literally one copy -- that is the point of the exercise, and it is
# why the two near-identical harnesses could be retired.
TCL_DIR   := $(FRAMEWORK_ROOT)/fpga/tcl
export FPGA_CONSTRAINTS_DIR := $(FRAMEWORK_ROOT)/fpga/constraints

FLOW      := stream_mon
TOP       := stream_genesys2_top
FILELIST  := $(FRAMEWORK_ROOT)/rtl/filelists/stream_genesys2_top.f
BOARD     ?= genesys2
SEQ_DIR   := $(SELF_DIR)/../bin
SIM_TESTS ?= $(SELF_DIR)/dv/tests

# stream_env's DEFAULT is 'mon', so this is belt-and-braces here -- but being
# explicit is what makes build-perf's setting obviously necessary rather than
# looking like a stray override.
export STREAM_BUILD ?= mon

# ---- Build geometry (Vivado generics) --------------------------------------
export STREAM_NUM_CHANNELS ?= 8
export MON_N_PROFILE       ?= 64
# Datapath-monitor cone set: 0 = all-except-error, 1 = error only,
# 2 = ALL cones. 0 and 1 are mutually exclusive halves and needed TWO
# bitstreams (and a re-flash mid-campaign) to cover every packet class;
# 2 is the union, which is the point of the 90 MHz harness clock.
export MON_ERROR_FLAVOR    ?= 2

# The flavor is part of the ARTIFACT NAME, not just a build-time switch. With a
# single fixed name, `make bitstream MON_ERROR_FLAVOR=1` silently overwrote the
# flavor-0 bitstream and left no way to tell the two apart on disk -- which then
# reads as "the monitor missed the fault" when the truth is "that cone is not in
# this bitstream". Encode it instead.
#
# DERIVED, not hand-written. The old expression tested only for flavor 1 and
# called everything else "_all_except_error", so the all-cones build landed on
# disk under a name asserting the error cone was absent -- the exact failure
# this comment block was written to prevent, reintroduced by adding a third
# mode. Deriving every token from the geometry means the filename cannot
# disagree with the bitstream again.
FPGA_DIR  := $(SELF_DIR)/fpga
MON_CONES := $(if $(filter 2,$(MON_ERROR_FLAVOR)),allcones,$(if $(filter 1,$(MON_ERROR_FLAVOR)),error,allexcepterror))
BITSTREAM := $(FPGA_DIR)/bitstream/$(FLOW)_$(STREAM_NUM_CHANNELS)ch_$(MON_CONES)_obsmaster_obsslave.bit

# Keep the generated bridge in lockstep with its .toml/.csv before any synthesis
# (cheap, and stops a stale checkout producing a stale bitstream). fpga_flow.mk
# wires PREBUILD into project/synth/bitstream -- no recipe belongs here.
PREBUILD := bash $(FRAMEWORK_ROOT)/bin/regen_bridges.sh bridge_stream_mon_axil

# Settings shared by every build in this component (see stream.mk).
include $(FRAMEWORK_ROOT)/stream.mk

include $(RDS_ROOT)/make/fpga_flow.mk
