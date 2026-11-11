#==============================================================================
# jet pair-rig bring-up build -- Genesys 2 (XC7K325T).
# All flow logic is in the global make/fpga_flow.mk; keep this file to
# variables only.
#==============================================================================

SELF_DIR  := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT  := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))

# Roots this build's filelist closure resolves against.
export JET_ROOT          ?= $(RDS_ROOT)/projects/components/cache-ip/jet-mesi-l1
export AMBER_ROOT        ?= $(RDS_ROOT)/projects/components/cache-ip/amber-mesi-l1
export CACHE_COMMON_ROOT ?= $(RDS_ROOT)/projects/components/cache-ip/common-ip
export CONVERTERS_ROOT   ?= $(RDS_ROOT)/projects/components/utility-ip/converters
export MISC_ROOT         ?= $(RDS_ROOT)/projects/components/utility-ip/misc

# The shared harness collateral is COMPONENT-level, one directory up.
export FRAMEWORK_ROOT      := $(SELF_DIR)/..
export REF_FRAMEWORK_ROOT  := $(FRAMEWORK_ROOT)
export JET_FRAMEWORK_ROOT  ?= $(FRAMEWORK_ROOT)/../jet
# amber_cycle_injector.sv is reused from the amber area.
export AMBER_FRAMEWORK_ROOT ?= $(FRAMEWORK_ROOT)/../amber

# ---- Shared collateral ------------------------------------------------------
TCL_DIR   := $(FRAMEWORK_ROOT)/fpga/tcl
export FPGA_CONSTRAINTS_DIR := $(FRAMEWORK_ROOT)/fpga/constraints

# REF_CACHE_SEL picks the reference in the cache slot: 0 = HPDcache (flow
# ref_hpd_bringup), 1 = CVA6 write-back dcache (flow ref_cva6_bringup). The
# flow name keeps the two bitstreams and report sets apart.
REF_CACHE_SEL ?= 0
export REF_CACHE_SEL
FLOW      := ref_$(if $(filter 1,$(REF_CACHE_SEL)),cva6,hpd)_bringup
BOARD     ?= genesys2
export BOARD

TOP       := ref_genesys2_top
FILELIST  := $(FRAMEWORK_ROOT)/rtl/filelists/ref_genesys2_top.f

HOST_DIR  := $(JET_FRAMEWORK_ROOT)/host   # same bridge map: the jet host stack drives this rig
SEQ_DIR   := $(JET_FRAMEWORK_ROOT)/bin
SIM_TESTS := $(FRAMEWORK_ROOT)/dv/tests

# jet geometry is fixed at the FULL pair-rig configuration.

# Harness clock: set by the RTL parameters VCO_MHZ/CLKOUT0_DIVIDE in
# rtl/ref_genesys2_top.sv (clone of the jet top: 1350/13.5 = 100 MHz; the
# ISSUE-001 v3 lookup-pipeline work). No env knob -- a Makefile variable
# here would silently NOT reach the RTL (learned 2026-11-03).

# Tally CAM legal-set size.

# J1 outstanding-miss count.

FPGA_DIR  := $(SELF_DIR)/fpga
BITSTREAM := $(FPGA_DIR)/bitstream/$(FLOW).bit

# Keep the generated bridge in lockstep with its .toml/.csv before any synthesis.

include $(RDS_ROOT)/make/fpga_flow.mk

# Lint the configuration this build actually synthesizes.
LINT_GENERICS += -GREF_CACHE_SEL=$(REF_CACHE_SEL)

# ---- cache-only area / Fmax (TASK-003 comparison) ----------------------------
# make ooc CACHE=hpd|cva6|jet|amber [PERIOD=10.0]: out-of-context synth+route
# of one cache module via fpga/tcl/ooc_cache.tcl; reports under
# ../results/ooc/<cache>/<period>ns/ (summary.txt has lut/ff/ramb/wns; outside
# fpga/, which `make clean` wipes -- the first run lost three rows that way).
CACHE  ?= hpd
PERIOD ?= 10.0
OOC_OUT := $(FRAMEWORK_ROOT)/results/ooc/$(CACHE)/$(PERIOD)ns
ooc_top_hpd    := ref_hpdcache_top
ooc_top_cva6   := ref_cva6_dcache_top
ooc_top_jet    := jet_top
ooc_top_amber  := amber_top
ooc_fl_hpd     := $(FRAMEWORK_ROOT)/rtl/filelists/ref_hpdcache_top.f
ooc_fl_cva6    := $(FRAMEWORK_ROOT)/rtl/filelists/ref_cva6_dcache_top.f
ooc_fl_jet     := $(FRAMEWORK_ROOT)/rtl/filelists/ooc_jet_top.f
ooc_fl_amber   := $(FRAMEWORK_ROOT)/rtl/filelists/ooc_amber_top.f
.PHONY: ooc
ooc:
	mkdir -p $(OOC_OUT)
	cd $(OOC_OUT) && REPO_ROOT=$(RDS_ROOT) OOC_TOP=$(ooc_top_$(CACHE)) OOC_FILELIST=$(ooc_fl_$(CACHE)) \
	    OOC_OUT=$(OOC_OUT) OOC_PERIOD_NS=$(PERIOD) OOC_GENERICS="$(OOC_GENERICS)" \
	    $(VIVADO) -mode batch -log ooc.log -nojournal -source $(TCL_DIR)/ooc_cache.tcl
