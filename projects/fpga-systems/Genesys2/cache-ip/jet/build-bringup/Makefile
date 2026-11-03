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
export JET_FRAMEWORK_ROOT  := $(FRAMEWORK_ROOT)
# amber_cycle_injector.sv is reused from the amber area.
export AMBER_FRAMEWORK_ROOT ?= $(FRAMEWORK_ROOT)/../amber

# ---- Shared collateral ------------------------------------------------------
TCL_DIR   := $(FRAMEWORK_ROOT)/fpga/tcl
export FPGA_CONSTRAINTS_DIR := $(FRAMEWORK_ROOT)/fpga/constraints

FLOW      := jet_bringup
BOARD     ?= genesys2
export BOARD

TOP       := jet_pair_genesys2_top
FILELIST  := $(FRAMEWORK_ROOT)/rtl/filelists/jet_pair_genesys2_top.f

HOST_DIR  := $(SELF_DIR)/../host
SEQ_DIR   := $(FRAMEWORK_ROOT)/bin
SIM_TESTS := $(FRAMEWORK_ROOT)/dv/tests

# jet geometry is fixed at the FULL pair-rig configuration.
export JET_USE_MONITOR ?= 1

# Harness clock: 90 MHz from the 200 MHz LVDS oscillator.
export JET_VCO_MHZ        ?= 1350
export JET_CLKOUT0_DIVIDE ?= 15

# Tally CAM legal-set size.
export MON_N_PROFILE ?= 32

# J1 outstanding-miss count.
export MSHR_COUNT ?= 8

FPGA_DIR  := $(SELF_DIR)/fpga
BITSTREAM := $(FPGA_DIR)/bitstream/$(FLOW).bit

# Keep the generated bridge in lockstep with its .toml/.csv before any synthesis.
PREBUILD := bash $(FRAMEWORK_ROOT)/bin/regen_bridges.sh bridge_jet_axil

include $(RDS_ROOT)/make/fpga_flow.mk

# Lint the configuration this build actually synthesizes.
LINT_GENERICS += -GMSHR_COUNT=$(MSHR_COUNT)
