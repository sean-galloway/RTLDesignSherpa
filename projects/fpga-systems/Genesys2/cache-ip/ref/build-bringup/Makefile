#==============================================================================
# jet pair-rig bring-up build -- Genesys 2 (XC7K325T).
# All flow logic is in the global make/fpga_flow.mk; keep this file to
# variables only.
#==============================================================================

SELF_DIR  := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT  := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))

# Roots this build's filelist closure resolves against.
export JET_ROOT          ?= $(RDS_ROOT)/projects/components/cache-ip/jet-mesi-l1
export JET_PRIME_ROOT    ?= $(RDS_ROOT)/projects/components/cache-ip/jet-prime-mesi-l1
export ONYX_ROOT         ?= $(RDS_ROOT)/projects/components/cache-ip/onyx-ace-ccu
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

# REF_CACHE_SEL picks the cache in the slot: 0 = HPDcache (flow
# ref_hpd_bringup), 1 = CVA6 write-back dcache (flow ref_cva6_bringup),
# 2 = jet-prime straight onto memory, no pair fabric (flow ref_jetp_bringup;
# jet-prime TASK-001 step 1), 3 = the jet-prime pair through the pipelined
# jet_prime_pair_fabric (flow ref_jetpp_bringup; step 3), 4 = the same pair
# behind onyx_ccu with the memory read alongside the snoop (flow
# ref_onyx_bringup; onyx TASK-001 step 6), 5 = onyx with DEFER_AR (flow
# ref_onyxd_bringup). The flow name keeps the bitstreams and report sets
# apart.
REF_CACHE_SEL ?= 0
export REF_CACHE_SEL
flow_sel_0 := hpd
flow_sel_1 := cva6
flow_sel_2 := jetp
flow_sel_3 := jetpp
flow_sel_4 := onyx
flow_sel_5 := onyxd
FLOW      := ref_$(flow_sel_$(REF_CACHE_SEL))_bringup
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
# make ooc CACHE=hpd|cva6|jet|jetp|jetp5|jetp6|amber|{jet,jetp6,amber}_nomon|jetp_fabric|onyx2|onyx_top{,_nomon} [PERIOD=10.0]: out-of-context synth+route
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
ooc_top_jetp   := jet_prime_top
ooc_top_jetp5  := jet_prime_top   # the step-5 cache (its own results row; jetp is steps 2-4's)
ooc_top_jetp6  := jet_prime_top   # the TASK-002 cache (the 2-cycle hit)
ooc_fl_hpd     := $(FRAMEWORK_ROOT)/rtl/filelists/ref_hpdcache_top.f
ooc_fl_cva6    := $(FRAMEWORK_ROOT)/rtl/filelists/ref_cva6_dcache_top.f
ooc_fl_jet     := $(FRAMEWORK_ROOT)/rtl/filelists/ooc_jet_top.f
ooc_fl_amber   := $(FRAMEWORK_ROOT)/rtl/filelists/ooc_amber_top.f
ooc_fl_jetp    := $(FRAMEWORK_ROOT)/rtl/filelists/ooc_jet_prime_top.f
ooc_fl_jetp5   := $(FRAMEWORK_ROOT)/rtl/filelists/ooc_jet_prime_top.f
ooc_fl_jetp6   := $(FRAMEWORK_ROOT)/rtl/filelists/ooc_jet_prime_top.f
# <cache>_nomon: the same module with USE_MONITOR=0 (the MonBus observers and
# their arbiter tied off), so the area row can be read with and without the
# instrumentation HPDcache and CVA6 do not carry. Own results dir per row.
ooc_top_jet_nomon   := jet_top
ooc_top_jetp6_nomon := jet_prime_top
ooc_top_amber_nomon := amber_top
ooc_fl_jet_nomon    := $(ooc_fl_jet)
ooc_fl_jetp6_nomon  := $(ooc_fl_jetp6)
ooc_fl_amber_nomon  := $(ooc_fl_amber)
ooc_gen_jet_nomon   := USE_MONITOR=1'b0
ooc_gen_jetp6_nomon := USE_MONITOR=1'b0
ooc_gen_amber_nomon := USE_MONITOR=1'b0
# The two-port coherency managers alone (onyx TASK-001 step 2): the pair
# fabric as the reference rig builds it (FAB_SLOTS 18, SNOOP_INFLIGHT 2)
# and onyx_ccu at N_PORTS 2 in its place, same table depth.
ooc_top_jetp_fabric := jet_prime_pair_fabric
ooc_top_onyx2       := onyx_ccu
ooc_fl_jetp_fabric  := $(FRAMEWORK_ROOT)/rtl/filelists/ooc_jetp_fabric.f
ooc_fl_onyx2        := $(FRAMEWORK_ROOT)/rtl/filelists/ooc_onyx_ccu.f
ooc_gen_jetp_fabric := FAB_SLOTS=18 SNOOP_INFLIGHT=2
ooc_gen_onyx2       := N_PORTS=2 SLOTS=18 SNOOP_INFLIGHT=2
# the managers clock on clk/rst_n (the cache tops on aclk/aresetn); the
# OOC clock port follows, or the timing row is empty
ooc_clk_jetp_fabric := clk
ooc_clk_onyx2       := clk
# onyx_top as the reference rig builds it (N_PORTS 2, SLOTS 18,
# SNOOP_INFLIGHT 2) with its observer and counters, and with USE_MONITOR=0
# (onyx PRD criterion 5, with and without the observers).
ooc_top_onyx_top       := onyx_top
ooc_top_onyx_top_nomon := onyx_top
ooc_fl_onyx_top        := $(FRAMEWORK_ROOT)/rtl/filelists/ooc_onyx_top.f
ooc_fl_onyx_top_nomon  := $(ooc_fl_onyx_top)
ooc_gen_onyx_top       := N_PORTS=2 SLOTS=18 SNOOP_INFLIGHT=2
ooc_gen_onyx_top_nomon := N_PORTS=2 SLOTS=18 SNOOP_INFLIGHT=2 USE_MONITOR=1'b0
ooc_clk_onyx_top       := clk
ooc_clk_onyx_top_nomon := clk
.PHONY: ooc
ooc:
	mkdir -p $(OOC_OUT)
	cd $(OOC_OUT) && REPO_ROOT=$(RDS_ROOT) OOC_TOP=$(ooc_top_$(CACHE)) OOC_FILELIST=$(ooc_fl_$(CACHE)) \
	    OOC_OUT=$(OOC_OUT) OOC_PERIOD_NS=$(PERIOD) OOC_GENERICS="$(or $(OOC_GENERICS),$(ooc_gen_$(CACHE)))" \
	    OOC_CLK="$(or $(ooc_clk_$(CACHE)),aclk)" \
	    $(VIVADO) -mode batch -log ooc.log -nojournal -source $(TCL_DIR)/ooc_cache.tcl
