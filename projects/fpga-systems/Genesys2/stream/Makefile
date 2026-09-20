#==============================================================================
# stream on Genesys 2 -- area dispatcher
#==============================================================================
# One entry point for the whole component. Per-build work is delegated to the
# build's own Makefile (which is variables + the global make/fpga_flow.mk), so
# nothing here re-implements flow logic.
#
#   make                        this message
#   make bitstream              BUILD=mon (default) -- or obs, or perf
#   make <target> BUILD=obs     any build target against another build
#   make -C build-mon help      the full per-build target list
#
# THREE builds, and which one you want is a question about WHAT IS UNDER TEST.
# They are the same design at different parameters -- one stream_harness.sv,
# one stream_genesys2_top.sv, at component level ([[area-structure]]):
#
#   build    USE_AXI_MONITORS  OBS_ENABLE_MON_TAPS  channels  measures
#   -------  ----------------  -------------------  --------  -------------------
#   mon                     1                    0         8  in-core monitors
#   obs                     0                    1         4  interface observers
#   perf                    0                    0         8  the datapath itself
#
# The two monitor builds are deliberately COMPLEMENTARY, not redundant: obs and
# mon test the monitor code from two directions. build-obs has NO in-core
# stream monitors at all -- that is the point of it, not an omission -- so a
# zero on any `mon_*` probe there is structural. Equally build-mon leaves the
# observer taps off. Reading either zero as a defect costs an afternoon.
#
# obs is pinned at 4 channels (e8511f777): it builds both observers with every
# monitor cone and at 8 channels hits 99.33% LUTs and "Placer could not place
# all instances" on the xc7k325t. The 8-channel design point is PERF's
# requirement (2ee6c2f8a) -- the obs channel count is incidental, not a
# traded-away requirement.
#==============================================================================

SELF_DIR := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))
PYTHON   ?= python3

BUILDS   := mon obs perf
BUILD    ?= mon
BUILD_DIR = $(SELF_DIR)/build-$(BUILD)

BOARD    ?= genesys2

.DEFAULT_GOAL := help
.PHONY: help builds blocks-sim clean clean-all

help:
	@echo "stream on Genesys 2 (BUILD=$(BUILD), BOARD=$(BOARD))"
	@echo ""
	@echo "  Builds -- the same design at different parameters:"
	@echo "    build-mon/    in-core monitors ON,  observer taps off, 8ch"
	@echo "    build-obs/    in-core monitors OFF, observer taps ON,   4ch"
	@echo "    build-perf/   both off -- the datapath itself,          8ch"
	@echo ""
	@echo "    obs and mon test the monitor code from TWO DIRECTIONS."
	@echo "    build-obs has no in-core stream monitors by design: a zero on"
	@echo "    a mon_* probe there is structural, not a defect."
	@echo ""
	@echo "  Any build target, against any build:"
	@echo "    make bitstream                 # BUILD=mon by default"
	@echo "    make bitstream BUILD=obs"
	@echo "    make program lint sim utilization timing clean"
	@echo "    make -C build-mon help         # full per-build target list"
	@echo ""
	@echo "  Area-wide:"
	@echo "    make blocks-sim   Sim the shared dv/ blocks (component level)"
	@echo "    make builds       List builds"
	@echo ""
	@echo "  Host programs -- PER BUILD, auto-discovered from <build>/host/:"
	@echo "    make -C build-perf targets     # list what that build offers"
	@echo "    make -C build-perf host-characterize ARGS=\"--help\""
	@echo ""
	@echo "    This area has NO run_*.py, so the shared run/seq-list targets"
	@echo "    do not apply -- they exit 1 with \"No run_*.py found\". Board"
	@echo "    work goes through host-<name>: build-mon has the monitor probes,"
	@echo "    build-obs the observer campaign, build-perf the characterization"
	@echo "    and perf tools. bin/ holds the LIBRARIES those import."

builds:
	@for b in $(BUILDS); do echo "  $$b"; done

# Sim for the component-level shared blocks -- distinct from a build's
# whole-harness sim, which is `make sim BUILD=<name>`.
#
# dv/tests, NOT dv/: dv/ also holds tbclasses/, stream_cfg.py and
# cocotb_stream_harness.py, which are imported BY tests rather than being
# tests, so the tests directory is the honest target -- and it is the shape
# pumice already uses. Measured 2026-09-16: TODAY both paths happen to
# collect the same single test (dv/tests/fub/test_monbus_tally_axil.py), so
# this is precision against future drift, not a bug being fixed. Said plainly
# because a Makefile comment claiming a failure mode nobody observed is how
# folklore starts.
blocks-sim:
	@echo "[blocks-sim] $(SELF_DIR)/dv/tests"
	cd $(RDS_ROOT) && $(PYTHON) -m pytest $(SELF_DIR)/dv/tests -q

# Fan out across every build, matching the cdc_counter_display precedent so a
# parent aggregator visiting this component cleans all three.
clean:
	@for b in $(BUILDS); do $(MAKE) --no-print-directory -C $(SELF_DIR)/build-$$b clean; done

clean-all:
	@for b in $(BUILDS); do $(MAKE) --no-print-directory -C $(SELF_DIR)/build-$$b clean-all; done

# Anything else is a per-build target: forward it to the selected build.
# The two no-op rules stop the catch-all from trying to "remake" the makefiles
# themselves, which would recurse.
Makefile: ;
%.mk: ;

%:
	@[ -d $(BUILD_DIR) ] || (echo "No such build: $(BUILD) (have: $(BUILDS))" && false)
	@$(MAKE) --no-print-directory -C $(BUILD_DIR) $@
