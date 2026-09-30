#==============================================================================
# scoria on Genesys 2 -- area dispatcher
#==============================================================================
# One entry point for the whole component. Per-build work is delegated to the
# build's own Makefile (variables + the global make/fpga_flow.mk), so nothing
# here re-implements flow logic.
#
#   make                          this message
#   make bitstream                BUILD=scoria (default) -- or BUILD=litedram
#   make ab                       the point of two builds: A/B both on the board
#   make <target> BUILD=litedram  any build target against the other build
#   make -C build-scoria help     the full per-build target list
#
# Both builds live at build-<name>/ so the dispatcher below actually resolves.
# The pumice area's equivalent declares `BUILDS := perf litedram` and resolves
# build-$(BUILD), but its LiteDRAM build sits at
# ddr2-characterization/flows-litedram-uart -- so `make bitstream BUILD=litedram`,
# which its own help advertises, dies with "No such build". Only its `make ab`
# works, because that target hardcodes the real path. Do not reintroduce that
# split here.
#==============================================================================

SELF_DIR := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))
PYTHON   ?= python3

BUILDS   := scoria litedram
BUILD    ?= scoria
BUILD_DIR = $(SELF_DIR)/build-$(BUILD)

BOARD    ?= genesys2

.DEFAULT_GOAL := help
.PHONY: help builds blocks-sim ab $(BUILDS)

help:
	@echo "scoria on Genesys 2 (BUILD=$(BUILD), BOARD=$(BOARD))"
	@echo ""
	@echo "  Builds:"
	@echo "    build-scoria/     scoria on real DDR3    -- the subject"
	@echo "    build-litedram/   LiteDRAM in its place  -- the yardstick"
	@echo ""
	@echo "  Any build target, against either build:"
	@echo "    make bitstream                 # BUILD=scoria by default"
	@echo "    make bitstream BUILD=litedram"
	@echo "    make program lint sim run seq-list utilization timing clean"
	@echo "    make -C build-scoria help      # full per-build target list"
	@echo ""
	@echo "  Area-wide:"
	@echo "    make blocks-sim   Sim the shared rtl/ blocks (dv/tests)"
	@echo "    make ab           Program+run BOTH builds for the A/B comparison"
	@echo "    make builds       List builds"

builds:
	@for b in $(BUILDS); do echo "  $$b"; done

blocks-sim:
	@echo "[blocks-sim] $(SELF_DIR)/dv/tests"
	cd $(RDS_ROOT) && $(PYTHON) -m pytest $(SELF_DIR)/dv/tests -q

# The reason two builds exist: same engine, same taps, two controllers. Running
# them back to back on one board is the comparison; running them weeks apart on
# different board states is not.
ab:
	@echo "=== A/B: scoria vs LiteDRAM, same harness, same board ==="
	@$(MAKE) --no-print-directory -C $(SELF_DIR)/build-scoria   program run
	@$(MAKE) --no-print-directory -C $(SELF_DIR)/build-litedram program run
	@echo "=== results: build-scoria/results vs build-litedram/results ==="

# Anything else is a per-build target: forward it to the selected build. The two
# no-op rules stop the catch-all from trying to "remake" the makefiles, which
# would recurse.
Makefile: ;
%.mk: ;

%:
	@[ -d $(BUILD_DIR) ] || (echo "No such build: $(BUILD) (have: $(BUILDS))" && false)
	@$(MAKE) --no-print-directory -C $(BUILD_DIR) $@
