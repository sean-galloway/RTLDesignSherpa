#==============================================================================
# pumice on Nexys A7 -- area dispatcher
#==============================================================================
# One entry point for the whole component. Per-build work is delegated to the
# build's own Makefile (which is variables + the global make/fpga_flow.mk), so
# nothing here re-implements flow logic.
#
#   make                        this message
#   make bitstream              BUILD=perf (default) -- or BUILD=litedram
#   make ab                     the point of two builds: A/B both on the board
#   make <target> BUILD=litedram   any build target against the other build
#   make -C build-perf help     the full per-build target list
#==============================================================================

SELF_DIR := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))
PYTHON   ?= python3

BUILDS   := perf litedram
BUILD    ?= perf
BUILD_DIR = $(SELF_DIR)/build-$(BUILD)

# Board targets need no build context, so answer them from the perf build.
BOARD    ?= nexys_a7_100t

.DEFAULT_GOAL := help
.PHONY: help builds blocks-sim ab $(BUILDS)

help:
	@echo "pumice on Nexys A7 (BUILD=$(BUILD), BOARD=$(BOARD))"
	@echo ""
	@echo "  Builds:"
	@echo "    build-perf/       pumice on real DDR2      -- the subject"
	@echo "    build-litedram/   LiteDRAM in its place    -- the yardstick"
	@echo ""
	@echo "  Any build target, against either build:"
	@echo "    make bitstream                 # BUILD=perf by default"
	@echo "    make bitstream BUILD=litedram"
	@echo "    make program lint sim run seq-list utilization timing clean"
	@echo "    make -C build-perf help        # full per-build target list"
	@echo ""
	@echo "  Area-wide:"
	@echo "    make blocks-sim   Sim the shared rtl/ blocks (dv/tests)"
	@echo "    make ab           Program+run BOTH builds for the A/B comparison"
	@echo "    make builds       List builds"
	@echo ""
	@echo "  Sequences live in bin/ and are transport-agnostic:"
	@echo "    make seq-list                  # what this area offers"
	@echo "    make run SEQUENCES=\"init write_read\""

builds:
	@for b in $(BUILDS); do echo "  $$b"; done

# Sim for the shared blocks in rtl/ -- distinct from a build's whole-harness sim.
blocks-sim:
	@echo "[blocks-sim] $(SELF_DIR)/dv/tests"
	cd $(RDS_ROOT) && $(PYTHON) -m pytest $(SELF_DIR)/dv/tests -q

# The reason two builds exist: same engines, same taps, two controllers. Running
# them back to back on one board is the comparison; running them weeks apart on
# different board states is not.
ab:
	@echo "=== A/B: pumice vs LiteDRAM, same harness ==="
	@$(MAKE) --no-print-directory -C $(SELF_DIR)/build-perf program run
	@$(MAKE) --no-print-directory -C $(SELF_DIR)/build-litedram program run
	@echo "=== results: build-perf/results vs build-litedram/results ==="

# Anything else is a per-build target: forward it to the selected build.
# The two no-op rules stop the catch-all from trying to "remake" the makefiles
# themselves, which would recurse.
Makefile: ;
%.mk: ;

%:
	@[ -d $(BUILD_DIR) ] || (echo "No such build: $(BUILD) (have: $(BUILDS))" && false)
	@$(MAKE) --no-print-directory -C $(BUILD_DIR) $@
