#==============================================================================
# cdc_counter_display on Nexys A7 -- area dispatcher
#==============================================================================
# One entry point for the whole component. Per-build work is delegated to the
# build's own Makefile (which is variables + the global make/fpga_flow.mk), so
# nothing here re-implements flow logic.
#
#   make                        this message
#   make bitstream              BUILD=demo (default) -- or BUILD=phase1
#   make <target> BUILD=phase1  any build target against the other build
#   make -C build-demo help     the full per-build target list
#==============================================================================

SELF_DIR := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))
PYTHON   ?= python3

BUILDS   := demo phase1
BUILD    ?= demo
BUILD_DIR = $(SELF_DIR)/build-$(BUILD)

BOARD    ?= nexys_a7_100t

.DEFAULT_GOAL := help
.PHONY: help builds regmap consistency clean clean-all

help:
	@echo "cdc_counter_display on Nexys A7 (BUILD=$(BUILD), BOARD=$(BOARD))"
	@echo ""
	@echo "  Builds:"
	@echo "    build-demo/     UART harness + 4 CDC counters -- the headline demo"
	@echo "    build-phase1/   button-only starter (no UART)"
	@echo ""
	@echo "  Any build target, against either build:"
	@echo "    make bitstream                 # BUILD=demo by default"
	@echo "    make bitstream BUILD=phase1"
	@echo "    make program lint sim utilization timing clean"
	@echo "    make host-cdc_demo ARGS=smoke  # host CLI (build-demo)"
	@echo "    make -C build-demo help        # full per-build target list"
	@echo ""
	@echo "  Area-wide:"
	@echo "    make regmap        Regenerate cdc_demo_csr regmap from the RDL"
	@echo "    make consistency   Check RDL/regmap vs the hand-written harness SV"
	@echo "    make builds        List builds"

builds:
	@for b in $(BUILDS); do echo "  $$b"; done

# Regenerate the PeakRDL regmap from the RDL descriptor (CRITICAL RULE #0:
# generated collateral -- never hand-edit dv/tbclasses/cdc_demo_csr_regmap.py).
# Deliberately NOT a PREBUILD step: it writes DV collateral, and a build step
# that rewrites DV has destroyed committed fixes before (see the handbook).
regmap:
	@echo "Regenerating cdc_demo_csr regmap from RDL..."
	cd $(RDS_ROOT) && $(PYTHON) bin/peakrdl_generate.py \
		projects/fpga-systems/NexysA7/cdc_counter_display/build-demo/rtl/cdc_demo_csr.rdl \
		--regmap --docs-only --no-html --no-markdown \
		--regmap-output projects/fpga-systems/NexysA7/cdc_counter_display/build-demo/dv/tbclasses/cdc_demo_csr_regmap.py
	@echo "Done. build-demo/dv/tbclasses/cdc_demo_csr_regmap.py"

# Guard: generated regmap must match the hand-written harness SV + RDL.
consistency:
	$(PYTHON) -m pytest $(SELF_DIR)/build-demo/host/test_cdc_demo_regmap_consistency.py -q

# The NexysA7 aggregator visits this component for clean; fan out to builds.
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
