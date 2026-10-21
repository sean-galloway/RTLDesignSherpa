#==============================================================================
# alu-infer on Nexys A7-100T -- area dispatcher
#==============================================================================
# Per-build work is delegated to the build's own Makefile (variables + the
# global make/fpga_flow.mk); nothing here re-implements flow logic.
#
#   make                              this message
#   make bitstream ALU_PROFILE=lean   BUILD=infer (the only build today)
#   make -C build-infer help          the full per-build target list
#==============================================================================

SELF_DIR := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))
PYTHON   ?= python3

BUILDS   := infer
BUILD    ?= infer
BUILD_DIR = $(SELF_DIR)/build-$(BUILD)

.DEFAULT_GOAL := help
.PHONY: help builds regmap clean clean-all

help:
	@echo "alu-infer on Nexys A7-100T (BUILD=$(BUILD))"
	@echo ""
	@echo "  Builds:"
	@echo "    build-infer/   alu_infer_top in the ALU harness slot (ALU_PROFILE=lean|full)"
	@echo ""
	@echo "  Any build target: make bitstream | program | lint | sim | utilization | timing | clean"
	@echo "  make -C build-infer help       full per-build target list"
	@echo "  make regmap                    regenerate the CSR regblock + regmap from rtl/alu_harness_regs.rdl"

builds:
	@for b in $(BUILDS); do echo "  $$b"; done

# CRITICAL RULE #0: the regblock RTL and the regmap are generated -- never
# hand-edit rtl/generated/ or dv/tbclasses/alu_harness_regs_regmap.py.
# Deliberately NOT a PREBUILD step (it writes DV collateral).
regmap:
	cd $(RDS_ROOT) && $(PYTHON) bin/peakrdl_generate.py \
		projects/fpga-systems/Genesys2/compute-eng-ip/alu-infer/rtl/alu_harness_regs.rdl \
		-o projects/fpga-systems/Genesys2/compute-eng-ip/alu-infer/rtl/generated/alu_harness_regs \
		--cpuif passthrough --no-html --no-markdown --regmap \
		--regmap-output projects/fpga-systems/Genesys2/compute-eng-ip/alu-infer/dv/tbclasses/alu_harness_regs_regmap.py

clean:
	@for b in $(BUILDS); do $(MAKE) --no-print-directory -C $(SELF_DIR)/build-$$b clean; done

clean-all:
	@for b in $(BUILDS); do $(MAKE) --no-print-directory -C $(SELF_DIR)/build-$$b clean-all; done

Makefile: ;
%.mk: ;

%:
	@[ -d $(BUILD_DIR) ] || (echo "No such build: $(BUILD) (have: $(BUILDS))" && false)
	@$(MAKE) --no-print-directory -C $(BUILD_DIR) $@
