#==============================================================================
# gatling on Nexys A7-100T -- area dispatcher
#==============================================================================
# Per-build work is delegated to the build's own Makefile (variables + the
# global make/fpga_flow.mk); nothing here re-implements flow logic.
#
#   make                              this message
#   make bitstream                    BUILD=bram (the only build today)
#   make -C build-bram help           the full per-build target list
#==============================================================================

SELF_DIR := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))
PYTHON   ?= python3

BUILDS   := bram
BUILD    ?= bram
BUILD_DIR = $(SELF_DIR)/build-$(BUILD)

.DEFAULT_GOAL := help
.PHONY: help builds clean clean-all

help:
	@echo "gatling on Nexys A7-100T (BUILD=$(BUILD))"
	@echo ""
	@echo "  Builds:"
	@echo "    build-bram/    gatling_core (4 harts) behind gatling_mem_bram (block RAM, one bank per hart)"
	@echo ""
	@echo "  Any build target: make bitstream | program | lint | sim | utilization | timing | clean"
	@echo "  make -C build-bram help        full per-build target list"

builds:
	@for b in $(BUILDS); do echo "  $$b"; done

clean:
	@for b in $(BUILDS); do $(MAKE) --no-print-directory -C $(SELF_DIR)/build-$$b clean; done

clean-all:
	@for b in $(BUILDS); do $(MAKE) --no-print-directory -C $(SELF_DIR)/build-$$b clean-all; done

Makefile: ;
%.mk: ;

%:
	@[ -d $(BUILD_DIR) ] || (echo "No such build: $(BUILD) (have: $(BUILDS))" && false)
	@$(MAKE) --no-print-directory -C $(BUILD_DIR) $@
