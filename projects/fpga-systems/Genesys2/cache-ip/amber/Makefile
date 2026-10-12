#==============================================================================
# amber pair-rig on Genesys 2 -- area dispatcher
#==============================================================================
# One entry point for the whole component. Per-build work is delegated to the
# build's own Makefile.
#
#   make                 this message
#   make bitstream       BUILD=bringup (default)
#
#==============================================================================

SELF_DIR := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))
PYTHON   ?= python3

BUILDS   := bringup
BUILD    ?= bringup
BUILD_DIR = $(SELF_DIR)/build-$(BUILD)

BOARD    ?= genesys2

.DEFAULT_GOAL := help
.PHONY: help builds clean clean-all

help:
	@echo "amber pair-rig on Genesys 2 (BUILD=$(BUILD), BOARD=$(BOARD))"
	@echo ""
	@echo "  Builds:"
	@echo "    build-bringup/    pair-rig bring-up harness"
	@echo ""
	@echo "  Any build target, against any build:"
	@echo "    make bitstream"
	@echo "    make synth"
	@echo "    make program lint sim utilization timing clean"
	@echo "    make -C build-bringup help"
	@echo ""

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
