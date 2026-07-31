# ==============================================================================
# RDS FPGA flow master Makefile -- the whole flow for one harness build
# ==============================================================================
#
# The ONLY place FPGA build/board/sim logic lives. A build's Makefile sets a few
# variables and includes this file; you should never need to know a tcl script
# name, a Vivado command line, or a pytest path to run the flow.
#
#     FLOW      := ddr2_char                 # names the project + bitstream
#     TOP       := ddr2_char_top             # top module, for lint
#     FILELIST  := $(SELF_DIR)/rtl/filelists/ddr2_char_harness.f
#     SIM_TESTS := $(SELF_DIR)/dv/tests      # pytest target for `make sim`
#     SEQ_DIR   := $(SELF_DIR)/../bin        # sequences, for `make run`
#     RDS_ROOT  := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))
#     include $(RDS_ROOT)/make/fpga_flow.mk
#
# Everything else is derived and overridable. `make help` lists the real target
# set (generated from the ## comments, so it cannot drift).
#
# Target grammar:
#
#   build     project  synth  bitstream  bitstream-ila  lint
#   board     program  ports  board-info  boards
#   run       sim  run  seq-list
#   inspect   utilization  timing
#   tidy      clean  clean-all
#
# Layout: defaults assume the current layout (fpga/tcl, fpga/bitstream,
# fpga/reports) and fall back to the older flat one (tcl/, bitstream/, reports/)
# so existing flows can adopt this file without moving anything first.
#
# A build that needs a genuinely different recipe overrides the variable, not
# the rule -- e.g. BUILD_TCL := my_build.tcl. If it must replace a rule outright,
# include make/fpga_board.mk instead and keep its own build half.
#
# Handbook: [[fpga/cmn-infra/build-flows]] (the Vivado batch flow),
#           [[fpga/cmn-infra/boards]] (the registry),
#           [[fpga/cmn-infra/sequences]] (what `make run` runs).
# ==============================================================================

SHELL := /bin/bash

ifndef FLOW
$(error FLOW is not set. An FPGA build Makefile must set FLOW before including make/fpga_flow.mk)
endif

SELF_DIR ?= $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT ?= $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))
export REPO_ROOT ?= $(RDS_ROOT)

# ---- Layout ----------------------------------------------------------------
# Prefer the fpga/ subdirectory layout; fall back to flat for older flows.
FPGA_DIR   ?= $(if $(wildcard $(SELF_DIR)/fpga),$(SELF_DIR)/fpga,$(SELF_DIR))
TCL_DIR    ?= $(FPGA_DIR)/tcl
BITSTREAM  ?= $(FPGA_DIR)/bitstream/$(FLOW).bit
ILA_BITSTREAM ?= $(FPGA_DIR)/bitstream/$(FLOW)_ila.bit
REPORTS    ?= $(FPGA_DIR)/reports
BUILD_DIR  ?= $(SELF_DIR)/build
PROJECT    ?= $(BUILD_DIR)/vivado_project/$(FLOW).xpr

# ---- Tools -----------------------------------------------------------------
VIVADO       ?= vivado
VIVADO_BATCH ?= $(VIVADO) -mode batch -notrace
PYTHON       ?= python3
VERILATOR    ?= verilator

# ---- Tcl script names (override the variable, not the rule) ----------------
PROJECT_TCL ?= create_project.tcl
SYNTH_TCL   ?= synth_only.tcl
BUILD_TCL   ?= build_all.tcl
ILA_TCL     ?= build_ila.tcl

# ---- Host / sim entry points -----------------------------------------------
BAUD      ?= 115200
SEQ_DIR   ?=
RUN_SCRIPT ?= $(firstword $(wildcard $(SEQ_DIR)/run_*.py))
SEQUENCES ?=
SIM_TESTS ?=
SIM_ARGS  ?= -q

# Lint waiver set. These are the harness-integration warnings that are noise on
# a board top (vendor IP, generated cores, wide interconnect); real RTL rules are
# enforced where the RTL lives, not here.
LINT_DEFINES ?= +define+USE_ASYNC_RESET
LINT_WAIVERS ?= -Wno-MULTIDRIVEN -Wno-UNUSED -Wno-UNDRIVEN -Wno-WIDTH \
                -Wno-CASEINCOMPLETE -Wno-SELRANGE -Wno-DECLFILENAME \
                -Wno-UNUSEDSIGNAL -Wno-VARHIDDEN -Wno-IMPLICIT \
                -Wno-CASEOVERLAP -Wno-MODDUP

include $(RDS_ROOT)/make/fpga_board.mk

.DEFAULT_GOAL := help
.PHONY: help project synth bitstream bitstream-ila lint sim run seq-list \
        utilization timing clean clean-all

# ---- Help (generated from ## comments, so it cannot go stale) --------------
help:               ## Show this message
	@echo "$(FLOW) -- FPGA flow (BOARD=$(BOARD))"
	@echo ""
	@grep -hE '^[a-zA-Z0-9_-]+:.*?## .*$$' $(MAKEFILE_LIST) \
	    | sort -u \
	    | awk 'BEGIN {FS = ":.*?## "}; {printf "  \033[36m%-16s\033[0m %s\n", $$1, $$2}'
	@echo ""
	@echo "  bitstream -> $(BITSTREAM)"
	@echo "  reports   -> $(REPORTS)"

# ---- Build -----------------------------------------------------------------
lint:               ## verilator --lint-only of the whole harness (fast, pre-Vivado)
	@[ -n "$(TOP)" ] || (echo "TOP is not set -- cannot lint." && false)
	@[ -f "$(FILELIST)" ] || (echo "FILELIST not found: $(FILELIST)" && false)
	@echo "[lint] $(TOP)"
	@$(VERILATOR) --lint-only --top-module $(TOP) -f $(FILELIST) \
	    $(LINT_DEFINES) $(LINT_WAIVERS)

project:            ## Create the Vivado project (no build)
	@echo "[project] $(FLOW)"
	cd $(SELF_DIR) && $(VIVADO_BATCH) -source $(TCL_DIR)/$(PROJECT_TCL)

synth:              ## Synthesis only + utilization + failing-path reports
	@echo "[synth] $(FLOW) (skip place/route)"
	cd $(SELF_DIR) && $(VIVADO_BATCH) -source $(TCL_DIR)/$(SYNTH_TCL)
	@$(MAKE) --no-print-directory utilization
	@$(MAKE) --no-print-directory timing

bitstream:          ## Full synth/impl/bitgen + all reports (10-30 min)
	@echo "[bitstream] $(FLOW) full flow"
	cd $(SELF_DIR) && $(VIVADO_BATCH) -source $(TCL_DIR)/$(BUILD_TCL)
	@echo ""
	@echo "Bitstream: $(BITSTREAM)"
	@echo "Reports:   $(REPORTS)"

bitstream-ila:      ## Same design plus an ILA on the marked debug nets
	@echo "[bitstream-ila] $(FLOW)"
	cd $(SELF_DIR) && $(VIVADO_BATCH) -source $(TCL_DIR)/$(ILA_TCL)
	@echo ""
	@echo "ILA bitstream: $(ILA_BITSTREAM) (+ .ltx probes)"

# ---- Sim + sequences -------------------------------------------------------
sim:                ## Run this build's harness sim (cocotb, no board)
	@[ -n "$(SIM_TESTS)" ] || (echo "SIM_TESTS is not set -- nothing to simulate." && false)
	@echo "[sim] $(SIM_TESTS)"
	cd $(REPO_ROOT) && $(PYTHON) -m pytest $(SIM_TESTS) $(SIM_ARGS)

# `run` drives a PROGRAMMED board through the area's sequences. Port discovery
# is the run script's job (board registry + identity probe), so no UART= here.
run:                ## Run sequences on the board (SEQUENCES="init write_read")
	@[ -n "$(RUN_SCRIPT)" ] || \
	    (echo "No run_*.py found in SEQ_DIR=$(SEQ_DIR)" && false)
	$(PYTHON) $(RUN_SCRIPT) --board $(BOARD) --baud $(BAUD) \
	    $(if $(SEQUENCES),--sequences $(SEQUENCES),)

seq-list:           ## List the sequences this area offers
	@[ -n "$(RUN_SCRIPT)" ] || \
	    (echo "No run_*.py found in SEQ_DIR=$(SEQ_DIR)" && false)
	@$(PYTHON) $(RUN_SCRIPT) --list

# ---- Report shortcuts ------------------------------------------------------
utilization:        ## Print the latest utilization report
	@if [ -f $(REPORTS)/utilization_impl.txt ]; then \
	    echo "=== Post-route utilization ==="; \
	    sed -n '/Slice LUTs\|Slice Registers\|Block RAM Tile\|DSPs\|LUT as Logic\|LUT as Memory/,+0p' \
	        $(REPORTS)/utilization_impl.txt | head -60; \
	elif [ -f $(REPORTS)/utilization_synth.txt ]; then \
	    echo "=== Post-synth utilization (impl not yet run) ==="; \
	    sed -n '/Slice LUTs\|Slice Registers\|Block RAM Tile\|DSPs\|LUT as Logic\|LUT as Memory/,+0p' \
	        $(REPORTS)/utilization_synth.txt | head -60; \
	else \
	    echo "No utilization report yet -- run 'make synth' or 'make bitstream'."; \
	fi

timing:             ## Print the latest timing summary + failing hotspots
	@if [ -f $(REPORTS)/timing_summary.txt ]; then \
	    echo "=== Post-route timing summary (first 60 lines) ==="; \
	    head -60 $(REPORTS)/timing_summary.txt; \
	elif [ -f $(REPORTS)/timing_summary_synth.txt ]; then \
	    echo "=== Post-synth timing summary (first 60 lines) ==="; \
	    head -60 $(REPORTS)/timing_summary_synth.txt; \
	else \
	    echo "No timing report yet -- run 'make synth' or 'make bitstream'."; \
	fi
	@if [ -f $(REPORTS)/timing_failing_hotspots.txt ]; then \
	    echo ""; echo "=== Failing-endpoint hotspots ==="; \
	    head -20 $(REPORTS)/timing_failing_hotspots.txt; \
	fi

# ---- Clean -----------------------------------------------------------------
clean:              ## Remove Vivado artifacts, reports and the bitstream
	@echo "[clean] $(FLOW)"
	rm -rf $(BUILD_DIR) $(REPORTS) $(SELF_DIR)/.Xil
	rm -f  $(BITSTREAM) $(ILA_BITSTREAM)
	rm -f  $(SELF_DIR)/vivado.log $(SELF_DIR)/vivado.jou
	rm -f  $(SELF_DIR)/vivado_*.backup.log $(SELF_DIR)/vivado_*.backup.jou
	rm -f  $(SELF_DIR)/vivado_pid*.str $(SELF_DIR)/hs_err_pid*.log

clean-all: clean    ## clean + logs + Python bytecode
	@echo "[clean-all] $(FLOW)"
	@find $(SELF_DIR) -type d -name __pycache__ -exec rm -rf {} + 2>/dev/null || true
	@find $(SELF_DIR) -type f -name "*.pyc" -delete 2>/dev/null || true
