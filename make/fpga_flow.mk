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
# Vivado creates its project under $project_root/build, and project_root is
# FPGA_PROJECT_ROOT below -- so this must track FPGA_DIR or `make clean` would
# miss the very directory the build wrote.
BUILD_DIR  ?= $(FPGA_DIR)/build
PROJECT    ?= $(BUILD_DIR)/vivado_project/$(FLOW).xpr

# ---- Tools -----------------------------------------------------------------
VIVADO       ?= vivado
VIVADO_BATCH ?= $(VIVADO) -mode batch -notrace
PYTHON       ?= python3
VERILATOR    ?= verilator

# ---- Tcl scripts: DISCOVERED, never enumerated -----------------------------
# Every fpga/tcl/*.tcl becomes a `make tcl-<name>` target the moment it lands --
# same discipline as make/tests.mk globbing test_*.py. There is no list to keep
# in sync, so a new script is runnable without editing any Makefile.
TCL_SCRIPTS := $(sort $(notdir $(wildcard $(TCL_DIR)/*.tcl)))
TCL_NAMES   := $(basename $(TCL_SCRIPTS))
# Helpers included BY other scripts, not run on their own.
TCL_HELPERS ?= filelist_utils
TCL_RUNNABLE := $(filter-out $(TCL_HELPERS),$(TCL_NAMES))

# The four semantic targets map onto conventional script names when present.
# Override the variable if a build names them differently; the rule never
# changes, and a missing script fails with a readable message, not a Vivado one.
PROJECT_TCL ?= $(if $(filter create_project,$(TCL_NAMES)),create_project.tcl,)
SYNTH_TCL   ?= $(if $(filter synth_only,$(TCL_NAMES)),synth_only.tcl,)
BUILD_TCL   ?= $(if $(filter build_all,$(TCL_NAMES)),build_all.tcl,)
ILA_TCL     ?= $(if $(filter build_ila,$(TCL_NAMES)),build_ila.tcl,)

# Vivado reads the layout from the environment rather than guessing it from
# where the script sits, so moving a build does not silently relocate outputs.
export FPGA_PROJECT_ROOT := $(FPGA_DIR)

# ---- Host / sim entry points -----------------------------------------------
BAUD      ?= 115200
SEQ_DIR   ?=
# run_*.py in the sequence area are DISCOVERED too: each becomes `make run-<name>`.
RUN_SCRIPTS := $(sort $(wildcard $(SEQ_DIR)/run_*.py))
RUN_NAMES   := $(patsubst run_%,%,$(basename $(notdir $(RUN_SCRIPTS))))
RUN_SCRIPT  ?= $(firstword $(RUN_SCRIPTS))
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
        utilization timing clean clean-all targets \
        $(addprefix tcl-,$(TCL_RUNNABLE)) $(addprefix run-,$(RUN_NAMES))

# Run any discovered tcl by name: `make tcl-capture_ila`.
define _tcl_rule
tcl-$(1):
	@echo "[tcl] $(1).tcl"
	cd $$(SELF_DIR) && $$(VIVADO_BATCH) -source $$(TCL_DIR)/$(1).tcl
endef
$(foreach t,$(TCL_RUNNABLE),$(eval $(call _tcl_rule,$(t))))

# Run any discovered run_*.py by name: `make run-smoke`.
define _run_rule
run-$(1):
	$$(PYTHON) $$(SEQ_DIR)/run_$(1).py --board $$(BOARD) --baud $$(BAUD) \
	    $$(if $$(SEQUENCES),--sequences $$(SEQUENCES),)
endef
$(foreach r,$(RUN_NAMES),$(eval $(call _run_rule,$(r))))

targets:            ## Show what was DISCOVERED on disk (tcl scripts, run scripts)
	@echo "tcl scripts in $(TCL_DIR):"
	@$(if $(TCL_RUNNABLE),for t in $(TCL_RUNNABLE); do echo "    make tcl-$$t"; done,echo "    (none)")
	@echo "  helpers (sourced, not run): $(if $(TCL_HELPERS),$(TCL_HELPERS),none)"
	@echo "run scripts in $(SEQ_DIR):"
	@$(if $(RUN_NAMES),for r in $(RUN_NAMES); do echo "    make run-$$r"; done,echo "    (none)")
	@echo "semantic targets -> script:"
	@echo "    project       $(if $(PROJECT_TCL),$(PROJECT_TCL),MISSING)"
	@echo "    synth         $(if $(SYNTH_TCL),$(SYNTH_TCL),MISSING)"
	@echo "    bitstream     $(if $(BUILD_TCL),$(BUILD_TCL),MISSING)"
	@echo "    bitstream-ila $(if $(ILA_TCL),$(ILA_TCL),MISSING)"

# A semantic target whose script is absent should say so, not hand Vivado an
# empty -source argument.
_require_tcl = @[ -n "$(1)" ] || (echo "No $(2) script found in $(TCL_DIR) -- \
	set $(3) or add one (make targets shows what was discovered)." && false)

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
	$(call _require_tcl,$(PROJECT_TCL),create_project,PROJECT_TCL)
	@echo "[project] $(FLOW)"
	cd $(SELF_DIR) && $(VIVADO_BATCH) -source $(TCL_DIR)/$(PROJECT_TCL)

synth:              ## Synthesis only + utilization + failing-path reports
	$(call _require_tcl,$(SYNTH_TCL),synth,SYNTH_TCL)
	@echo "[synth] $(FLOW) (skip place/route)"
	cd $(SELF_DIR) && $(VIVADO_BATCH) -source $(TCL_DIR)/$(SYNTH_TCL)
	@$(MAKE) --no-print-directory utilization
	@$(MAKE) --no-print-directory timing

bitstream:          ## Full synth/impl/bitgen + all reports (10-30 min)
	$(call _require_tcl,$(BUILD_TCL),build,BUILD_TCL)
	@echo "[bitstream] $(FLOW) full flow"
	cd $(SELF_DIR) && $(VIVADO_BATCH) -source $(TCL_DIR)/$(BUILD_TCL)
	@echo ""
	@echo "Bitstream: $(BITSTREAM)"
	@echo "Reports:   $(REPORTS)"

bitstream-ila:      ## Same design plus an ILA on the marked debug nets
	$(call _require_tcl,$(ILA_TCL),ILA build,ILA_TCL)
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
