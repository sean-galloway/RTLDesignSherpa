#==============================================================================
# Vivado MCDMA Characterization — Nexys A7-100T build & test Makefile
#==============================================================================
# STATUS: SKELETON. `make project` and `make synth` work; `make bitstream`
# elaborates a stub harness that doesn't yet drive MCDMA.  See README.md.
#
# Targets:
#   make help        — this message
#   make project     — create the Vivado project (no build)
#   make synth       — synthesis only + utilization report
#   make bitstream   — synth + impl + bitstream + all reports
#   make program     — program the board with the current bitstream
#   make utilization — print the latest synth utilization report
#   make timing      — print the latest post-route timing summary
#   make clean       — remove build/, reports, bitstream
#   make clean-all   — clean + remove __pycache__ / sim caches
#==============================================================================

# ---- Layout ---------------------------------------------------------------
# REPO_ROOT must be set in the environment (e.g. by sourcing env_python).
# We don't compute it from relative paths — too brittle when the directory
# tree gets reshuffled. Hard-fail here so the failure mode is obvious.
ifndef REPO_ROOT
$(error REPO_ROOT is not set. Source the repo's env file (env_python) or export REPO_ROOT manually before running make.)
endif

SELF_DIR                 := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
export REPO_ROOT
export CHAR_ROOT         := $(REPO_ROOT)/projects/NexysA7/stream_characterization
export FLOW_ROOT         := $(SELF_DIR)
export MCDMA_FLOW_ROOT   := $(SELF_DIR)
export FRAMEWORK_ROOT    := $(CHAR_ROOT)/stream_char_framework
export RTL_VIVADO_ROOT   := $(CHAR_ROOT)/rtl-vivado
export DOCS_ROOT         := $(CHAR_ROOT)/docs
export STREAM_ROOT       := $(REPO_ROOT)/projects/components/stream
export CONVERTERS_ROOT   := $(REPO_ROOT)/projects/components/converters
export MISC_ROOT         := $(REPO_ROOT)/projects/components/misc

VIVADO ?= vivado
VIVADO_BATCH = $(VIVADO) -mode batch -notrace

TCL      := $(SELF_DIR)/tcl

PROJECT  := $(SELF_DIR)/build/vivado_project/vivado_mcdma.xpr
BITSTREAM:= $(SELF_DIR)/bitstream/vivado_mcdma.bit
REPORTS  := $(SELF_DIR)/reports

.PHONY: help project synth bitstream program utilization timing sim clean clean-all cleanall

help:
	@echo "Vivado MCDMA Characterization — FPGA build targets"
	@echo "  make project      Create Vivado project (no build)"
	@echo "  make synth        Synthesis + utilization_synth.txt report"
	@echo "  make bitstream    Full synth/impl/bitgen + all reports"
	@echo "  make program      Flash the Nexys A7 via JTAG"
	@echo "  make utilization  cat utilization_impl.txt (post-route)"
	@echo "  make timing       cat timing_summary.txt   (post-route)"
	@echo "  make clean        Remove build/, reports, bitstream"
	@echo "  make clean-all    clean + sim caches/logs + Python bytecode"

project:
	@echo "[create_project] REPO_ROOT=$(REPO_ROOT)"
	cd $(SELF_DIR) && $(VIVADO_BATCH) -source $(TCL)/create_project.tcl

synth:
	@echo "[synth] synth_1 + utilization_synth.txt (skips place/route)"
	cd $(SELF_DIR) && $(VIVADO_BATCH) -source $(TCL)/synth_only.tcl
	@$(MAKE) --no-print-directory utilization

bitstream:
	@echo "[bitstream] full flow (~10-30 min depending on host)"
	cd $(SELF_DIR) && $(VIVADO_BATCH) -source $(TCL)/build_all.tcl
	@echo ""
	@echo "Bitstream: $(BITSTREAM)"
	@echo "Reports:   $(REPORTS)"

program:
	@[ -f $(BITSTREAM) ] || (echo "No bitstream found — run 'make bitstream' first." && false)
	cd $(SELF_DIR) && $(VIVADO_BATCH) -source $(TCL)/program_fpga.tcl

# ---- Sim ------------------------------------------------------------------
# This flow is FPGA-only validated. The Vivado MCDMA IP is delivered as
# VHDL, which Verilator (our cocotb default) cannot simulate. See
# dv/README.md for the rationale and how to wire xsim if you need
# pre-silicon regression here.
sim:
	@echo ""
	@echo "  flows-vivado-mcdma is FPGA-only validated; there is no cocotb"
	@echo "  regression for this flow. See dv/README.md for the rationale."
	@echo ""
	@echo "  Bring-up loop instead:"
	@echo "    make project    # validate IP imports + elaborates"
	@echo "    make synth      # validate it fits"
	@echo "    make bitstream  # validate it routes + meets timing"
	@echo "    make program    # flash to the Nexys A7"
	@echo "    cmds.sh         # exercise on-board with UART"
	@echo ""
	@false

utilization:
	@if [ -f $(REPORTS)/utilization_impl.txt ]; then \
	    echo "=== Post-route utilization ==="; \
	    sed -n '/Slice LUTs\|Slice Registers\|Block RAM Tile\|DSPs\|LUT as Logic\|LUT as Memory/,+0p' \
	        $(REPORTS)/utilization_impl.txt | head -60; \
	elif [ -f $(REPORTS)/utilization_synth.txt ]; then \
	    echo "=== Post-synth utilization (impl not yet run) ==="; \
	    sed -n '/Slice LUTs\|Slice Registers\|Block RAM Tile\|DSPs\|LUT as Logic\|LUT as Memory/,+0p' \
	        $(REPORTS)/utilization_synth.txt | head -60; \
	else \
	    echo "No utilization report yet — run 'make synth' or 'make bitstream'."; \
	fi

timing:
	@if [ -f $(REPORTS)/timing_summary.txt ]; then \
	    echo "=== Timing summary (first 60 lines) ==="; \
	    head -60 $(REPORTS)/timing_summary.txt; \
	else \
	    echo "No timing report yet — run 'make bitstream'."; \
	fi

clean:
	@echo "[clean] removing build artifacts..."
	rm -rf $(SELF_DIR)/build
	rm -rf $(REPORTS)
	rm -f  $(BITSTREAM)
	rm -rf $(SELF_DIR)/.Xil
	rm -f  $(SELF_DIR)/vivado.log $(SELF_DIR)/vivado.jou
	rm -f  $(SELF_DIR)/vivado_*.backup.log $(SELF_DIR)/vivado_*.backup.jou
	rm -f  $(SELF_DIR)/vivado_pid*.str $(SELF_DIR)/hs_err_pid*.log
	rm -f  $(SELF_DIR)/run.log

clean-all: clean
	@echo "[clean-all] removing sim caches, logs, and Python bytecode..."
	rm -rf $(SELF_DIR)/dv/tests/logs
	rm -rf $(SELF_DIR)/dv/tests/local_sim_build
	rm -rf $(SELF_DIR)/dv/tests/GTKW
	find $(SELF_DIR) -type d -name __pycache__ -exec rm -rf {} + 2>/dev/null || true
	find $(SELF_DIR) -type f -name "*.pyc"    -delete 2>/dev/null || true
	@echo "[clean-all] done."

cleanall: clean-all
