#==============================================================================
# STREAM Characterization — Nexys A7-100T build & test Makefile
#==============================================================================
# Targets:
#   make help        — this message
#   make project     — create the Vivado project (no build)
#   make synth       — synthesis only + utilization report
#   make bitstream   — synth + impl + bitstream + all reports
#   make program     — program the board with the current bitstream
#   make utilization — print the latest synth utilization report
#   make timing      — print the latest post-route timing summary
#   make sim         — run the cocotb DMA regression (passthrough to pytest)
#   make clean       — remove Vivado work dir, reports, bitstream
#   make cleanall    — clean + remove any __pycache__ / sim logs
#==============================================================================

# ---- Layout ---------------------------------------------------------------
# Resolve the repo root two levels above projects/ (three levels up from here).
SELF_DIR         := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
export STREAM_CHAR_ROOT := $(SELF_DIR)
export REPO_ROOT        := $(abspath $(SELF_DIR)/../../..)
export STREAM_ROOT      := $(REPO_ROOT)/projects/components/stream
export CONVERTERS_ROOT  := $(REPO_ROOT)/projects/components/converters
export MISC_ROOT        := $(REPO_ROOT)/projects/components/misc

VIVADO ?= vivado
# Keep the journal+log for post-mortem (vivado.log / vivado.jou in project dir).
VIVADO_BATCH = $(VIVADO) -mode batch -notrace

TCL      := $(SELF_DIR)/tcl
PROJECT  := $(SELF_DIR)/vivado_project/stream_char.xpr
BITSTREAM:= $(SELF_DIR)/stream_char.bit
REPORTS  := $(SELF_DIR)/reports

.PHONY: help project synth bitstream program utilization timing sim clean clean-all cleanall

help:
	@echo "STREAM Characterization — FPGA build targets"
	@echo "  make project      Create Vivado project (no build)"
	@echo "  make synth        Synthesis + utilization_synth.txt report"
	@echo "  make bitstream    Full synth/impl/bitgen + all reports"
	@echo "  make program      Flash the Nexys A7 via JTAG"
	@echo "  make utilization  cat utilization_impl.txt (post-route)"
	@echo "  make timing       cat timing_summary.txt   (post-route)"
	@echo "  make sim          Run cocotb regression (pytest)"
	@echo "  make clean        Remove Vivado artifacts and reports"
	@echo "  make clean-all    clean + sim caches/logs + Python bytecode"

# ---- Project creation ------------------------------------------------------
project:
	@echo "[create_project] REPO_ROOT=$(REPO_ROOT)"
	cd $(SELF_DIR) && $(VIVADO_BATCH) -source $(TCL)/create_project.tcl

# ---- Synthesis only --------------------------------------------------------
synth:
	@echo "[synth] synth_1 + utilization_synth.txt (skips place/route)"
	cd $(SELF_DIR) && $(VIVADO_BATCH) -source $(TCL)/synth_only.tcl
	@$(MAKE) --no-print-directory utilization

# ---- Full build ------------------------------------------------------------
bitstream:
	@echo "[bitstream] full flow (~10-30 min depending on host)"
	cd $(SELF_DIR) && $(VIVADO_BATCH) -source $(TCL)/build_all.tcl
	@echo ""
	@echo "Bitstream: $(BITSTREAM)"
	@echo "Reports:   $(REPORTS)"

# ---- Program board ---------------------------------------------------------
program:
	@[ -f $(BITSTREAM) ] || (echo "No bitstream found — run 'make bitstream' first." && false)
	cd $(SELF_DIR) && $(VIVADO_BATCH) -source $(TCL)/program_fpga.tcl

# ---- Report shortcuts ------------------------------------------------------
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

# ---- Simulation -----------------------------------------------------------
sim:
	$(MAKE) -C $(SELF_DIR)/dv/tests run-all-full-parallel

# ---- Clean ----------------------------------------------------------------
# clean      — Vivado build artifacts only (project, reports, bitstream, logs).
# clean-all  — everything generated: clean + sim caches + Python bytecode +
#              GTKWave save files + debug synth_run.log. Keeps source RTL,
#              XDC, TCL, Python tests, host tooling, and README.
# cleanall   — legacy alias for clean-all.

clean:
	@echo "[clean] removing Vivado build artifacts..."
	rm -rf $(SELF_DIR)/vivado_project
	rm -rf $(REPORTS)
	rm -f  $(BITSTREAM)
	rm -f  $(SELF_DIR)/vivado.log $(SELF_DIR)/vivado.jou
	rm -f  $(SELF_DIR)/vivado_*.backup.log $(SELF_DIR)/vivado_*.backup.jou
	rm -f  $(SELF_DIR)/vivado_pid*.str $(SELF_DIR)/hs_err_pid*.log
	rm -rf $(SELF_DIR)/.Xil

clean-all: clean
	@echo "[clean-all] removing sim caches, logs, and Python bytecode..."
	rm -rf $(SELF_DIR)/dv/tests/logs
	rm -rf $(SELF_DIR)/dv/tests/local_sim_build
	rm -rf $(SELF_DIR)/dv/tests/GTKW
	rm -f  $(SELF_DIR)/synth_run.log
	find $(SELF_DIR) -type d -name __pycache__ -exec rm -rf {} + 2>/dev/null || true
	find $(SELF_DIR) -type f -name "*.pyc"    -delete 2>/dev/null || true
	@echo "[clean-all] done."

# Backward-compat alias (was the original target name before the dash was added).
cleanall: clean-all
