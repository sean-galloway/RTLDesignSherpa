#==============================================================================
# Timing Characterization - Nexys A7-100T build & program Makefile
#==============================================================================
# Targets:
#   make help        - this message
#   make project     - create the Vivado project (no build)
#   make synth       - synthesis only + utilization_synth.txt
#   make bitstream   - synth + impl + bitstream + all reports
#   make program     - flash the board with the current bitstream
#   make utilization - print the latest synth utilization report
#   make timing      - print the latest post-route timing summary
#   make clean       - remove Vivado work dir, reports, bitstream
#   make clean-all   - clean + Python bytecode + sim caches
#==============================================================================

ifndef REPO_ROOT
$(error REPO_ROOT is not set. Source the repo's env file (env_python) or export REPO_ROOT manually before running make.)
endif

SELF_DIR              := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
export REPO_ROOT
export TIMING_CHAR_ROOT := $(REPO_ROOT)/projects/NexysA7/timing_characterization
export FPGA_FLOW_ROOT   := $(SELF_DIR)

# Top-variant selector. Either:
#   char_top_fpga       (default) - single-clock board wrapper
#   char_top_fpga_mmcm  - MMCM sweep with 4 test clocks + signature accumulators
FPGA_TOP ?= char_top_fpga
export FPGA_TOP

VIVADO ?= vivado
VIVADO_BATCH = $(VIVADO) -mode batch -notrace

TCL       := $(SELF_DIR)/tcl
PROJECT   := $(SELF_DIR)/build/vivado_project/timing_char.xpr
BITSTREAM := $(SELF_DIR)/bitstream/timing_char.bit
REPORTS   := $(SELF_DIR)/reports

.PHONY: help project synth bitstream bitstream-mmcm program utilization timing clean clean-all cleanall

help:
	@echo "Timing Characterization - Nexys A7-100T build targets"
	@echo "  make project          Create Vivado project (no build)"
	@echo "  make synth            Synth + utilization_synth.txt only"
	@echo "  make bitstream        Full synth/impl/bitgen + all reports"
	@echo "  make bitstream-mmcm   MMCM variant with 4 parallel test clocks"
	@echo "  make bitstream-sweep  Loop bitstream across FREQS_MHZ; emit CSV"
	@echo "                          (override list: FREQS_MHZ=\"100 150 ...\")"
	@echo "  make program          Flash the Nexys A7 via JTAG"
	@echo "  make utilization      cat the latest utilization report"
	@echo "  make timing           cat the latest post-route timing summary"
	@echo "  make clean            Remove Vivado artifacts + reports"
	@echo "  make clean-all        clean + sim caches + Python bytecode"

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
	@echo "[bitstream] FPGA_TOP=$(FPGA_TOP) (~10-30 min)"
	cd $(SELF_DIR) && $(VIVADO_BATCH) -source $(TCL)/build_all.tcl
	@echo ""
	@echo "Bitstream: $(BITSTREAM)"
	@echo "Reports:   $(REPORTS)"

# ---- MMCM sweep build -----------------------------------------------------
# Convenience target so a designer doesn't have to remember the env var.
# Builds the char_top_fpga_mmcm top with four parallel char_top instances
# at 150 / 200 / 240 / 300 MHz; Vivado's STA reports per-test-clock WNS
# independently.  Compare those WNS values against the spreadsheet's
# predicted slack to calibrate the seed numbers in
# work/build_fpga_characterization_xlsx.py.
bitstream-mmcm:
	@echo "[bitstream-mmcm] FPGA_TOP=char_top_fpga_mmcm (4-clock sweep)"
	$(MAKE) --no-print-directory bitstream FPGA_TOP=char_top_fpga_mmcm

# ---- Target-frequency sweep (calibration loop) ----------------------------
# Loops the simple char_top_fpga wrapper across multiple TARGET_PERIOD_NS
# values, captures Vivado's per-clock-group WNS at each, and rolls them up
# into reports/sweep_wns.csv for direct feedback into the spreadsheet
# builder.
#
# Override the freq list with:
#   make bitstream-sweep FREQS_MHZ="100 150 200 250 300"
#
# Runs N back-to-back full builds (~10-30 min each).  Each run's reports
# get archived under reports/sweep_<F>MHz/ so they're kept separate.
FREQS_MHZ ?= 100 150 200 250 300

.PHONY: bitstream-sweep
bitstream-sweep:
	@echo "[bitstream-sweep] sweeping FREQS_MHZ=$(FREQS_MHZ)"
	@for f in $(FREQS_MHZ); do \
	    period=$$(awk "BEGIN {printf \"%.4f\", 1000.0 / $$f}"); \
	    echo ""; \
	    echo "================================================================"; \
	    echo " sweep point: $$f MHz  (period $$period ns)"; \
	    echo "================================================================"; \
	    $(MAKE) --no-print-directory bitstream TARGET_PERIOD_NS=$$period \
	        || (echo "bitstream-sweep: bailing at $$f MHz" && exit 1); \
	    mkdir -p $(REPORTS)/sweep_$${f}MHz; \
	    cp $(REPORTS)/timing_summary.txt   $(REPORTS)/sweep_$${f}MHz/ 2>/dev/null || true; \
	    cp $(REPORTS)/timing_worst.txt     $(REPORTS)/sweep_$${f}MHz/ 2>/dev/null || true; \
	    cp $(REPORTS)/utilization_impl.txt $(REPORTS)/sweep_$${f}MHz/ 2>/dev/null || true; \
	done
	@echo ""
	@echo "[bitstream-sweep] aggregating WNS into reports/sweep_wns.csv"
	@python3 $(SELF_DIR)/tools/parse_timing_sweep.py $(REPORTS) $(REPORTS)/sweep_wns.csv
	@echo ""
	@echo "Done. Feed reports/sweep_wns.csv into the spreadsheet builder."

# ---- Program board ---------------------------------------------------------
program:
	@[ -f $(BITSTREAM) ] || (echo "No bitstream found - run 'make bitstream' first." && false)
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
	    echo "No utilization report yet - run 'make synth' or 'make bitstream'."; \
	fi

timing:
	@if [ -f $(REPORTS)/timing_summary.txt ]; then \
	    echo "=== Timing summary (first 60 lines) ==="; \
	    head -60 $(REPORTS)/timing_summary.txt; \
	else \
	    echo "No timing report yet - run 'make bitstream'."; \
	fi

# ---- Clean ----------------------------------------------------------------
clean:
	@echo "[clean] removing Vivado build artifacts..."
	rm -rf $(SELF_DIR)/build
	rm -rf $(REPORTS)
	rm -f  $(BITSTREAM)
	rm -rf $(SELF_DIR)/.Xil
	rm -f  $(SELF_DIR)/vivado.log $(SELF_DIR)/vivado.jou
	rm -f  $(SELF_DIR)/vivado_*.backup.log $(SELF_DIR)/vivado_*.backup.jou
	rm -f  $(SELF_DIR)/vivado_pid*.str $(SELF_DIR)/hs_err_pid*.log

clean-all: clean
	@echo "[clean-all] removing Python bytecode..."
	find $(SELF_DIR) -type d -name __pycache__ -exec rm -rf {} + 2>/dev/null || true
	find $(SELF_DIR) -type f -name "*.pyc"    -delete 2>/dev/null || true
	@echo "[clean-all] done."

cleanall: clean-all
