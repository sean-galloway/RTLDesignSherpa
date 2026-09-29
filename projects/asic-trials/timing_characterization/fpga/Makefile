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
export TIMING_CHAR_ROOT := $(REPO_ROOT)/projects/asic-trials/timing_characterization
export FPGA_FLOW_ROOT   := $(SELF_DIR)

# Companion artifacts (spreadsheet + whitepaper) live one level up.
WORK_DIR := $(TIMING_CHAR_ROOT)/work
DOCS_DIR := $(TIMING_CHAR_ROOT)/docs

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

.PHONY: help project synth bitstream bitstream-mmcm bitstream-sweep program \
        quartus-sweep quartus-sweep-dry \
        utilization timing clean clean-all cleanall \
        xlsx xlsx-asic xlsx-fpga whitepaper whitepaper-asic whitepaper-fpga \
        calibrate docs

help:
	@echo "Timing Characterization - Nexys A7-100T build targets"
	@echo ""
	@echo "Vivado flow:"
	@echo "  make project          Create Vivado project (no build)"
	@echo "  make synth            Synth + utilization_synth.txt only"
	@echo "  make bitstream        Full synth/impl/bitgen + all reports"
	@echo "  make bitstream-mmcm   MMCM variant with 4 parallel test clocks"
	@echo "  make bitstream-sweep  Loop bitstream across FREQS_MHZ; emit CSV"
	@echo "                          (override list: FREQS_MHZ=\"100 150 ...\")"
	@echo "  make program          Flash the Nexys A7 via JTAG"
	@echo ""
	@echo "Quartus flow (timing_characterization TASK-001; no board, STA only):"
	@echo "  make quartus-sweep    map/fit/sta char_top per FREQS_MHZ on QUARTUS_CFG's"
	@echo "                          device; per-FUB slack CSV -> reports/quartus/sweep_wns.csv"
	@echo "                          (QUARTUS_CFG=quartus/sweep_config.example.tcl, QUARTUS_SH=quartus_sh)"
	@echo "  make quartus-sweep-dry  Same plan under plain tclsh, nothing compiled"
	@echo "                          Parameter sweeps: QUARTUS_CFG=quartus/sweeps/<name>.tcl QUARTUS_REPORTS_SUB=<name>"
	@echo ""
	@echo "Reports:"
	@echo "  make utilization      cat the latest utilization report"
	@echo "  make timing           cat the latest post-route timing summary"
	@echo ""
	@echo "Methodology artifacts (no Vivado required):"
	@echo "  make xlsx             Regen BOTH spreadsheets (asap7 + artix7)"
	@echo "  make xlsx-asic        Regen the ASAP7 spreadsheet"
	@echo "  make xlsx-fpga        Regen the Artix-7 spreadsheet"
	@echo "  make whitepaper       Regen BOTH papers (ASIC + FPGA PDFs)"
	@echo "  make whitepaper-asic  Regen the ASIC paper PDF"
	@echo "  make whitepaper-fpga  Regen the FPGA paper PDF"
	@echo ""
	@echo "End-to-end calibration:"
	@echo "  make calibrate        bitstream-sweep + copy CSV + xlsx-fpga"
	@echo "                          (one command: Vivado WNS -> spreadsheet)"
	@echo "  make docs             xlsx + whitepaper (all methodology output)"
	@echo ""
	@echo "Cleanup:"
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

# ---- Quartus target-frequency sweep ----------------------------------------
# The Quartus twin of bitstream-sweep: one project per frequency under
# build/quartus/<F>MHz (git-ignored), summaries + per-FUB slack under
# reports/quartus/sweep_<F>MHz/, rolled up by the same parser with
# --tool quartus. Device, I/O split and parameters come from QUARTUS_CFG;
# FREQS_MHZ from the command line overrides the config's list. Quartus Prime
# Lite 24.1std installs to ~/intelFPGA_lite/24.1std/quartus/bin and is not on
# PATH by default -- point QUARTUS_SH at it or add that dir to PATH.
QUARTUS_SH  ?= quartus_sh
QUARTUS_CFG ?= $(SELF_DIR)/quartus/sweep_config.example.tcl
# The sweep script cd's to the area root, so a QUARTUS_CFG given relative to
# fpga/ (quartus/sweeps/carry_width.tcl) must be made absolute here.
QUARTUS_CFG_ABS := $(abspath $(QUARTUS_CFG))
# FREQS_MHZ reaches the script only when given on the command line; otherwise
# the config's own list stands (a parameter sweep pins one frequency there).
QUARTUS_FREQS_ARG := $(if $(filter command line,$(origin FREQS_MHZ)),-freqs "$(FREQS_MHZ)")
# A parameter sweep (fpga/quartus/sweeps/*.tcl) writes under reports/quartus/<name>;
# pass QUARTUS_REPORTS_SUB=<name> so the aggregation reads the same place.
QUARTUS_REPORTS_SUB ?=
QUARTUS_REPORTS := $(REPORTS)/quartus$(if $(QUARTUS_REPORTS_SUB),/$(QUARTUS_REPORTS_SUB))

.PHONY: quartus-sweep
quartus-sweep:
	@command -v $(QUARTUS_SH) >/dev/null 2>&1 || { \
	    echo "quartus-sweep: '$(QUARTUS_SH)' not found. Quartus Prime Lite installs to"; \
	    echo "  ~/intelFPGA_lite/<ver>/quartus/bin -- run with QUARTUS_SH=<that>/quartus_sh"; \
	    echo "  or add the directory to PATH. Use 'make quartus-sweep-dry' to check the plan."; \
	    exit 1; }
	@echo "[quartus-sweep] cfg=$(QUARTUS_CFG_ABS) $(if $(QUARTUS_FREQS_ARG),FREQS_MHZ=$(FREQS_MHZ),FREQS from the config)"
	cd $(TIMING_CHAR_ROOT) && $(QUARTUS_SH) -t $(SELF_DIR)/quartus/syn_sweep_quartus.tcl $(QUARTUS_CFG_ABS) $(QUARTUS_FREQS_ARG)
	@echo ""
	@echo "[quartus-sweep] aggregating into $(QUARTUS_REPORTS)/sweep_wns.csv"
	@python3 $(SELF_DIR)/tools/parse_timing_sweep.py --tool quartus $(QUARTUS_REPORTS) $(QUARTUS_REPORTS)/sweep_wns.csv

.PHONY: quartus-sweep-dry
quartus-sweep-dry:
	cd $(TIMING_CHAR_ROOT) && TCL_LIBRARY=$${TCL_LIBRARY:-/usr/share/tcltk/tcl8.6} tclsh $(SELF_DIR)/quartus/syn_sweep_quartus.tcl $(QUARTUS_CFG_ABS) $(QUARTUS_FREQS_ARG) -dry-run

# ---- Program board ---------------------------------------------------------
# program / ports / board-info / boards come from the shared board layer. The
# per-flow tcl this replaces pinned NO serial at all --
# `current_hw_target [get_hw_targets */xilinx_tcf/*]` takes whatever Vivado
# lists first, which with two boards on the chain is a coin flip.
# Handbook: vault/handbook/fpga/cmn-infra/boards.md
FLOW ?= timing-char
include $(REPO_ROOT)/make/fpga_board.mk

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

# ---- Spreadsheet regeneration --------------------------------------------
# Pure Python; no Vivado, no board, no synth runs. The Artix-7 builder
# automatically picks up work/sweep_wns.csv if one is present (written by
# `make calibrate`) and appends a 'measured (sweep)' sheet.
xlsx: xlsx-asic xlsx-fpga

xlsx-asic:
	@echo "[xlsx-asic] regenerating asap7_characterization.xlsx"
	@python3 $(WORK_DIR)/build_characterization_xlsx.py

xlsx-fpga:
	@echo "[xlsx-fpga] regenerating artix7_characterization.xlsx"
	@python3 $(WORK_DIR)/build_fpga_characterization_xlsx.py

# ---- White paper regeneration --------------------------------------------
# Wraps the existing generate_wp_*_pdf.sh scripts under docs/. Run from
# wherever; the scripts cd into docs/ themselves.
whitepaper: whitepaper-asic whitepaper-fpga

whitepaper-asic:
	@echo "[whitepaper-asic] regenerating Pre_Synth_Timing_Prediction_White_Paper PDF"
	@cd $(DOCS_DIR) && ./generate_wp_pdf.sh

whitepaper-fpga:
	@echo "[whitepaper-fpga] regenerating Pre_Synth_Timing_Prediction_FPGA PDF"
	@cd $(DOCS_DIR) && ./generate_wp_fpga_pdf.sh

# ---- End-to-end calibration loop -----------------------------------------
# 1. bitstream-sweep across FREQS_MHZ -> reports/sweep_wns.csv
# 2. copy that CSV next to the FPGA spreadsheet builder
# 3. regenerate the spreadsheet (now with a 'measured (sweep)' sheet)
# 4. regenerate the FPGA white paper PDF for distribution
#
# Skip the synthesis runs if you already have a fresh sweep_wns.csv by
# pointing at a cached one:
#   make calibrate CALIBRATION_SRC=/path/to/sweep_wns.csv
CALIBRATION_SRC ?= $(REPORTS)/sweep_wns.csv

calibrate:
	@if [ ! -f $(CALIBRATION_SRC) ]; then \
	    echo "[calibrate] no $(CALIBRATION_SRC) yet - running bitstream-sweep first"; \
	    $(MAKE) --no-print-directory bitstream-sweep; \
	fi
	@echo "[calibrate] using $(CALIBRATION_SRC)"
	@cp $(CALIBRATION_SRC) $(WORK_DIR)/sweep_wns.csv
	@$(MAKE) --no-print-directory xlsx-fpga
	@$(MAKE) --no-print-directory whitepaper-fpga
	@echo ""
	@echo "Calibration done."
	@echo "  Spreadsheet:  $(WORK_DIR)/artix7_characterization.xlsx"
	@echo "  Sweep CSV:    $(WORK_DIR)/sweep_wns.csv"
	@echo "  White paper:  $(DOCS_DIR)/Pre_Synth_Timing_Prediction_FPGA_v*.pdf"

# ---- 'docs' rolls up everything that doesn't need Vivado -----------------
docs: xlsx whitepaper
