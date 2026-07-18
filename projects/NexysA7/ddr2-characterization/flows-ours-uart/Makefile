#==============================================================================
# DDR2 Characterization — Nexys A7-100T build & test Makefile
#==============================================================================
# Targets:
#   make help        — this message
#   make project     — create the Vivado project (no build)
#   make synth       — synthesis only + utilization + failing-path reports
#   make bitstream   — synth + impl + bitstream + all reports
#   make program     — program the board with the current bitstream
#   make utilization — print the latest utilization report
#   make timing      — print the latest timing summary
#   make smoke       — run host smoke test against the programmed board
#   make status      — one-shot host status dump against the programmed board
#   make lint        — verilator --lint-only of the whole harness
#   make clean       — remove Vivado work dir, reports, bitstream
#   make clean-all   — clean + logs + Python bytecode
#==============================================================================

# ---- Layout ---------------------------------------------------------------
ifndef REPO_ROOT
$(error REPO_ROOT is not set. Source RTLDesignSherpa/env_python or export REPO_ROOT manually.)
endif

SELF_DIR              := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
export REPO_ROOT
export CHAR_ROOT      := $(REPO_ROOT)/projects/NexysA7/ddr2-characterization
export FLOW_ROOT      := $(SELF_DIR)
export FRAMEWORK_ROOT := $(CHAR_ROOT)/ddr2_char_framework
export CONVERTERS_ROOT:= $(REPO_ROOT)/projects/components/converters

VIVADO ?= vivado
VIVADO_BATCH = $(VIVADO) -mode batch -notrace

TCL      := $(SELF_DIR)/tcl
PROJECT  := $(SELF_DIR)/build/vivado_project/ddr2_char.xpr
BITSTREAM:= $(SELF_DIR)/bitstream/ddr2_char.bit
REPORTS  := $(SELF_DIR)/reports
FILELIST := $(SELF_DIR)/rtl/filelists/ddr2_char_harness.f

# Host driver defaults (override on command line: make smoke UART=/dev/ttyUSB2)
UART ?= /dev/ttyUSB1
BAUD ?= 115200

.PHONY: help project synth bitstream program utilization timing smoke status \
        level simple characterize host-test sim sim-smoke sim-simple sim-level \
        lint clean clean-all

help:
	@echo "DDR2 Characterization — Nexys A7 build targets"
	@echo "  make project      Create Vivado project (no build)"
	@echo "  make synth        Synthesis + utilization + failing-path reports"
	@echo "  make bitstream    Full synth/impl/bitgen + all reports"
	@echo "  make program      Flash the Nexys A7 via JTAG"
	@echo "  make utilization  cat utilization_impl.txt (falls back to synth)"
	@echo "  make timing       cat timing_summary.txt"
	@echo "  make smoke        Run host smoke test (UART=$(UART))"
	@echo "  make status       One-shot host status dump"
	@echo "  make level        a7ddrphy read/write leveling (pumice_master)"
	@echo "  make simple       Init(+leveling) + one write-then-read pass"
	@echo "  make characterize Init + full workload-sweep characterization"
	@echo "  make host-test    Board-less host-logic unit tests (mock UART)"
	@echo "  make sim          Run the SAME programs in sim (cocotb UART, no board)"
	@echo "  make sim-smoke    Sim: BUILD_ID/SCRATCH + tiny write-read"
	@echo "  make sim-simple   Sim: unmodified SimpleTest program"
	@echo "  make sim-level    Sim: unmodified A7Leveling program (DFI loopback)"
	@echo "  make lint         verilator --lint-only of the harness"
	@echo "  make clean        Remove Vivado artifacts + reports + bitstream"
	@echo "  make clean-all    clean + logs + Python bytecode"

# ---- Verilator lint (fast pre-Vivado sanity) ------------------------------
lint:
	@echo "[lint] verilator --lint-only ddr2_char_top"
	@verilator --lint-only --top-module ddr2_char_top \
	    -f $(FILELIST) \
	    +define+USE_ASYNC_RESET \
	    -Wno-MULTIDRIVEN -Wno-UNUSED -Wno-UNDRIVEN -Wno-WIDTH \
	    -Wno-CASEINCOMPLETE -Wno-SELRANGE -Wno-DECLFILENAME \
	    -Wno-UNUSEDSIGNAL -Wno-VARHIDDEN -Wno-IMPLICIT -Wno-CASEOVERLAP \
	    -Wno-MODDUP

# ---- Project creation ------------------------------------------------------
project:
	@echo "[create_project] REPO_ROOT=$(REPO_ROOT)"
	cd $(SELF_DIR) && $(VIVADO_BATCH) -source $(TCL)/create_project.tcl

# ---- Synthesis only --------------------------------------------------------
synth:
	@echo "[synth] synth_1 + utilization + failing-path reports (skip place/route)"
	cd $(SELF_DIR) && $(VIVADO_BATCH) -source $(TCL)/synth_only.tcl
	@$(MAKE) --no-print-directory utilization
	@$(MAKE) --no-print-directory timing

# ---- Full build ------------------------------------------------------------
bitstream:
	@echo "[bitstream] full flow (10-30 min depending on host)"
	cd $(SELF_DIR) && $(VIVADO_BATCH) -source $(TCL)/build_all.tcl
	@echo ""
	@echo "Bitstream: $(BITSTREAM)"
	@echo "Reports:   $(REPORTS)"

# ---- Debug build: same design + an ILA on the DFI-boundary nets ------------
bitstream-ila:
	@echo "[bitstream-ila] build with ILA on the marked DFI-boundary nets"
	cd $(SELF_DIR) && $(VIVADO_BATCH) -source $(TCL)/build_ila.tcl
	@echo ""
	@echo "ILA bitstream: $(SELF_DIR)/bitstream/ddr2_char_ila.bit (+ .ltx probes)"

# ---- Program board ---------------------------------------------------------
program:
	@[ -f $(BITSTREAM) ] || (echo "No bitstream found — run 'make bitstream' first." && false)
	cd $(SELF_DIR) && $(VIVADO_BATCH) -source $(TCL)/program_fpga.tcl

# ---- Host-side smoke / status ---------------------------------------------
smoke:
	@echo "[smoke] running host/run_smoke.py against $(UART)"
	@cd $(SELF_DIR)/host && python3 run_smoke.py --port $(UART) --baud $(BAUD)

status:
	@cd $(SELF_DIR)/host && python3 ddr2_char.py --port $(UART) --baud $(BAUD)

# ---- pumice_master.py orchestration (on-board; needs a programmed FPGA) ----
level:
	@echo "[level] a7ddrphy read/write leveling against $(UART)"
	@cd $(SELF_DIR)/host && python3 pumice_master.py --port $(UART) --baud $(BAUD) --level-only

sweep-rddly:
	@echo "[sweep-rddly] sweep DFI_TUNING.rddata_delay 0..15, report beats_mismatched"
	@cd $(SELF_DIR)/host && python3 sweep_rddata_delay.py --port $(UART) --baud $(BAUD)

train-deskew:
	@echo "[train-deskew] sweep PHY_TIMING.deskew_lo x deskew_hi, find beats_mismatched==0"
	@cd $(SELF_DIR)/host && python3 train_deskew.py --port $(UART) --baud $(BAUD)

simple:
	@echo "[simple] init (+leveling) + one write-then-read integrity pass"
	@cd $(SELF_DIR)/host && python3 pumice_master.py --port $(UART) --baud $(BAUD) --simple

characterize:
	@echo "[characterize] init + full workload-sweep characterization"
	@cd $(SELF_DIR)/host && python3 pumice_master.py --port $(UART) --baud $(BAUD) --full

# ---- board-less host-logic unit tests (mock UART; CI-safe, no FPGA) ----
host-test:
	@echo "[host-test] pytest host/test_pumice_master.py (mock UART, no board)"
	@cd $(SELF_DIR)/host && python3 -m pytest test_pumice_master.py -q

# ---- Same programs, in simulation (cocotb UART master + DFI loopback) ------
# Runs the IDENTICAL host stack (pumice_master / DDR2CharDriver / UARTAxiBridge)
# against ddr2_char_uart_tb_top in verilator, driving the real UART bridge RTL.
# Proves silicon/sim equivalence: same bytes, same code — only the ByteChannel
# differs (pyserial on the board vs a cocotb UARTMaster here). No FPGA needed.
SIM_TEST := $(CHAR_ROOT)/ddr2_char_framework/dv/tests/test_ddr2_char_uart.py

sim:
	@echo "[sim] all UART equivalence tests (cocotb, no board)"
	@cd $(REPO_ROOT) && python3 -m pytest $(SIM_TEST) -q

sim-smoke:
	@cd $(REPO_ROOT) && python3 -m pytest $(SIM_TEST)::test_ddr2_char_uart_smoke -q

sim-simple:
	@cd $(REPO_ROOT) && python3 -m pytest $(SIM_TEST)::test_ddr2_char_uart_simple -q

sim-level:
	@cd $(REPO_ROOT) && python3 -m pytest $(SIM_TEST)::test_ddr2_char_uart_leveling -q

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
	    echo "=== Post-route timing summary (first 60 lines) ==="; \
	    head -60 $(REPORTS)/timing_summary.txt; \
	elif [ -f $(REPORTS)/timing_summary_synth.txt ]; then \
	    echo "=== Post-synth timing summary (first 60 lines) ==="; \
	    head -60 $(REPORTS)/timing_summary_synth.txt; \
	else \
	    echo "No timing report yet — run 'make synth' or 'make bitstream'."; \
	fi
	@if [ -f $(REPORTS)/timing_failing_hotspots.txt ]; then \
	    echo ""; \
	    echo "=== Failing-endpoint hotspots ==="; \
	    head -20 $(REPORTS)/timing_failing_hotspots.txt; \
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
	@echo "[clean-all] removing logs + Python bytecode..."
	find $(SELF_DIR) -type d -name __pycache__ -exec rm -rf {} + 2>/dev/null || true
	find $(SELF_DIR) -type f -name "*.pyc"    -delete 2>/dev/null || true
	@echo "[clean-all] done."
