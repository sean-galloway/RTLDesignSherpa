#==============================================================================
# RAPIDS Characterization — Nexys A7-100T build & test Makefile
#==============================================================================
# End-to-end flow for the split RAPIDS beats DUT + characterization harness:
#
#   make sim          Run the cocotb harness self-check (sink + source, multi-channel)
#   make synth        Synthesis only + utilization/timing reports (fast "does it fit/build")
#   make bitstream    Full synth + impl + bitstream + reports ("build the bridge")
#   make program      Flash the Nexys A7 via JTAG
#   make characterize Run the UART characterization campaign against the board
#   make flow         sim -> bitstream -> program -> characterize (the whole thing)
#
#   make project      Create the Vivado project (no build)
#   make utilization  Print the latest utilization report
#   make timing       Print the latest post-route timing summary
#   make clean        Remove Vivado work dir, reports, bitstream
#   make clean-all    clean + sim caches/logs + Python bytecode
#
# Knobs (override on the command line):
#   CHANNELS=4   NUM_CHANNELS the bitstream is built with AND the host drives.
#                The build generic and the host --channels are kept in lockstep.
#   ACTIVE=4     active channels the characterization exercises (<= CHANNELS)
#   BEATS=8      beats per channel
#   PORT=/dev/ttyUSB1   serial device for `characterize` / `program`
#   BITSTREAM_SKIP_VERIFY=1   bypass the pre-bitstream sim gate
#==============================================================================

# ---- Layout ---------------------------------------------------------------
# REPO_ROOT must be set in the environment (source env_python). Hard-fail so
# the failure mode is obvious rather than a mysterious wrong-path build.
ifndef REPO_ROOT
$(error REPO_ROOT is not set. Source the repo's env file (env_python) or export REPO_ROOT manually before running make.)
endif

SELF_DIR         := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
export REPO_ROOT
export CHAR_ROOT := $(REPO_ROOT)/projects/NexysA7/rapids_characterization
export FLOW_ROOT := $(SELF_DIR)

VIVADO      ?= vivado
VIVADO_BATCH = $(VIVADO) -mode batch -notrace

TCL       := $(SELF_DIR)/tcl
PROJECT   := $(SELF_DIR)/build/vivado_project/rapids_char.xpr
BITSTREAM := $(SELF_DIR)/bitstream/rapids_char.bit
REPORTS   := $(SELF_DIR)/reports

HARNESS_TEST := projects/NexysA7/rapids_characterization/flows-rapids-beats/dv/test_rapids_char_harness.py

# ---- Board target ----------------------------------------------------------
# BOARD selects the FPGA target: nexys (Artix-7 100T, default) or genesys2
# (Kintex-7 325T-2). Passed through to create_project.tcl; the genesys2 build
# uses the rapids_char_genesys2_top wrapper (MMCM 200->100 MHz) and defaults to
# the full 8-channel geometry.
BOARD ?= nexys
export BOARD

# ---- Characterization knobs -----------------------------------------------
# CHANNELS is exported as the build generic (RAPIDS_NUM_CHANNELS) AND passed to
# the host, so the bitstream and the host campaign can never silently disagree.
# Default follows the board: 8 on the roomy Genesys 2, 4 on the tight Nexys.
ifeq ($(BOARD),genesys2)
CHANNELS ?= 8
else
CHANNELS ?= 4
endif
ACTIVE   ?= $(CHANNELS)
BEATS    ?= 8
PORT     ?= /dev/ttyUSB1
export RAPIDS_NUM_CHANNELS := $(CHANNELS)

.PHONY: help sim verify-sim project synth bitstream program characterize \
        smoke suite flow utilization timing clean clean-all cleanall

help:
	@echo "RAPIDS Characterization — FPGA build & characterization targets"
	@echo "  make sim          cocotb harness self-check (sink + source, multi-channel)"
	@echo "  make synth        synthesis only + utilization/timing reports"
	@echo "  make bitstream    full synth/impl/bitgen + reports"
	@echo "  make program      flash the Nexys A7 via JTAG"
	@echo "  make characterize run the UART characterization campaign (needs board on PORT)"
	@echo "  make smoke        fast golden-validated confidence check (sink + source)"
	@echo "  make suite        full characterization sweep (channels x beats x bp x seed)"
	@echo "  make flow         sim -> bitstream -> program -> characterize"
	@echo "  make project      create the Vivado project (no build)"
	@echo "  make utilization  print utilization report"
	@echo "  make timing       print post-route timing summary"
	@echo "  make clean / clean-all"
	@echo ""
	@echo "  CHANNELS=$(CHANNELS) ACTIVE=$(ACTIVE) BEATS=$(BEATS) PORT=$(PORT)"

# ---- Simulation -----------------------------------------------------------
# The harness self-check IS the characterization, run in sim: a multi-channel
# sink pass (axis gen -> sink -> m_axi_wr, per-channel CRC == gen expected) and
# source pass (m_axi_rd -> source -> m_axis, per-channel CRC == chk actual).
sim:
	cd $(REPO_ROOT) && . ./env_python && \
	    pytest $(HARNESS_TEST) -v

# ---- Pre-bitstream sim gate -----------------------------------------------
# Cheap insurance: the sink self-check must pass before a 10-30 min build.
# Bypass with:  make bitstream BITSTREAM_SKIP_VERIFY=1
verify-sim:
	@if [ "$(BITSTREAM_SKIP_VERIFY)" = "1" ]; then \
	    echo "[verify-sim] skipped (BITSTREAM_SKIP_VERIFY=1)"; \
	else \
	    echo "[verify-sim] running rapids_char harness sink self-check"; \
	    cd $(REPO_ROOT) && . ./env_python && \
	      pytest $(HARNESS_TEST) -q -k sink \
	      || (echo "[verify-sim] FAILED — refusing to start synth/bitstream" && exit 1); \
	fi

# ---- Project creation ------------------------------------------------------
project:
	@echo "[create_project] REPO_ROOT=$(REPO_ROOT) NUM_CHANNELS=$(CHANNELS)"
	cd $(SELF_DIR) && $(VIVADO_BATCH) -source $(TCL)/create_project.tcl

# ---- Synthesis only --------------------------------------------------------
synth: verify-sim
	@echo "[synth] synth_1 + utilization_synth.txt (skips place/route)"
	cd $(SELF_DIR) && $(VIVADO_BATCH) -source $(TCL)/synth_only.tcl
	@$(MAKE) --no-print-directory utilization

# ---- Full build (build the bridge + bitstream) -----------------------------
bitstream: verify-sim
	@echo "[bitstream] full flow (~10-30 min depending on host), NUM_CHANNELS=$(CHANNELS)"
	cd $(SELF_DIR) && $(VIVADO_BATCH) -source $(TCL)/build_all.tcl
	@echo ""
	@echo "Bitstream: $(BITSTREAM)"
	@echo "Reports:   $(REPORTS)"

# ---- Program board ---------------------------------------------------------
program:
	@[ -f $(BITSTREAM) ] || (echo "No bitstream found — run 'make bitstream' first." && false)
	cd $(SELF_DIR) && $(VIVADO_BATCH) -source $(TCL)/program_fpga.tcl

# ---- UART characterization -------------------------------------------------
# Drives the programmed board over UART: config SRC+SNK by name, load
# descriptors, run the multi-channel sink + source passes, report per-channel
# PASS/FAIL. --channels MUST match the built NUM_CHANNELS (kept == CHANNELS).
characterize:
	@echo "[characterize] UART campaign on $(PORT): channels=$(CHANNELS) active=$(ACTIVE) beats=$(BEATS)"
	cd $(REPO_ROOT) && . ./env_python && \
	    python3 $(SELF_DIR)/host/run_characterization.py \
	        --port $(PORT) --channels $(CHANNELS) --active $(ACTIVE) --beats $(BEATS)

# ---- Fast confidence check -------------------------------------------------
# A couple-second golden-validated sink+source smoke test over UART. Exits
# non-zero on failure. --channels stays in lockstep with the build.
smoke:
	@echo "[smoke] UART golden-validated confidence check on $(PORT): channels=$(CHANNELS)"
	cd $(REPO_ROOT) && . ./env_python && \
	    python3 $(SELF_DIR)/host/run_characterization.py \
	        --port $(PORT) --channels $(CHANNELS) --smoke

# ---- Full characterization suite -------------------------------------------
# Sweeps active-channels x beats x source-backpressure x base-seed, runs both
# paths per config with golden validation, prints a summary table, and emits a
# JSON results file under reports/.
suite:
	@echo "[suite] UART characterization sweep on $(PORT): channels=$(CHANNELS)"
	cd $(REPO_ROOT) && . ./env_python && \
	    python3 $(SELF_DIR)/host/run_characterization.py \
	        --port $(PORT) --channels $(CHANNELS) --suite

# ---- Whole flow ------------------------------------------------------------
# The full sequence the way you'd run it on the bench: prove it in sim, build
# the bitstream, flash the board, then characterize over UART.
flow: sim bitstream program characterize
	@echo "[flow] complete: sim -> bitstream -> program -> characterize"

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
	elif [ -f $(REPORTS)/timing_summary_synth.txt ]; then \
	    echo "=== Post-synth timing summary (impl not yet run) ==="; \
	    head -60 $(REPORTS)/timing_summary_synth.txt; \
	else \
	    echo "No timing report yet — run 'make synth' or 'make bitstream'."; \
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
	@echo "[clean-all] removing sim caches, logs, and Python bytecode..."
	rm -rf $(SELF_DIR)/dv/local_sim_build
	rm -rf $(SELF_DIR)/dv/logs
	find $(SELF_DIR) -type d -name __pycache__ -exec rm -rf {} + 2>/dev/null || true
	find $(SELF_DIR) -type f -name "*.pyc"    -delete 2>/dev/null || true
	@echo "[clean-all] done."

cleanall: clean-all
