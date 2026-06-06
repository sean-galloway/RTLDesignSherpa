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
export STREAM_CHAR_ROOT  := $(SELF_DIR)
export FRAMEWORK_ROOT    := $(CHAR_ROOT)/stream_char_framework
export DOCS_ROOT         := $(CHAR_ROOT)/docs
export STREAM_ROOT       := $(REPO_ROOT)/projects/components/stream
export CONVERTERS_ROOT   := $(REPO_ROOT)/projects/components/converters
export MISC_ROOT         := $(REPO_ROOT)/projects/components/misc

VIVADO ?= vivado
# Keep the journal+log for post-mortem (vivado.log / vivado.jou in project dir).
VIVADO_BATCH = $(VIVADO) -mode batch -notrace

TCL      := $(SELF_DIR)/tcl

PROJECT  := $(SELF_DIR)/build/vivado_project/stream_char.xpr
BITSTREAM:= $(SELF_DIR)/bitstream/stream_char.bit
REPORTS  := $(SELF_DIR)/reports

.PHONY: help project synth bitstream program utilization timing sim clean clean-all cleanall regen-bridges verify-sim

# Regenerate every framework-owned bridge before any synthesis. Cheap
# (~seconds), keeps the bridge RTL + filelist consistent with the .toml,
# and means a stale checkout can't silently produce a stale bitstream.
REGEN_BRIDGES := $(FRAMEWORK_ROOT)/bin/regen_bridges.sh

help:
	@echo "STREAM Characterization — FPGA build targets"
	@echo "  make regen-bridges Regenerate framework bridges (RTL + filelist + TBs)"
	@echo "  make project      Create Vivado project (no build)"
	@echo "  make synth        regen-bridges + synthesis + utilization_synth.txt"
	@echo "  make bitstream    regen-bridges + full synth/impl/bitgen + all reports"
	@echo "  make program      Flash the Nexys A7 via JTAG"
	@echo "  make utilization  cat utilization_impl.txt (post-route)"
	@echo "  make timing       cat timing_summary.txt   (post-route)"
	@echo "  make sim          Run cocotb regression (pytest)"
	@echo "  make clean        Remove Vivado artifacts and reports"
	@echo "  make clean-all    clean + sim caches/logs + Python bytecode"

# ---- Bridge regeneration --------------------------------------------------
# Always re-runs (the script itself is fast and idempotent). Synth/bitstream
# depend on this so a stale checkout can't silently feed stale bridge RTL
# into Vivado.
regen-bridges:
	@$(REGEN_BRIDGES)

# ---- Pre-bitstream sim verification ---------------------------------------
# Runs the stream_char FUNC ping + csr_read sanity tests against the current
# RTL. Catches the case where a refactor (e.g. monitor reporter sub-block
# split, perfmon plumbing, bridge regen) breaks elaboration but the user
# kicks off a 10-30 min bitstream build without noticing. ~2 minutes
# on a warm cache; cheap insurance.
#
# Override:  make bitstream BITSTREAM_SKIP_VERIFY=1  to bypass.
verify-sim:
	@if [ "$(BITSTREAM_SKIP_VERIFY)" = "1" ]; then \
	    echo "[verify-sim] skipped (BITSTREAM_SKIP_VERIFY=1)"; \
	else \
	    echo "[verify-sim] running stream_char FUNC ping + csr_read"; \
	    cd $(REPO_ROOT) && . env_python && \
	      pytest projects/NexysA7/stream_characterization/flows-stream-bridge/dv/tests/test_stream_char.py \
	        -v -k "ping or csr_read" \
	      || (echo "[verify-sim] FAILED — refusing to start synth/bitstream" && exit 1); \
	fi

# ---- Project creation ------------------------------------------------------
project:
	@echo "[create_project] REPO_ROOT=$(REPO_ROOT)"
	cd $(SELF_DIR) && $(VIVADO_BATCH) -source $(TCL)/create_project.tcl

# ---- Synthesis only --------------------------------------------------------
synth: regen-bridges verify-sim
	@echo "[synth] synth_1 + utilization_synth.txt (skips place/route)"
	cd $(SELF_DIR) && $(VIVADO_BATCH) -source $(TCL)/synth_only.tcl
	@$(MAKE) --no-print-directory utilization

# ---- Full build ------------------------------------------------------------
bitstream: regen-bridges verify-sim
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
	rm -rf $(SELF_DIR)/build
	rm -rf $(REPORTS)
	rm -f  $(BITSTREAM)
	rm -rf $(SELF_DIR)/.Xil
	# Belt-and-suspenders: kill stale Vivado droppings that escaped build/.
	rm -f  $(SELF_DIR)/vivado.log $(SELF_DIR)/vivado.jou
	rm -f  $(SELF_DIR)/vivado_*.backup.log $(SELF_DIR)/vivado_*.backup.jou
	rm -f  $(SELF_DIR)/vivado_pid*.str $(SELF_DIR)/hs_err_pid*.log
	rm -f  $(SELF_DIR)/run.log

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
