#==============================================================================
# Makefile for CDC Counter Display Project
#==============================================================================
# Provides convenient targets for building, simulating, and programming
#==============================================================================

.PHONY: help build sim program clean cleanall lint
.PHONY: build-demo sim-demo program-demo lint-demo create-demo cleanall-demo host-smoke host-watch-fail

# Default target
help:
	@echo "========================================================================"
	@echo "CDC Counter Display - Nexys A7 FPGA Project"
	@echo "========================================================================"
	@echo "Available targets:"
	@echo ""
	@echo "Phase 1 (button-only, original cdc_counter_display_top):"
	@echo "  make sim          - Run CocoTB simulation"
	@echo "  make build        - Build FPGA bitstream"
	@echo "  make program      - Program FPGA with bitstream"
	@echo "  make lint         - Verilator lint check"
	@echo "  make clean        - Clean simulation files"
	@echo "  make cleanall     - Clean all generated files"
	@echo ""
	@echo "Phase 2 (UART harness, cdc_demo_top — 4 counters, NO-CDC demo):"
	@echo "  make sim-demo         - CocoTB sim of the harness"
	@echo "  make build-demo       - Build phase-2 bitstream (~5-10 min)"
	@echo "  make program-demo     - Flash phase-2 bitstream"
	@echo "  make lint-demo        - Verilator lint of the harness RTL"
	@echo "  make create-demo      - Create Vivado project only (no build)"
	@echo "  make cleanall-demo    - Wipe phase-2 build artifacts"
	@echo "  make host-smoke       - python3 host/run_cdc_demo.py ... smoke"
	@echo "  make host-watch-fail  - python3 host/run_cdc_demo.py ... watch-fail"
	@echo ""
	@echo "Quick start (Phase 2):"
	@echo "  1. make sim-demo            # Verify the harness in simulation"
	@echo "  2. make build-demo          # Generate bitstream"
	@echo "  3. make program-demo        # Flash the board"
	@echo "  4. make host-watch-fail     # Run the 'watch CDC break' demo"
	@echo "========================================================================"

# Run CocoTB simulation
sim:
	@echo "Running CocoTB simulation..."
	cd sim && pytest test_cdc_counter_display.py -v -s
	@echo ""
	@echo "Simulation completed. Waveforms available in sim/sim_build/"

# Build FPGA bitstream
build:
	@echo "Building FPGA bitstream with Vivado..."
	@echo "This will take approximately 5-10 minutes..."
	vivado -mode batch -source tcl/build_all.tcl
	@echo ""
	@echo "Build completed!"
	@echo "Bitstream: cdc_counter_display.bit"
	@echo "Reports:   reports/"

# Program FPGA
program:
	@echo "Programming Nexys A7 FPGA..."
	@echo "Make sure your board is connected and powered on."
	vivado -mode batch -source tcl/program_fpga.tcl
	@echo ""
	@echo "Programming completed!"
	@echo "Try pressing the center button (BTNC) to increment the counter."

# Lint RTL with Verilator
lint:
	@echo "Running Verilator lint check..."
	verilator --lint-only -Wall \
		-I../../../rtl/common \
		rtl/cdc_counter_display_top.sv \
		../../../rtl/common/clock_divider.sv \
		../../../rtl/common/debounce.sv \
		../../../rtl/common/sync_pulse.sv \
		../../../rtl/common/hex_to_7seg.sv
	@echo "Lint check completed."

# Clean simulation files
clean:
	@echo "Cleaning simulation files..."
	rm -rf sim/sim_build
	rm -rf sim/__pycache__
	rm -f sim/*.vcd
	rm -f sim/results.xml
	@echo "Simulation files cleaned."

# Clean all generated files
cleanall: clean
	@echo "Cleaning all generated files..."
	rm -rf vivado_project
	rm -rf reports
	rm -f cdc_counter_display.bit
	rm -f .Xil
	rm -f vivado*.log
	rm -f vivado*.jou
	@echo "All generated files cleaned."

# Development shortcuts
.PHONY: test quick rebuild

# Quick test (alias for sim)
test: sim

# Quick rebuild (clean + build)
rebuild: cleanall build

# Create project only (no build)
create:
	@echo "Creating Vivado project..."
	vivado -mode batch -source tcl/create_project.tcl
	@echo ""
	@echo "Project created: vivado_project/cdc_counter_display.xpr"
	@echo "Open with: vivado vivado_project/cdc_counter_display.xpr"

#==============================================================================
# Phase 2 — UART harness build (cdc_demo_top)
#==============================================================================
REPO_ROOT := $(abspath ../../..)
PORT      ?= /dev/ttyUSB1

# CocoTB sim of the harness
sim-demo:
	@echo "Running CocoTB harness sim..."
	cd sim && pytest test_cdc_demo.py -v -s
	@echo "Done. Build dir: sim/sim_build_demo/"

# Verilator lint of just the harness RTL + counter domain + top
lint-demo:
	@echo "Running Verilator lint (phase 2)..."
	verilator --lint-only -Wno-fatal -Wno-WIDTH -Wno-UNUSEDSIGNAL -Wno-UNUSEDPARAM -Wno-DECLFILENAME \
		-I$(REPO_ROOT)/rtl/amba/includes \
		--top-module cdc_demo_top \
		$(REPO_ROOT)/rtl/common/clock_divider.sv \
		$(REPO_ROOT)/rtl/common/gray2bin.sv \
		$(REPO_ROOT)/rtl/common/bin2gray.sv \
		$(REPO_ROOT)/rtl/common/sync_pulse.sv \
		$(REPO_ROOT)/rtl/common/fifo_sync.sv \
		$(REPO_ROOT)/rtl/common/fifo_async.sv \
		$(REPO_ROOT)/rtl/common/fifo_control.sv \
		$(REPO_ROOT)/rtl/common/counter_bin.sv \
		$(REPO_ROOT)/rtl/common/counter_bin_load.sv \
		$(REPO_ROOT)/rtl/common/counter_bingray.sv \
		$(REPO_ROOT)/rtl/common/glitch_free_n_dff_arn.sv \
		$(REPO_ROOT)/rtl/amba/shared/cdc_open_loop.sv \
		$(REPO_ROOT)/rtl/amba/shared/cdc_2_phase_handshake.sv \
		$(REPO_ROOT)/rtl/amba/shared/cdc_4_phase_handshake.sv \
		$(REPO_ROOT)/rtl/amba/shared/cdc_synchronizer.sv \
		$(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv \
		$(REPO_ROOT)/rtl/amba/gaxi/gaxi_skid_buffer.sv \
		$(REPO_ROOT)/rtl/amba/axil4/axil4_master_rd.sv \
		$(REPO_ROOT)/rtl/amba/axil4/axil4_master_wr.sv \
		$(REPO_ROOT)/projects/components/converters/rtl/uart_to_axil4/uart_rx.sv \
		$(REPO_ROOT)/projects/components/converters/rtl/uart_to_axil4/uart_tx.sv \
		$(REPO_ROOT)/projects/components/converters/rtl/uart_to_axil4/uart_axil_bridge.sv \
		rtl/cdc_demo_harness.sv rtl/cdc_counter_domain.sv rtl/cdc_demo_top.sv

# Build phase-2 bitstream
build-demo:
	@echo "Building phase-2 bitstream (cdc_demo_top) — ~5-10 min..."
	vivado -mode batch -source tcl/build_demo.tcl
	@echo "Done. Bitstream: cdc_demo.bit"

# Program FPGA with phase-2 bitstream
program-demo:
	@echo "Programming Nexys A7 with cdc_demo.bit..."
	vivado -mode batch -source tcl/program_fpga_demo.tcl
	@echo "Done. Connect: python3 host/run_cdc_demo.py --port $(PORT) smoke"

# Create phase-2 project only
create-demo:
	@echo "Creating Vivado phase-2 project..."
	vivado -mode batch -source tcl/create_project_demo.tcl
	@echo "Project: vivado_project_demo/cdc_demo.xpr"

# Clean phase-2 artifacts
cleanall-demo:
	rm -rf vivado_project_demo reports_demo cdc_demo.bit
	rm -f vivado*.log vivado*.jou .Xil

# Host script convenience
host-smoke:
	python3 host/run_cdc_demo.py --port $(PORT) smoke

host-watch-fail:
	python3 host/run_cdc_demo.py --port $(PORT) watch-fail --counter 2
