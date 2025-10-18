#==============================================================================
# Makefile for CDC Counter Display Project
#==============================================================================
# Provides convenient targets for building, simulating, and programming
#==============================================================================

.PHONY: help build sim program clean cleanall lint

# Default target
help:
	@echo "========================================================================"
	@echo "CDC Counter Display - Nexys A7 FPGA Project"
	@echo "========================================================================"
	@echo "Available targets:"
	@echo ""
	@echo "  make sim          - Run CocoTB simulation"
	@echo "  make build        - Build FPGA bitstream (Vivado)"
	@echo "  make program      - Program FPGA with bitstream"
	@echo "  make lint         - Run Verilator lint check"
	@echo "  make clean        - Clean simulation files"
	@echo "  make cleanall     - Clean all generated files"
	@echo "  make help         - Show this help message"
	@echo ""
	@echo "Quick start:"
	@echo "  1. make sim       # Verify design in simulation"
	@echo "  2. make build     # Generate bitstream (~5-10 min)"
	@echo "  3. make program   # Program your Nexys A7 board"
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
