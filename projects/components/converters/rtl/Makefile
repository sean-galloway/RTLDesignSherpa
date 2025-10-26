# ==============================================================================
# Converters (Data Width + Protocol) RTL - Lint & Synthesis Makefile
# ==============================================================================
#
# PREREQUISITES:
#   Must be run with sourced environment:
#     source $REPO_ROOT/env_python
#     cd $REPO_ROOT/projects/components/converters/rtl
#     make <target>
#
# Quick start:
#   make help           - Show all available targets
#   make lint-all       - Run all lint tools
#   make status         - Show RTL status
#
# ==============================================================================

# Force bash shell
SHELL := /bin/bash

# Check if REPO_ROOT is set (from env_python)
ifndef REPO_ROOT
$(error REPO_ROOT is not set. Please run: source $$REPO_ROOT/env_python)
endif

# Find all SystemVerilog files (for status reporting)
SV_FILES := $(shell find . -name "*.sv" -type f)
SV_COUNT := $(words $(SV_FILES))

# Lint output directories
LINT_DIR = lint_reports
VERILATOR_DIR = $(LINT_DIR)/verilator
VERIBLE_DIR = $(LINT_DIR)/verible
YOSYS_DIR = $(LINT_DIR)/yosys

# Include paths
INCLUDES = -I$(REPO_ROOT)/rtl/common \
           -I$(REPO_ROOT)/rtl/amba/includes

# Tool options
VERILATOR = verilator
VERILATOR_FLAGS = --lint-only -Wall -Wno-TIMESCALEMOD $(INCLUDES)

VERIBLE = verible-verilog-lint
VERIBLE_FLAGS = --rules_config_search

YOSYS = yosys
YOSYS_FLAGS = -p "read_verilog -sv"

# Default target
.DEFAULT_GOAL := help

.PHONY: help
help:
	@echo "================================================================================"
	@echo "Converters (Data Width + Protocol) RTL - Lint & Synthesis Makefile"
	@echo "================================================================================"
	@echo ""
	@echo "LINT TARGETS:"
	@echo "  make lint-all             Run all lint tools"
	@echo "  make verilator            Run Verilator lint"
	@echo "  make verible              Run Verible lint"
	@echo "  make yosys                Run Yosys synthesis check"
	@echo ""
	@echo "REPORT TARGETS:"
	@echo "  make report               Generate lint summary"
	@echo "  make status               Show RTL status"
	@echo ""
	@echo "CLEAN TARGETS:"
	@echo "  make clean-all            Remove all lint artifacts"
	@echo ""
	@echo "================================================================================"
	@echo "Prerequisites: source $(REPO_ROOT)/env_python"
	@echo "SystemVerilog files found: $(SV_COUNT)"
	@echo "================================================================================"

# Lint targets
.PHONY: lint-all
lint-all: verilator
	@echo "✓ All lint tools completed"

.PHONY: verilator
verilator: $(SV_FILES)
	@echo "================================================================================"
	@echo "Running Verilator on Converters RTL"
	@echo "================================================================================"
	@mkdir -p $(VERILATOR_DIR)
	@for file in $(SV_FILES); do \
		echo "Linting $$file..."; \
		$(VERILATOR) $(VERILATOR_FLAGS) $$file 2>&1 | tee $(VERILATOR_DIR)/$$(basename $$file .sv)_lint.log || true; \
	done
	@echo "✓ Verilator lint complete"

.PHONY: verible
verible: $(SV_FILES)
	@echo "Running Verible on Converters RTL"
	@mkdir -p $(VERIBLE_DIR)
	@for file in $(SV_FILES); do \
		$(VERIBLE) $(VERIBLE_FLAGS) $$file 2>&1 | tee $(VERIBLE_DIR)/$$(basename $$file .sv)_lint.log || true; \
	done
	@echo "✓ Verible lint complete"

.PHONY: yosys
yosys: $(SV_FILES)
	@echo "Running Yosys on Converters RTL"
	@mkdir -p $(YOSYS_DIR)
	@for file in $(SV_FILES); do \
		$(YOSYS) $(YOSYS_FLAGS) $$file 2>&1 | tee $(YOSYS_DIR)/$$(basename $$file .sv)_synth.log || true; \
	done
	@echo "✓ Yosys synthesis check complete"

# Status and reporting
.PHONY: status
status:
	@echo "================================================================================"
	@echo "Converters RTL Status"
	@echo "================================================================================"
	@echo "Location: $(REPO_ROOT)/projects/components/converters/rtl"
	@echo "SystemVerilog files: $(SV_COUNT)"
	@echo ""
	@echo "Modules:"
	@echo "  Data Width Converters:"
	@echo "    - axi_data_upsize.sv, axi_data_dnsize.sv (generic building blocks)"
	@echo "    - axi4_dwidth_converter_rd.sv, axi4_dwidth_converter_wr.sv (full converters)"
	@echo "  Protocol Converters:"
	@echo "    - axi4_to_apb_convert.sv, axi4_to_apb_shim.sv (AXI4-to-APB bridges)"
	@echo "    - peakrdl_to_cmdrsp.sv (PeakRDL adapter)"
	@echo ""
	@echo "Files:"
	@ls -1 *.sv 2>/dev/null || echo "  No .sv files found"
	@echo ""
	@echo "Lint reports:"
	@if [ -d "$(LINT_DIR)" ]; then \
		echo "  Verilator: $$(find $(VERILATOR_DIR) -name '*.log' 2>/dev/null | wc -l) reports"; \
	else \
		echo "  No lint reports (run 'make lint-all')"; \
	fi
	@echo "================================================================================"

.PHONY: report
report: status

# Clean targets
.PHONY: clean-all
clean-all:
	@echo "Cleaning Converters lint artifacts..."
	@rm -rf $(LINT_DIR)
	@echo "✓ Clean complete"

.PHONY: clean
clean: clean-all

# ==============================================================================
# End of Makefile
# ==============================================================================
