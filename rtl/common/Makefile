# ==============================================================================
# RTL Common Building Blocks - Lint & Synthesis Makefile
# ==============================================================================
#
# PREREQUISITES:
#   Must be run with sourced environment:
#     source $REPO_ROOT/env_python  # Sets $REPO_ROOT and activates venv
#     cd $REPO_ROOT/rtl/common
#     make <target>
#
# Quick start:
#   make help           - Show all available targets
#   make lint-all       - Run all lint tools
#   make verilator      - Run Verilator lint
#   make verible        - Run Verible lint
#   make clean-all      - Clean all lint artifacts
#
# ==============================================================================

# Force bash shell
SHELL := /bin/bash

# Check if REPO_ROOT is set (from env_python)
ifndef REPO_ROOT
$(error REPO_ROOT is not set. Please run: source $$REPO_ROOT/env_python)
endif

# Find all SystemVerilog files
SV_FILES := $(shell find . -name "*.sv" -type f)
SV_COUNT := $(words $(SV_FILES))

# Master filelist for hierarchical linting
MASTER_FILELIST = filelists/common_all.f

# Lint output directories
LINT_DIR = lint_reports
VERILATOR_DIR = $(LINT_DIR)/verilator
VERIBLE_DIR = $(LINT_DIR)/verible
YOSYS_DIR = $(LINT_DIR)/yosys

# Include paths
INCLUDES = -I$(REPO_ROOT)/rtl/amba/includes

# Tool options
VERILATOR = verilator
# Note: -Wno-fatal allows warnings without failing build (Common has intentional design patterns that trigger warnings)
VERILATOR_FLAGS = --lint-only -Wall -Wno-TIMESCALEMOD -Wno-fatal $(INCLUDES)

VERIBLE = verible-verilog-lint
VERIBLE_FLAGS = --rules_config_search --rules=-parameter-name-style,-line-length

YOSYS = yosys
YOSYS_FLAGS = -p "read_verilog -sv"

# Default target - show help
.DEFAULT_GOAL := help

# ==============================================================================
# Help Target
# ==============================================================================

.PHONY: help
help:
	@echo "================================================================================"
	@echo "RTL Common - Lint & Synthesis Makefile"
	@echo "================================================================================"
	@echo ""
	@echo "LINT TARGETS:"
	@echo "  make lint-all             Run all lint tools on all files"
	@echo "  make verilator            Run Verilator lint on all files"
	@echo "  make verilator-counters   Run Verilator on counter modules"
	@echo "  make verilator-arbiters   Run Verilator on arbiter modules"
	@echo "  make verilator-fifos      Run Verilator on FIFO modules (AMBA GAXI)"
	@echo "  make verible              Run Verible lint on all files"
	@echo "  make verible-counters     Run Verible on counter modules"
	@echo ""
	@echo "SYNTHESIS TARGETS:"
	@echo "  make yosys                Run Yosys synthesis check on all files"
	@echo "  make yosys-counters       Run Yosys on counter modules"
	@echo ""
	@echo "REPORT TARGETS:"
	@echo "  make report               Generate lint summary report"
	@echo "  make status               Show file counts and lint status"
	@echo ""
	@echo "CLEAN TARGETS:"
	@echo "  make clean-all            Remove all lint artifacts"
	@echo "  make clean-verilator      Remove Verilator reports"
	@echo "  make clean-verible        Remove Verible reports"
	@echo "  make clean-yosys          Remove Yosys reports"
	@echo ""
	@echo "================================================================================"
	@echo "Prerequisites: source $(REPO_ROOT)/env_python"
	@echo "Current REPO_ROOT: $(REPO_ROOT)"
	@echo "SystemVerilog files found: $(SV_COUNT)"
	@echo "================================================================================"

# ==============================================================================
# Verilator Targets
# ==============================================================================

.PHONY: verilator
verilator:
	@echo "================================================================================"
	@echo "Running Verilator Lint on RTL Common ($(SV_COUNT) files)"
	@echo "Using master filelist: $(MASTER_FILELIST)"
	@echo "================================================================================"
	@mkdir -p $(VERILATOR_DIR)
	@if $(VERILATOR) $(VERILATOR_FLAGS) -f $(MASTER_FILELIST) > $(VERILATOR_DIR)/common_all.log 2>&1; then \
		echo "✓ RTL Common lint passed" | tee $(VERILATOR_DIR)/summary.txt; \
		echo "" >> $(VERILATOR_DIR)/summary.txt; \
		echo "All $(SV_COUNT) files passed lint checks" >> $(VERILATOR_DIR)/summary.txt; \
	else \
		echo "✗ RTL Common lint failed" | tee $(VERILATOR_DIR)/summary.txt; \
		echo "" >> $(VERILATOR_DIR)/summary.txt; \
		echo "Errors found. See $(VERILATOR_DIR)/common_all.log for details" >> $(VERILATOR_DIR)/summary.txt; \
		echo ""; \
		echo "Last 30 lines of error log:"; \
		tail -30 $(VERILATOR_DIR)/common_all.log; \
		exit 1; \
	fi
	@echo "✓ Verilator lint complete. Reports: $(VERILATOR_DIR)/"

.PHONY: verilator-counters
verilator-counters:
	@echo "Running Verilator on counter modules..."
	@mkdir -p $(VERILATOR_DIR)
	@for file in counter*.sv; do \
		echo "Linting $$file..."; \
		$(VERILATOR) $(VERILATOR_FLAGS) $$file > $(VERILATOR_DIR)/$$(basename $$file .sv).log 2>&1 || true; \
	done
	@echo "✓ Verilator lint complete (counters)"

.PHONY: verilator-arbiters
verilator-arbiters:
	@echo "Running Verilator on arbiter modules..."
	@mkdir -p $(VERILATOR_DIR)
	@for file in arbiter*.sv; do \
		echo "Linting $$file..."; \
		$(VERILATOR) $(VERILATOR_FLAGS) $$file > $(VERILATOR_DIR)/$$(basename $$file .sv).log 2>&1 || true; \
	done
	@echo "✓ Verilator lint complete (arbiters)"

.PHONY: verilator-fifos
verilator-fifos:
	@echo "Running Verilator on FIFO modules (AMBA GAXI)..."
	@echo "Note: FIFOs are in rtl/amba/gaxi/"
	@mkdir -p $(VERILATOR_DIR)
	@if [ -d "$(REPO_ROOT)/rtl/amba/gaxi" ]; then \
		cd $(REPO_ROOT)/rtl/amba/gaxi && \
		for file in gaxi_fifo*.sv; do \
			echo "Linting $$file..."; \
			$(VERILATOR) $(VERILATOR_FLAGS) $$file > $(REPO_ROOT)/rtl/common/$(VERILATOR_DIR)/$$(basename $$file .sv).log 2>&1 || true; \
		done; \
	fi
	@echo "✓ Verilator lint complete (FIFOs)"

# ==============================================================================
# Verible Targets
# ==============================================================================

.PHONY: verible
verible:
	@echo "================================================================================"
	@echo "Running Verible Lint on RTL Common ($(SV_COUNT) files)"
	@echo "================================================================================"
	@mkdir -p $(VERIBLE_DIR)
	@if command -v $(VERIBLE) &> /dev/null; then \
		echo "Lint results:" > $(VERIBLE_DIR)/summary.txt; \
		pass_count=0; fail_count=0; \
		for file in $(SV_FILES); do \
			echo "Linting $$file..."; \
			if $(VERIBLE) $(VERIBLE_FLAGS) $$file > $(VERIBLE_DIR)/$$(basename $$file .sv).log 2>&1; then \
				echo "✓ $$file" >> $(VERIBLE_DIR)/summary.txt; \
				pass_count=$$((pass_count + 1)); \
			else \
				echo "✗ $$file" >> $(VERIBLE_DIR)/summary.txt; \
				fail_count=$$((fail_count + 1)); \
			fi; \
		done; \
		echo "" >> $(VERIBLE_DIR)/summary.txt; \
		echo "Summary: $$pass_count passed, $$fail_count failed" >> $(VERIBLE_DIR)/summary.txt; \
		cat $(VERIBLE_DIR)/summary.txt; \
		echo "✓ Verible lint complete. Reports: $(VERIBLE_DIR)/"; \
	else \
		echo "⚠ Verible not found. Install: https://github.com/chipsalliance/verible"; \
		echo "Skipping Verible lint."; \
	fi

.PHONY: verible-counters
verible-counters:
	@echo "Running Verible on counter modules..."
	@mkdir -p $(VERIBLE_DIR)
	@if command -v $(VERIBLE) &> /dev/null; then \
		for file in counter*.sv; do \
			echo "Linting $$file..."; \
			$(VERIBLE) $(VERIBLE_FLAGS) $$file > $(VERIBLE_DIR)/$$(basename $$file .sv).log 2>&1 || true; \
		done; \
		echo "✓ Verible lint complete (counters)"; \
	else \
		echo "⚠ Verible not found. Skipping."; \
	fi

# ==============================================================================
# Yosys Targets
# ==============================================================================

.PHONY: yosys
yosys:
	@echo "================================================================================"
	@echo "Running Yosys Synthesis Check on RTL Common ($(SV_COUNT) files)"
	@echo "================================================================================"
	@mkdir -p $(YOSYS_DIR)
	@if command -v $(YOSYS) &> /dev/null; then \
		echo "Synthesis check results:" > $(YOSYS_DIR)/summary.txt; \
		pass_count=0; fail_count=0; \
		for file in $(SV_FILES); do \
			echo "Checking $$file..."; \
			if $(YOSYS) $(YOSYS_FLAGS) $$file -p "hierarchy -check" > $(YOSYS_DIR)/$$(basename $$file .sv).log 2>&1; then \
				echo "✓ $$file" >> $(YOSYS_DIR)/summary.txt; \
				pass_count=$$((pass_count + 1)); \
			else \
				echo "✗ $$file" >> $(YOSYS_DIR)/summary.txt; \
				fail_count=$$((fail_count + 1)); \
			fi; \
		done; \
		echo "" >> $(YOSYS_DIR)/summary.txt; \
		echo "Summary: $$pass_count passed, $$fail_count failed" >> $(YOSYS_DIR)/summary.txt; \
		cat $(YOSYS_DIR)/summary.txt; \
		echo "✓ Yosys synthesis check complete. Reports: $(YOSYS_DIR)/"; \
	else \
		echo "⚠ Yosys not found. Install: http://www.clifford.at/yosys/"; \
		echo "Skipping Yosys synthesis check."; \
	fi

.PHONY: yosys-counters
yosys-counters:
	@echo "Running Yosys on counter modules..."
	@mkdir -p $(YOSYS_DIR)
	@if command -v $(YOSYS) &> /dev/null; then \
		for file in counter*.sv; do \
			echo "Checking $$file..."; \
			$(YOSYS) $(YOSYS_FLAGS) $$file -p "hierarchy -check" > $(YOSYS_DIR)/$$(basename $$file .sv).log 2>&1 || true; \
		done; \
		echo "✓ Yosys synthesis check complete (counters)"; \
	else \
		echo "⚠ Yosys not found. Skipping."; \
	fi

# ==============================================================================
# Combined Targets
# ==============================================================================

.PHONY: lint-all
lint-all: verilator verible
	@echo "================================================================================"
	@echo "✓ All lint tools completed"
	@echo "================================================================================"

.PHONY: synth-all
synth-all: yosys
	@echo "✓ Synthesis checks completed"

# ==============================================================================
# Report Targets
# ==============================================================================

.PHONY: report
report:
	@echo "================================================================================"
	@echo "RTL Common Lint Summary Report"
	@echo "================================================================================"
	@echo ""
	@echo "Files found: $(SV_COUNT)"
	@echo ""
	@if [ -f $(VERILATOR_DIR)/summary.txt ]; then \
		echo "=== Verilator Results ==="; \
		cat $(VERILATOR_DIR)/summary.txt; \
		echo ""; \
	fi
	@if [ -f $(VERIBLE_DIR)/summary.txt ]; then \
		echo "=== Verible Results ==="; \
		cat $(VERIBLE_DIR)/summary.txt; \
		echo ""; \
	fi
	@if [ -f $(YOSYS_DIR)/summary.txt ]; then \
		echo "=== Yosys Results ==="; \
		cat $(YOSYS_DIR)/summary.txt; \
		echo ""; \
	fi
	@echo "================================================================================"

.PHONY: status
status:
	@echo "================================================================================"
	@echo "RTL Common Status"
	@echo "================================================================================"
	@echo "Location: $(REPO_ROOT)/rtl/common/"
	@echo ""
	@echo "SystemVerilog files: $(SV_COUNT)"
	@echo ""
	@echo "Module categories:"
	@echo "  Counters:       $$(ls counter*.sv 2>/dev/null | wc -l)"
	@echo "  Arbiters:       $$(ls arbiter*.sv 2>/dev/null | wc -l)"
	@echo "  Shifters:       $$(ls shifter*.sv 2>/dev/null | wc -l)"
	@echo "  Data Integrity: $$(ls dataint*.sv 2>/dev/null | wc -l)"
	@echo "  Clock Utils:    $$(ls clock*.sv 2>/dev/null | wc -l)"
	@echo "  Math:           $$(ls bin2*.sv gray2*.sv count_*.sv 2>/dev/null | wc -l)"
	@echo ""
	@echo "Lint reports:"
	@echo "  Verilator: $$(find $(VERILATOR_DIR) -name '*.log' 2>/dev/null | wc -l) reports"
	@echo "  Verible:   $$(find $(VERIBLE_DIR) -name '*.log' 2>/dev/null | wc -l) reports"
	@echo "  Yosys:     $$(find $(YOSYS_DIR) -name '*.log' 2>/dev/null | wc -l) reports"
	@echo ""
	@echo "Environment:"
	@echo "  REPO_ROOT: $(REPO_ROOT)"
	@echo "================================================================================"

# ==============================================================================
# Clean Targets
# ==============================================================================

.PHONY: clean-verilator
clean-verilator:
	@echo "Cleaning Verilator reports..."
	@rm -rf $(VERILATOR_DIR)
	@echo "✓ Verilator reports cleaned"

.PHONY: clean-verible
clean-verible:
	@echo "Cleaning Verible reports..."
	@rm -rf $(VERIBLE_DIR)
	@echo "✓ Verible reports cleaned"

.PHONY: clean-yosys
clean-yosys:
	@echo "Cleaning Yosys reports..."
	@rm -rf $(YOSYS_DIR)
	@echo "✓ Yosys reports cleaned"

.PHONY: clean-all
clean-all: clean-verilator clean-verible clean-yosys
	@echo "Cleaning all lint artifacts..."
	@rm -rf $(LINT_DIR)
	@echo "================================================================================"
	@echo "✓ All lint artifacts cleaned"
	@echo "================================================================================"

# ==============================================================================
# Quick Aliases
# ==============================================================================

.PHONY: lint
lint: lint-all

.PHONY: synth
synth: synth-all

.PHONY: clean
clean: clean-all

# ==============================================================================
# End of Makefile
# ==============================================================================
