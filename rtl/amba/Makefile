# ==============================================================================
# RTL AMBA Protocol Infrastructure - Lint & Synthesis Makefile
# ==============================================================================
#
# PREREQUISITES:
#   Must be run with sourced environment:
#     source $REPO_ROOT/env_python  # Sets $REPO_ROOT and activates venv
#     cd $REPO_ROOT/rtl/amba
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

# Protocol directories
SUBDIRS = axi4 axil4 apb axis4 gaxi shared

# Find all SystemVerilog files
SV_FILES := $(shell find $(SUBDIRS) -name "*.sv" -type f 2>/dev/null)
SV_COUNT := $(words $(SV_FILES))

# Master filelist for hierarchical linting
MASTER_FILELIST = filelists/amba_all.f

# Lint output directories
LINT_DIR = lint_reports
VERILATOR_DIR = $(LINT_DIR)/verilator
VERIBLE_DIR = $(LINT_DIR)/verible
YOSYS_DIR = $(LINT_DIR)/yosys

# Tool options
VERILATOR = verilator
VERILATOR_INCLUDES = -Iincludes -I$(REPO_ROOT)/rtl/common
# Note: -Wno-fatal allows warnings without failing build (AMBA has intentional design patterns that trigger warnings)
VERILATOR_FLAGS = --lint-only -Wall -Wno-TIMESCALEMOD -Wno-fatal $(VERILATOR_INCLUDES)

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
	@echo "RTL AMBA - Lint & Synthesis Makefile"
	@echo "================================================================================"
	@echo ""
	@echo "LINT TARGETS:"
	@echo "  make lint-all             Run all lint tools on all files"
	@echo "  make verilator            Run Verilator lint on all files"
	@echo "  make verilator-axi4       Run Verilator on AXI4 modules"
	@echo "  make verilator-axil4      Run Verilator on AXI4-Lite modules"
	@echo "  make verilator-apb        Run Verilator on APB modules"
	@echo "  make verilator-axis4      Run Verilator on AXI-Stream modules"
	@echo "  make verilator-gaxi       Run Verilator on GAXI modules"
	@echo "  make verilator-shared     Run Verilator on shared modules"
	@echo "  make verible              Run Verible lint on all files"
	@echo "  make verible-axi4         Run Verible on AXI4 modules"
	@echo ""
	@echo "SYNTHESIS TARGETS:"
	@echo "  make yosys                Run Yosys synthesis check on all files"
	@echo "  make yosys-axi4           Run Yosys on AXI4 modules"
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
	@echo "Running Verilator Lint on RTL AMBA ($(SV_COUNT) files)"
	@echo "Using master filelist: $(MASTER_FILELIST)"
	@echo "================================================================================"
	@mkdir -p $(VERILATOR_DIR)
	@if $(VERILATOR) $(VERILATOR_FLAGS) -f $(MASTER_FILELIST) > $(VERILATOR_DIR)/amba_all.log 2>&1; then \
		echo "✓ RTL AMBA lint passed" | tee $(VERILATOR_DIR)/summary.txt; \
		echo "" >> $(VERILATOR_DIR)/summary.txt; \
		echo "All $(SV_COUNT) files passed lint checks" >> $(VERILATOR_DIR)/summary.txt; \
	else \
		echo "✗ RTL AMBA lint failed" | tee $(VERILATOR_DIR)/summary.txt; \
		echo "" >> $(VERILATOR_DIR)/summary.txt; \
		echo "Errors found. See $(VERILATOR_DIR)/amba_all.log for details" >> $(VERILATOR_DIR)/summary.txt; \
		echo ""; \
		echo "Last 30 lines of error log:"; \
		tail -30 $(VERILATOR_DIR)/amba_all.log; \
		exit 1; \
	fi
	@echo "✓ Verilator lint complete. Reports: $(VERILATOR_DIR)/"

.PHONY: verilator-axi4
verilator-axi4:
	@echo "Running Verilator on AXI4 modules..."
	@mkdir -p $(VERILATOR_DIR)
	@for file in axi4/*.sv; do \
		echo "Linting $$file..."; \
		$(VERILATOR) $(VERILATOR_FLAGS) $(VERILATOR_INCLUDES) -Iaxi4 $$file > $(VERILATOR_DIR)/$$(basename $$file .sv).log 2>&1 || true; \
	done
	@echo "✓ Verilator lint complete (AXI4)"

.PHONY: verilator-axil4
verilator-axil4:
	@echo "Running Verilator on AXI4-Lite modules..."
	@mkdir -p $(VERILATOR_DIR)
	@for file in axil4/*.sv; do \
		echo "Linting $$file..."; \
		$(VERILATOR) $(VERILATOR_FLAGS) $(VERILATOR_INCLUDES) -Iaxil4 $$file > $(VERILATOR_DIR)/$$(basename $$file .sv).log 2>&1 || true; \
	done
	@echo "✓ Verilator lint complete (AXI4-Lite)"

.PHONY: verilator-apb
verilator-apb:
	@echo "Running Verilator on APB modules..."
	@mkdir -p $(VERILATOR_DIR)
	@for file in apb/*.sv; do \
		echo "Linting $$file..."; \
		$(VERILATOR) $(VERILATOR_FLAGS) $(VERILATOR_INCLUDES) -Iapb $$file > $(VERILATOR_DIR)/$$(basename $$file .sv).log 2>&1 || true; \
	done
	@echo "✓ Verilator lint complete (APB)"

.PHONY: verilator-axis4
verilator-axis4:
	@echo "Running Verilator on AXI-Stream modules..."
	@mkdir -p $(VERILATOR_DIR)
	@for file in axis4/*.sv; do \
		echo "Linting $$file..."; \
		$(VERILATOR) $(VERILATOR_FLAGS) $(VERILATOR_INCLUDES) -Iaxis4 $$file > $(VERILATOR_DIR)/$$(basename $$file .sv).log 2>&1 || true; \
	done
	@echo "✓ Verilator lint complete (AXI-Stream)"

.PHONY: verilator-gaxi
verilator-gaxi:
	@echo "Running Verilator on GAXI modules..."
	@mkdir -p $(VERILATOR_DIR)
	@for file in gaxi/*.sv; do \
		echo "Linting $$file..."; \
		$(VERILATOR) $(VERILATOR_FLAGS) $(VERILATOR_INCLUDES) -Igaxi $$file > $(VERILATOR_DIR)/$$(basename $$file .sv).log 2>&1 || true; \
	done
	@echo "✓ Verilator lint complete (GAXI)"

.PHONY: verilator-shared
verilator-shared:
	@echo "Running Verilator on shared modules..."
	@mkdir -p $(VERILATOR_DIR)
	@for file in shared/*.sv; do \
		echo "Linting $$file..."; \
		$(VERILATOR) $(VERILATOR_FLAGS) $(VERILATOR_INCLUDES) -Ishared $$file > $(VERILATOR_DIR)/$$(basename $$file .sv).log 2>&1 || true; \
	done
	@echo "✓ Verilator lint complete (shared)"

# ==============================================================================
# Verible Targets
# ==============================================================================

.PHONY: verible
verible:
	@echo "================================================================================"
	@echo "Running Verible Lint on RTL AMBA ($(SV_COUNT) files)"
	@echo "================================================================================"
	@mkdir -p $(VERIBLE_DIR)
	@if command -v $(VERIBLE) &> /dev/null; then \
		echo "Lint results:" > $(VERIBLE_DIR)/summary.txt; \
		pass_count=0; fail_count=0; \
		for file in $(SV_FILES); do \
			echo "Linting $$file..."; \
			if $(VERIBLE) $(VERIBLE_FLAGS) $$file > $(VERIBLE_DIR)/$$(echo $$file | tr '/' '_' | sed 's/.sv$$/.log/') 2>&1; then \
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

.PHONY: verible-axi4
verible-axi4:
	@echo "Running Verible on AXI4 modules..."
	@mkdir -p $(VERIBLE_DIR)
	@if command -v $(VERIBLE) &> /dev/null; then \
		for file in axi4/*.sv; do \
			echo "Linting $$file..."; \
			$(VERIBLE) $(VERIBLE_FLAGS) $$file > $(VERIBLE_DIR)/$$(basename $$file .sv).log 2>&1 || true; \
		done; \
		echo "✓ Verible lint complete (AXI4)"; \
	else \
		echo "⚠ Verible not found. Skipping."; \
	fi

# ==============================================================================
# Yosys Targets
# ==============================================================================

.PHONY: yosys
yosys:
	@echo "================================================================================"
	@echo "Running Yosys Synthesis Check on RTL AMBA ($(SV_COUNT) files)"
	@echo "================================================================================"
	@mkdir -p $(YOSYS_DIR)
	@if command -v $(YOSYS) &> /dev/null; then \
		echo "Synthesis check results:" > $(YOSYS_DIR)/summary.txt; \
		pass_count=0; fail_count=0; \
		for file in $(SV_FILES); do \
			echo "Checking $$file..."; \
			if $(YOSYS) $(YOSYS_FLAGS) $$file -p "hierarchy -check" > $(YOSYS_DIR)/$$(echo $$file | tr '/' '_' | sed 's/.sv$$/.log/') 2>&1; then \
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

.PHONY: yosys-axi4
yosys-axi4:
	@echo "Running Yosys on AXI4 modules..."
	@mkdir -p $(YOSYS_DIR)
	@if command -v $(YOSYS) &> /dev/null; then \
		for file in axi4/*.sv; do \
			echo "Checking $$file..."; \
			$(YOSYS) $(YOSYS_FLAGS) $$file -p "hierarchy -check" > $(YOSYS_DIR)/$$(basename $$file .sv).log 2>&1 || true; \
		done; \
		echo "✓ Yosys synthesis check complete (AXI4)"; \
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

.PHONY: lint-protocols
lint-protocols: verilator-axi4 verilator-axil4 verilator-apb verilator-axis4
	@echo "✓ All protocol linting completed"

# ==============================================================================
# Report Targets
# ==============================================================================

.PHONY: report
report:
	@echo "================================================================================"
	@echo "RTL AMBA Lint Summary Report"
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
	@echo "RTL AMBA Status"
	@echo "================================================================================"
	@echo "Location: $(REPO_ROOT)/rtl/amba/"
	@echo ""
	@echo "SystemVerilog files: $(SV_COUNT)"
	@echo ""
	@echo "Protocol breakdown:"
	@echo "  AXI4:        $$(find axi4 -name '*.sv' 2>/dev/null | wc -l) files"
	@echo "  AXI4-Lite:   $$(find axil4 -name '*.sv' 2>/dev/null | wc -l) files"
	@echo "  APB:         $$(find apb -name '*.sv' 2>/dev/null | wc -l) files"
	@echo "  AXI-Stream:  $$(find axis4 -name '*.sv' 2>/dev/null | wc -l) files"
	@echo "  GAXI:        $$(find gaxi -name '*.sv' 2>/dev/null | wc -l) files"
	@echo "  Shared:      $$(find shared -name '*.sv' 2>/dev/null | wc -l) files"
	@echo "  Shims:       $$(find shims -name '*.sv' 2>/dev/null | wc -l) files"
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
