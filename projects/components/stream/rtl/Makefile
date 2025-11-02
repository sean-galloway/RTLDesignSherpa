# ==============================================================================
# STREAM RTL - Lint & Synthesis Makefile
# ==============================================================================
#
# PREREQUISITES:
#   Must be run with sourced environment:
#     source $REPO_ROOT/env_python
#     cd $REPO_ROOT/projects/components/stream/rtl
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

# Master filelist for component-level linting
MASTER_FILELIST = filelists/stream_all.f

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
           -I$(REPO_ROOT)/rtl/amba/includes \
           -I./includes

# Tool options
VERILATOR = verilator
VERILATOR_FLAGS = --lint-only -Wall -Wno-TIMESCALEMOD $(INCLUDES)

VERIBLE = verible-verilog-lint
VERIBLE_FLAGS = --rules_config_search --rules=-parameter-name-style,-line-length

YOSYS = yosys
YOSYS_FLAGS = -p "read_verilog -sv"

# Default target
.DEFAULT_GOAL := help

# ==============================================================================
# Help Target
# ==============================================================================

.PHONY: help
help:
	@echo "================================================================================"
	@echo "STREAM RTL - Lint & Synthesis Makefile"
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
	@echo "Current REPO_ROOT: $(REPO_ROOT)"
	@echo "SystemVerilog files found: $(SV_COUNT)"
	@echo "================================================================================"

# ==============================================================================
# Verilator Targets
# ==============================================================================

.PHONY: verilator
verilator:
	@echo "================================================================================"
	@echo "Running Verilator Lint on STREAM RTL ($(SV_COUNT) files)"
	@echo "================================================================================"
	@mkdir -p $(VERILATOR_DIR)
	@echo "Linting using master filelist: $(MASTER_FILELIST)"
	@if $(VERILATOR) $(VERILATOR_FLAGS) -f $(MASTER_FILELIST) > $(VERILATOR_DIR)/stream_all.log 2>&1; then \
		echo "✓ STREAM RTL lint passed" | tee $(VERILATOR_DIR)/summary.txt; \
		echo "" >> $(VERILATOR_DIR)/summary.txt; \
		echo "Summary: 1 passed, 0 failed" >> $(VERILATOR_DIR)/summary.txt; \
	else \
		echo "✗ STREAM RTL lint failed" | tee $(VERILATOR_DIR)/summary.txt; \
		echo "" >> $(VERILATOR_DIR)/summary.txt; \
		echo "Summary: 0 passed, 1 failed" >> $(VERILATOR_DIR)/summary.txt; \
		echo ""; \
		echo "Error log:"; \
		cat $(VERILATOR_DIR)/stream_all.log; \
		exit 1; \
	fi
	@echo "✓ Verilator lint complete. Reports: $(VERILATOR_DIR)/"

# ==============================================================================
# Verible Targets
# ==============================================================================

.PHONY: verible
verible:
	@echo "================================================================================"
	@echo "Running Verible Lint on STREAM RTL ($(SV_COUNT) files)"
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
		echo "⚠ Verible not found. Skipping."; \
	fi

# ==============================================================================
# Yosys Targets
# ==============================================================================

.PHONY: yosys
yosys:
	@echo "================================================================================"
	@echo "Running Yosys Synthesis Check on STREAM RTL ($(SV_COUNT) files)"
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

# ==============================================================================
# Report Targets
# ==============================================================================

.PHONY: report
report:
	@echo "================================================================================"
	@echo "STREAM RTL Lint Summary Report"
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
	@echo "STREAM RTL Status"
	@echo "================================================================================"
	@echo "Location: $(REPO_ROOT)/projects/components/stream/rtl/"
	@echo ""
	@echo "SystemVerilog files: $(SV_COUNT)"
	@echo ""
	@echo "Modules:"
	@ls -1 *.sv 2>/dev/null | head -10
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

.PHONY: clean-all
clean-all:
	@echo "Cleaning all lint artifacts..."
	@rm -rf $(LINT_DIR)
	@echo "✓ All lint artifacts cleaned"

# ==============================================================================
# Quick Aliases
# ==============================================================================

.PHONY: lint
lint: lint-all

.PHONY: clean
clean: clean-all

# ==============================================================================
# End of Makefile
# ==============================================================================
