# ==============================================================================
# RAPIDS RTL - Lint & Synthesis Makefile
# ==============================================================================
#
# PREREQUISITES:
#   Must be run with sourced environment:
#     source $REPO_ROOT/env_python
#     cd $REPO_ROOT/projects/components/rapids/rtl
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
MASTER_FILELIST = filelists/rapids_all.f

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
VERIBLE_FLAGS = --rules_config_search

YOSYS = yosys
YOSYS_FLAGS = -p "read_verilog -sv"

# Default target
.DEFAULT_GOAL := help

.PHONY: help
help:
	@echo "================================================================================"
	@echo "RAPIDS RTL - Lint & Synthesis Makefile"
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

.PHONY: verilator
verilator:
	@echo "================================================================================"
	@echo "Running Verilator Lint on RAPIDS RTL ($(SV_COUNT) files)"
	@echo "================================================================================"
	@mkdir -p $(VERILATOR_DIR)
	@echo "Linting using master filelist: $(MASTER_FILELIST)"
	@if $(VERILATOR) $(VERILATOR_FLAGS) -f $(MASTER_FILELIST) > $(VERILATOR_DIR)/rapids_all.log 2>&1; then \
		echo "✓ RAPIDS RTL lint passed" | tee $(VERILATOR_DIR)/summary.txt; \
		echo "" >> $(VERILATOR_DIR)/summary.txt; \
		echo "Summary: 1 passed, 0 failed" >> $(VERILATOR_DIR)/summary.txt; \
	else \
		echo "✗ RAPIDS RTL lint failed" | tee $(VERILATOR_DIR)/summary.txt; \
		echo "" >> $(VERILATOR_DIR)/summary.txt; \
		echo "Summary: 0 passed, 1 failed" >> $(VERILATOR_DIR)/summary.txt; \
		echo ""; \
		echo "Error log:"; \
		cat $(VERILATOR_DIR)/rapids_all.log; \
		exit 1; \
	fi
	@echo "✓ Verilator lint complete. Reports: $(VERILATOR_DIR)/"

.PHONY: verible
verible:
	@echo "Running Verible Lint on RAPIDS RTL"
	@mkdir -p $(VERIBLE_DIR)
	@if command -v $(VERIBLE) &> /dev/null; then \
		for file in $(SV_FILES); do \
			$(VERIBLE) $(VERIBLE_FLAGS) $$file > $(VERIBLE_DIR)/$$(basename $$file .sv).log 2>&1 || true; \
		done; \
		echo "✓ Verible lint complete"; \
	else \
		echo "⚠ Verible not found. Skipping."; \
	fi

.PHONY: yosys
yosys:
	@echo "Running Yosys Synthesis Check on RAPIDS RTL"
	@mkdir -p $(YOSYS_DIR)
	@if command -v $(YOSYS) &> /dev/null; then \
		for file in $(SV_FILES); do \
			$(YOSYS) $(YOSYS_FLAGS) $$file -p "hierarchy -check" > $(YOSYS_DIR)/$$(basename $$file .sv).log 2>&1 || true; \
		done; \
		echo "✓ Yosys synthesis check complete"; \
	else \
		echo "⚠ Yosys not found. Skipping."; \
	fi

.PHONY: lint-all
lint-all: verilator verible
	@echo "✓ All lint tools completed"

.PHONY: status
status:
	@echo "================================================================================"
	@echo "RAPIDS RTL Status"
	@echo "================================================================================"
	@echo "Location: $(REPO_ROOT)/projects/components/rapids/rtl/"
	@echo "SystemVerilog files: $(SV_COUNT)"
	@echo "================================================================================"

.PHONY: clean-all
clean-all:
	@rm -rf $(LINT_DIR)
	@echo "✓ All lint artifacts cleaned"

.PHONY: lint
lint: lint-all

.PHONY: clean
clean: clean-all
