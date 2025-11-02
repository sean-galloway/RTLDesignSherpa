# ==============================================================================
# RTL Master Makefile - Lint & Synthesis for All RTL
# ==============================================================================
#
# PREREQUISITES:
#   Must be run with sourced environment:
#     source $REPO_ROOT/env_python  # Sets $REPO_ROOT and activates venv
#     cd $REPO_ROOT/rtl
#     make <target>
#
# Quick start:
#   make help           - Show all available targets
#   make lint-all       - Run lint tools on all RTL areas
#   make verilator-all  - Run Verilator on all areas
#   make status         - Show RTL status summary
#   make clean-all      - Clean all lint artifacts
#
# ==============================================================================

# Force bash shell
SHELL := /bin/bash

# Check if REPO_ROOT is set (from env_python)
ifndef REPO_ROOT
$(error REPO_ROOT is not set. Please run: source $$REPO_ROOT/env_python)
endif

# RTL area directories
COMMON_DIR = common
AMBA_DIR = amba

# Default target - show help
.DEFAULT_GOAL := help

# ==============================================================================
# Help Target
# ==============================================================================

.PHONY: help
help:
	@echo "================================================================================"
	@echo "RTL Master Makefile - Lint & Synthesis"
	@echo "================================================================================"
	@echo ""
	@echo "LINT TARGETS (all areas):"
	@echo "  make lint-all             Run all lint tools on all RTL areas"
	@echo "  make verilator-all        Run Verilator on all areas"
	@echo "  make verible-all          Run Verible on all areas"
	@echo "  make yosys-all            Run Yosys on all areas"
	@echo ""
	@echo "AREA-SPECIFIC TARGETS:"
	@echo "  make lint-common          Run lint on rtl/common/"
	@echo "  make lint-amba            Run lint on rtl/amba/"
	@echo "  make verilator-common     Run Verilator on common modules"
	@echo "  make verilator-amba       Run Verilator on AMBA modules"
	@echo ""
	@echo "REPORT TARGETS:"
	@echo "  make report               Generate combined lint report"
	@echo "  make status               Show status of all RTL areas"
	@echo ""
	@echo "CLEAN TARGETS:"
	@echo "  make clean-all            Clean all lint artifacts"
	@echo "  make clean-common         Clean common lint artifacts"
	@echo "  make clean-amba           Clean AMBA lint artifacts"
	@echo ""
	@echo "================================================================================"
	@echo "Prerequisites: source $(REPO_ROOT)/env_python"
	@echo "Current REPO_ROOT: $(REPO_ROOT)"
	@echo "================================================================================"

# ==============================================================================
# Combined Lint Targets
# ==============================================================================

.PHONY: lint-all
lint-all: lint-common lint-amba
	@echo "================================================================================"
	@echo "✓ All RTL areas linted"
	@echo "================================================================================"

.PHONY: verilator-all
verilator-all: verilator-common verilator-amba
	@echo "================================================================================"
	@echo "✓ Verilator completed on all RTL areas"
	@echo "================================================================================"

.PHONY: verible-all
verible-all: verible-common verible-amba
	@echo "================================================================================"
	@echo "✓ Verible completed on all RTL areas"
	@echo "================================================================================"

.PHONY: yosys-all
yosys-all: yosys-common yosys-amba
	@echo "================================================================================"
	@echo "✓ Yosys completed on all RTL areas"
	@echo "================================================================================"

# ==============================================================================
# Common Targets
# ==============================================================================

.PHONY: lint-common
lint-common:
	@echo "=== RTL Common Area ==="
	@$(MAKE) -C $(COMMON_DIR) lint-all

.PHONY: verilator-common
verilator-common:
	@echo "=== RTL Common Area (Verilator) ==="
	@$(MAKE) -C $(COMMON_DIR) verilator

.PHONY: verible-common
verible-common:
	@echo "=== RTL Common Area (Verible) ==="
	@$(MAKE) -C $(COMMON_DIR) verible

.PHONY: yosys-common
yosys-common:
	@echo "=== RTL Common Area (Yosys) ==="
	@$(MAKE) -C $(COMMON_DIR) yosys

# ==============================================================================
# AMBA Targets
# ==============================================================================

.PHONY: lint-amba
lint-amba:
	@echo "=== RTL AMBA Area ==="
	@$(MAKE) -C $(AMBA_DIR) lint-all

.PHONY: verilator-amba
verilator-amba:
	@echo "=== RTL AMBA Area (Verilator) ==="
	@$(MAKE) -C $(AMBA_DIR) verilator

.PHONY: verible-amba
verible-amba:
	@echo "=== RTL AMBA Area (Verible) ==="
	@$(MAKE) -C $(AMBA_DIR) verible

.PHONY: yosys-amba
yosys-amba:
	@echo "=== RTL AMBA Area (Yosys) ==="
	@$(MAKE) -C $(AMBA_DIR) yosys

# ==============================================================================
# Report Targets
# ==============================================================================

.PHONY: report
report:
	@echo "================================================================================"
	@echo "RTL Master Lint Report"
	@echo "================================================================================"
	@echo ""
	@echo "=== RTL Common ==="
	@$(MAKE) -C $(COMMON_DIR) status 2>/dev/null | grep -A 10 "SystemVerilog files:"
	@echo ""
	@echo "=== RTL AMBA ==="
	@$(MAKE) -C $(AMBA_DIR) status 2>/dev/null | grep -A 10 "SystemVerilog files:"
	@echo ""
	@echo "================================================================================"

.PHONY: status
status:
	@echo "================================================================================"
	@echo "RTL Master Status"
	@echo "================================================================================"
	@echo "Location: $(REPO_ROOT)/rtl/"
	@echo ""
	@echo "RTL areas:"
	@echo "  Common modules:  $$(find $(COMMON_DIR) -name '*.sv' 2>/dev/null | wc -l) files"
	@echo "  AMBA protocols:  $$(find $(AMBA_DIR) -name '*.sv' 2>/dev/null | wc -l) files"
	@echo "  Total:           $$(find $(COMMON_DIR) $(AMBA_DIR) -name '*.sv' 2>/dev/null | wc -l) files"
	@echo ""
	@echo "Sub-makefiles:"
	@echo "  rtl/common/Makefile: ✓"
	@echo "  rtl/amba/Makefile:   ✓"
	@echo ""
	@echo "Environment:"
	@echo "  REPO_ROOT: $(REPO_ROOT)"
	@echo "================================================================================"

# ==============================================================================
# Clean Targets
# ==============================================================================

.PHONY: clean-common
clean-common:
	@echo "Cleaning common lint artifacts..."
	@$(MAKE) -C $(COMMON_DIR) clean-all

.PHONY: clean-amba
clean-amba:
	@echo "Cleaning AMBA lint artifacts..."
	@$(MAKE) -C $(AMBA_DIR) clean-all

.PHONY: clean-all
clean-all: clean-common clean-amba
	@echo "================================================================================"
	@echo "✓ All RTL lint artifacts cleaned"
	@echo "================================================================================"

# ==============================================================================
# Quick Aliases
# ==============================================================================

.PHONY: lint
lint: lint-all

.PHONY: verilator
verilator: verilator-all

.PHONY: verible
verible: verible-all

.PHONY: yosys
yosys: yosys-all

.PHONY: clean
clean: clean-all

# ==============================================================================
# End of Makefile
# ==============================================================================
