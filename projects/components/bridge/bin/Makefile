# ==============================================================================
# BRIDGE GENERATOR - Makefile
# ==============================================================================
#
# Purpose: Generate AXI4 crossbar bridges from CSV configurations
#
# Usage:
#   make help           Show this help
#   make all            Generate all bridges from bridge_batch.csv
#   make single         Generate single bridge (requires PORTS, CONN, NAME)
#   make clean          Remove generated RTL
#   make batch          Create default bridge_batch.csv
#
# ==============================================================================

# Force bash shell
SHELL := /bin/bash

# Check if REPO_ROOT is set (from env_python)
ifndef REPO_ROOT
$(error REPO_ROOT is not set. Please run: source $$REPO_ROOT/env_python)
endif

# Directories
BIN_DIR := $(CURDIR)
RTL_DIR := $(REPO_ROOT)/projects/components/bridge/rtl
CSV_DIR := $(REPO_ROOT)/projects/components/bridge/dv/bridge_csv

# Generator script
GENERATOR := $(BIN_DIR)/bridge_generator.py

# Batch file
BATCH_FILE := $(BIN_DIR)/bridge_batch.csv

# Default batch file content
define BATCH_CONTENT
name,ports,connectivity,output_dir,expose_arbiter_signals
# Bridge Batch Generation Configuration
#
# This file defines all bridges to be generated.
# Lines starting with # are treated as comments.
#
# Columns:
#   name               - Output module name (empty = auto-generated)
#   ports              - Path to ports.csv configuration
#   connectivity       - Path to connectivity.csv configuration
#   output_dir         - Output directory for generated RTL
#   expose_arbiter_signals - true/false for debug signals
#
# ==============================================================================
# Test Bridges
# ==============================================================================

# 2x2 Basic Bridge
bridge_2x2_basic,$(CSV_DIR)/test_2x2_ports.csv,$(CSV_DIR)/test_2x2_connectivity.csv,$(RTL_DIR),false

# 4x4 Full Bridge
bridge_4x4_full,$(CSV_DIR)/test_4x4_ports.csv,$(CSV_DIR)/test_4x4_connectivity.csv,$(RTL_DIR),false

# 5x3 Channel-Specific Bridge
bridge_5x3_channels,$(CSV_DIR)/test_5x3_channels_ports.csv,$(CSV_DIR)/test_5x3_channels_connectivity.csv,$(RTL_DIR),false

# ==============================================================================
# Minimal Test Bridges (Read/Write Only)
# ==============================================================================

# 1x2 Read-Only Bridge
bridge_1x2_rd,$(CSV_DIR)/bridge_minimal_rd_1x2_ports.csv,$(CSV_DIR)/bridge_minimal_rd_1x2_connectivity.csv,$(RTL_DIR),false

# 1x2 Write-Only Bridge
bridge_1x2_wr,$(CSV_DIR)/bridge_minimal_wr_1x2_ports.csv,$(CSV_DIR)/bridge_minimal_wr_1x2_connectivity.csv,$(RTL_DIR),false

# ==============================================================================
# Example Bridges (For Documentation)
# ==============================================================================

# Example Bridge (Basic)
# bridge_example,$(CSV_DIR)/example_ports.csv,$(CSV_DIR)/example_connectivity.csv,$(RTL_DIR),false

# Example Bridge (Channel-Specific)
# bridge_example_channels,$(CSV_DIR)/example_ports_channels.csv,$(CSV_DIR)/example_connectivity_channels.csv,$(RTL_DIR),false

# Example Bridge (Out-of-Order)
# bridge_example_ooo,$(CSV_DIR)/example_ports_ooo.csv,$(CSV_DIR)/example_connectivity.csv,$(RTL_DIR),true
endef
export BATCH_CONTENT

.DEFAULT_GOAL := help

.PHONY: help
help:
	@echo "================================================================================"
	@echo "BRIDGE GENERATOR - Makefile"
	@echo "================================================================================"
	@echo ""
	@echo "GENERATION TARGETS:"
	@echo "  make all              Generate all bridges from bridge_batch.csv"
	@echo "  make single           Generate single bridge (see variables below)"
	@echo "  make batch            Create/update bridge_batch.csv with defaults"
	@echo ""
	@echo "SINGLE BRIDGE VARIABLES (for 'make single'):"
	@echo "  PORTS=<path>          Path to ports.csv (required)"
	@echo "  CONN=<path>           Path to connectivity.csv (required)"
	@echo "  NAME=<name>           Bridge name (optional, auto-generated if empty)"
	@echo "  OUTPUT=<dir>          Output directory (default: $(RTL_DIR))"
	@echo "  ARBITER=true/false    Expose arbiter signals (default: false)"
	@echo ""
	@echo "CLEAN TARGETS:"
	@echo "  make clean            Remove generated bridge directories"
	@echo "  make clean-all        Remove ALL generated files (dirs + old .sv + batch)"
	@echo ""
	@echo "STATUS TARGETS:"
	@echo "  make status           Show current configuration"
	@echo ""
	@echo "EXAMPLES:"
	@echo "  make all                                  # Generate all from batch file"
	@echo "  make single PORTS=test.csv CONN=conn.csv  # Generate single bridge"
	@echo "  make batch                                # Create default batch file"
	@echo ""
	@echo "================================================================================"
	@echo "Prerequisites: source $(REPO_ROOT)/env_python"
	@echo "Generator: $(GENERATOR)"
	@echo ""
	@echo "BATCH FILES:"
	@echo "  bridge_batch.csv         - Active batch file (used by 'make all')"
	@echo "  bridge_batch_example.csv - Example/template (for reference)"
	@echo ""
	@echo "Edit bridge_batch.csv to customize which bridges to generate."
	@echo "Run 'make batch' to regenerate bridge_batch.csv with defaults."
	@echo "================================================================================"

.PHONY: all
all: $(BATCH_FILE)
	@echo "================================================================================"
	@echo "Generating all bridges from: $(BATCH_FILE)"
	@echo "================================================================================"
	@cd $(BIN_DIR) && python3 $(GENERATOR) --bulk $(BATCH_FILE)
	@echo ""
	@echo "✓ All bridges generated successfully!"

.PHONY: single
single:
ifndef PORTS
	$(error PORTS variable not set. Usage: make single PORTS=path/to/ports.csv CONN=path/to/connectivity.csv)
endif
ifndef CONN
	$(error CONN variable not set. Usage: make single PORTS=path/to/ports.csv CONN=path/to/connectivity.csv)
endif
	@echo "================================================================================"
	@echo "Generating single bridge"
	@echo "  Ports: $(PORTS)"
	@echo "  Connectivity: $(CONN)"
	@echo "  Name: $(if $(NAME),$(NAME),auto-generated)"
	@echo "  Output: $(if $(OUTPUT),$(OUTPUT),$(RTL_DIR))"
	@echo "  Arbiter signals: $(if $(ARBITER),$(ARBITER),false)"
	@echo "================================================================================"
	@python3 $(GENERATOR) \
		--ports $(PORTS) \
		--connectivity $(CONN) \
		$(if $(NAME),--name $(NAME),) \
		--output-dir $(if $(OUTPUT),$(OUTPUT),$(RTL_DIR)) \
		$(if $(filter true,$(ARBITER)),--expose-arbiter-signals,)
	@echo ""
	@echo "✓ Single bridge generated successfully!"

.PHONY: batch
batch:
	@echo "Creating default bridge_batch.csv..."
	@echo "$$BATCH_CONTENT" > $(BATCH_FILE)
	@echo "✓ Created: $(BATCH_FILE)"
	@echo ""
	@echo "Edit this file to customize bridge generation, then run:"
	@echo "  make all"

$(BATCH_FILE):
	@$(MAKE) batch

.PHONY: status
status:
	@echo "================================================================================"
	@echo "BRIDGE GENERATOR Status"
	@echo "================================================================================"
	@echo "Location: $(BIN_DIR)"
	@echo "Generator: $(GENERATOR)"
	@echo "Batch file: $(BATCH_FILE) $(if $(wildcard $(BATCH_FILE)),[EXISTS],[NOT FOUND])"
	@echo "RTL output: $(RTL_DIR)"
	@echo "CSV configs: $(CSV_DIR)"
	@echo ""
	@if [ -f "$(BATCH_FILE)" ]; then \
		echo "Batch file contents:"; \
		echo "----------------------------------------"; \
		grep -v "^#" $(BATCH_FILE) | grep -v "^$$" | head -20; \
		echo "----------------------------------------"; \
	else \
		echo "No batch file found. Run 'make batch' to create one."; \
	fi
	@echo ""
	@echo "Generated bridges in $(RTL_DIR):"
	@ls -d $(RTL_DIR)/bridge_* 2>/dev/null | sed 's|$(RTL_DIR)/|  - |' || echo "  (none found)"
	@echo "================================================================================"

.PHONY: clean
clean:
	@echo "Cleaning generated bridge directories..."
	@rm -rf $(RTL_DIR)/bridge_*/
	@echo "✓ Generated bridge directories removed"

.PHONY: clean-all
clean-all: clean
	@echo "Removing old standalone bridge files..."
	@cd $(RTL_DIR) && find . -maxdepth 1 -name "bridge_*.sv" ! -name "bridge_cam.sv" -type f -delete
	@echo "✓ Old standalone bridge files removed (preserved bridge_cam.sv)"
	@echo "Removing batch file..."
	@rm -f $(BATCH_FILE)
	@echo "✓ Batch file removed"
	@echo ""
	@echo "All generated files cleaned. Run 'make all' to regenerate."

.PHONY: test
test:
	@echo "Testing bridge generator..."
	@python3 $(GENERATOR) --help | head -20
	@echo ""
	@echo "✓ Generator script is functional"
