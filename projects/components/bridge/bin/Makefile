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
#   make batch          Verify bridge_batch.csv exists (git-tracked)
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
RTL_DIR := $(REPO_ROOT)/projects/components/bridge/rtl/generated
CSV_DIR := $(REPO_ROOT)/projects/components/bridge/dv/bridge_csv

# Generator script
GENERATOR := $(BIN_DIR)/bridge_generator.py

# Batch file
BATCH_FILE := $(BIN_DIR)/bridge_batch.csv


.DEFAULT_GOAL := help

.PHONY: help
help:
	@echo "================================================================================"
	@echo "BRIDGE GENERATOR - Makefile"
	@echo "================================================================================"
	@echo ""
	@echo "GENERATION TARGETS:"
	@echo "  make rtl              Generate all bridges (same as 'make all')"
	@echo "  make all              Generate all bridges from bridge_batch.csv"
	@echo "  make regen            Rule #0 full regen: clean + all (use after generator changes)"
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
	@echo "bridge_batch.csv is git-tracked; restore with git if lost."
	@echo "================================================================================"

.PHONY: all
all: $(BATCH_FILE)
	@echo "================================================================================"
	@echo "Generating all bridges from: $(BATCH_FILE)"
	@echo "================================================================================"
	@cd $(BIN_DIR) && python3 $(GENERATOR) --bulk $(BATCH_FILE)
	@echo ""
	@echo "✓ All bridges generated successfully!"

.PHONY: rtl
rtl: all

# Full Rule #0 regeneration: delete every generated bridge dir, then
# regenerate the complete batch (all *_mon variants included). Use this
# after ANY change to the generator or a shared RTL module the bridges
# pull in (e.g. the monbus_<p1>_<p2>_group family).
.PHONY: regen
regen: clean all
	@echo ""
	@echo "✓ Full regeneration complete (clean + all)."

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

# bridge_batch.csv is a hand-curated, git-tracked manifest -- NOT a
# generated artifact. Never overwrite it from a template; if missing,
# restore it from git.
.PHONY: batch
batch: $(BATCH_FILE)
	@echo "✓ Batch manifest present: $(BATCH_FILE)"

$(BATCH_FILE):
	@echo "Batch manifest missing -- restoring from git..."
	@git -C $(BIN_DIR) checkout -- $(notdir $(BATCH_FILE)) || \
		(echo "ERROR: could not restore $(BATCH_FILE) from git." && exit 1)

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
	@echo "All generated files cleaned. Run 'make all' to regenerate."
	@echo "(bridge_batch.csv is a git-tracked manifest and is never removed.)"

.PHONY: test
test:
	@echo "Testing bridge generator..."
	@python3 $(GENERATOR) --help | head -20
	@echo ""
	@echo "✓ Generator script is functional"
