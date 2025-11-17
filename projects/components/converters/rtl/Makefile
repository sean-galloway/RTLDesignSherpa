# ==============================================================================
# Converters RTL - Lint & Synthesis Makefile
# ==============================================================================

# Optional: Use common.mk for color functions and REPO_ROOT check
-include $(REPO_ROOT)/makefiles/common.mk

# Find all SystemVerilog files
SV_FILES := $(shell find . -name "*.sv" -type f)
SV_COUNT := $(words $(SV_FILES))

# Lint output directories
LINT_DIR = lint_reports
VERILATOR_DIR = $(LINT_DIR)/verilator
VERIBLE_DIR = $(LINT_DIR)/verible
YOSYS_DIR = $(LINT_DIR)/yosys

# Include paths
INCLUDES = -I$(REPO_ROOT)/rtl/common -I$(REPO_ROOT)/rtl/amba/includes

# Tool options
VERILATOR = verilator
VERILATOR_FLAGS = --lint-only -Wall -Wno-TIMESCALEMOD $(INCLUDES)

VERIBLE = verible-verilog-lint
VERIBLE_FLAGS = --rules_config_search --rules=-parameter-name-style,-line-length

YOSYS = yosys
YOSYS_FLAGS = -p "read_verilog -sv"

# ==============================================================================
# Targets
# ==============================================================================

.PHONY: verilator
verilator: ## Run Verilator lint on all files
	$(call print_header,Running Verilator Lint on Converters RTL ($(SV_COUNT) files))
	@mkdir -p $(VERILATOR_DIR)
	@for file in $(SV_FILES); do \
		echo "Linting $$file..."; \
		$(VERILATOR) $(VERILATOR_FLAGS) $$file > $(VERILATOR_DIR)/$$(basename $$file .sv).log 2>&1 || true; \
	done
	$(call print_success,Verilator lint complete)

.PHONY: verible
verible: ## Run Verible lint on all files
	$(call print_header,Running Verible Lint on Converters RTL ($(SV_COUNT) files))
	@mkdir -p $(VERIBLE_DIR)
	@if command -v $(VERIBLE) &> /dev/null; then \
		for file in $(SV_FILES); do \
			echo "Linting $$file..."; \
			$(VERIBLE) $(VERIBLE_FLAGS) $$file > $(VERIBLE_DIR)/$$(basename $$file .sv).log 2>&1 || true; \
		done; \
		$(call print_success,Verible lint complete); \
	else \
		$(call print_warning,Verible not found. Skipping.); \
	fi

.PHONY: yosys
yosys: ## Run Yosys synthesis check on all files
	$(call print_header,Running Yosys Synthesis Check on Converters RTL ($(SV_COUNT) files))
	@mkdir -p $(YOSYS_DIR)
	@if command -v $(YOSYS) &> /dev/null; then \
		for file in $(SV_FILES); do \
			echo "Checking $$file..."; \
			$(YOSYS) $(YOSYS_FLAGS) $$file -p "hierarchy -check" > $(YOSYS_DIR)/$$(basename $$file .sv).log 2>&1 || true; \
		done; \
		$(call print_success,Yosys synthesis check complete); \
	else \
		$(call print_warning,Yosys not found. Skipping.); \
	fi

.PHONY: lint-all
lint-all: verilator verible ## Run all lint tools on all files
	$(call print_success,All lint tools completed)

.PHONY: synth-all
synth-all: yosys ## Run synthesis checks
	$(call print_success,Synthesis checks completed)

.PHONY: report
report: ## Generate lint summary report
	$(call print_header,Converters RTL Lint Summary Report)
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

.PHONY: status
status: ## Show file counts and lint status
	$(call print_header,Converters RTL Status)
	@echo "Location: $(REPO_ROOT)/projects/components/converters/rtl/"
	@echo ""
	@echo "SystemVerilog files: $(SV_COUNT)"
	@echo ""
	@echo "Lint reports:"
	@echo "  Verilator: $$(find $(VERILATOR_DIR) -name '*.log' 2>/dev/null | wc -l) reports"
	@echo "  Verible:   $$(find $(VERIBLE_DIR) -name '*.log' 2>/dev/null | wc -l) reports"
	@echo "  Yosys:     $$(find $(YOSYS_DIR) -name '*.log' 2>/dev/null | wc -l) reports"
	@echo ""
	@echo "Environment:"
	@echo "  REPO_ROOT: $(REPO_ROOT)"

.PHONY: clean-verilator
clean-verilator: ## Remove Verilator reports
	$(call print_info,Cleaning Verilator reports...)
	@rm -rf $(VERILATOR_DIR)
	$(call print_success,Verilator reports cleaned)

.PHONY: clean-verible
clean-verible: ## Remove Verible reports
	$(call print_info,Cleaning Verible reports...)
	@rm -rf $(VERIBLE_DIR)
	$(call print_success,Verible reports cleaned)

.PHONY: clean-yosys
clean-yosys: ## Remove Yosys reports
	$(call print_info,Cleaning Yosys reports...)
	@rm -rf $(YOSYS_DIR)
	$(call print_success,Yosys reports cleaned)

.PHONY: clean-all
clean-all: clean-verilator clean-verible clean-yosys ## Remove all lint artifacts
	$(call print_info,Cleaning all lint artifacts...)
	@rm -rf $(LINT_DIR)
	$(call print_success,All lint artifacts cleaned)

# Quick aliases
.PHONY: lint
lint: lint-all

.PHONY: synth
synth: synth-all

.PHONY: clean
clean: clean-all

# ==============================================================================
# Help
# ==============================================================================

.PHONY: help
help: ## Show this help message
	@echo "$(BOLD)$(CYAN)╔════════════════════════════════════════╗$(RESET)"
	@echo "$(BOLD)$(CYAN)║  Converters RTL - Lint & Synthesis     ║$(RESET)"
	@echo "$(BOLD)$(CYAN)╚════════════════════════════════════════╝$(RESET)"
	@echo ""
	@echo "$(GREEN)Targets:$(RESET)"
	@/bin/sh -c "grep -h -E '^[a-zA-Z_-]+:.*?## .*\$$' $(MAKEFILE_LIST) | sed -E 's/^([a-zA-Z_-]+):.*## (.*)\$$/\1@@@\2/' | awk -F'@@@' '{printf \"  %-30s %s\\n\", \$$1, \$$2}'"
	@echo ""
	@echo "$(GREEN)Environment:$(RESET)"
	@echo "  REPO_ROOT: $(REPO_ROOT)"
	@echo "  SystemVerilog files: $(SV_COUNT)"
	@echo ""

.PHONY: help-vars
help-vars: ## Show Makefile variables
	@echo "$(BOLD)Makefile Variables:$(RESET)"
	@echo "  SV_FILES = $(SV_FILES)"
	@echo "  SV_COUNT = $(SV_COUNT)"
	@echo "  LINT_DIR = $(LINT_DIR)"

.PHONY: all
all: lint-all synth-all

.DEFAULT_GOAL := help
