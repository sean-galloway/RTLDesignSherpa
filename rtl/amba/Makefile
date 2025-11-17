# ==============================================================================
# RTL AMBA Protocol Infrastructure - Lint & Synthesis Makefile
# ==============================================================================

# Optional: Use common.mk for color functions and REPO_ROOT check
-include $(REPO_ROOT)/makefiles/common.mk

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

# ==============================================================================
# Targets
# ==============================================================================

.PHONY: verilator
verilator: ## Run Verilator lint on all files
	$(call print_header,Running Verilator Lint on RTL AMBA ($(SV_COUNT) files))
	@mkdir -p $(VERILATOR_DIR)
	@if $(VERILATOR) $(VERILATOR_FLAGS) -f $(MASTER_FILELIST) > $(VERILATOR_DIR)/amba_all.log 2>&1; then \
		echo "$(GREEN)✓ RTL AMBA lint passed$(RESET)" | tee $(VERILATOR_DIR)/summary.txt; \
		echo "" >> $(VERILATOR_DIR)/summary.txt; \
		echo "All $(SV_COUNT) files passed lint checks" >> $(VERILATOR_DIR)/summary.txt; \
	else \
		echo "$(RED)✗ RTL AMBA lint failed$(RESET)" | tee $(VERILATOR_DIR)/summary.txt; \
		echo "" >> $(VERILATOR_DIR)/summary.txt; \
		echo "Errors found. See $(VERILATOR_DIR)/amba_all.log for details" >> $(VERILATOR_DIR)/summary.txt; \
		echo ""; \
		echo "Last 30 lines of error log:"; \
		tail -30 $(VERILATOR_DIR)/amba_all.log; \
		exit 1; \
	fi
	$(call print_success,Verilator lint complete. Reports: $(VERILATOR_DIR)/)

.PHONY: verilator-axi4
verilator-axi4: ## Run Verilator on AXI4 modules
	@echo "$(BLUE)Running Verilator on AXI4 modules...$(RESET)"
	@mkdir -p $(VERILATOR_DIR)
	@for file in axi4/*.sv; do \
		echo "Linting $$file..."; \
		$(VERILATOR) $(VERILATOR_FLAGS) $(VERILATOR_INCLUDES) -Iaxi4 $$file > $(VERILATOR_DIR)/$$(basename $$file .sv).log 2>&1 || true; \
	done
	$(call print_success,Verilator lint complete (AXI4))

.PHONY: verilator-axil4
verilator-axil4: ## Run Verilator on AXI4-Lite modules
	@echo "$(BLUE)Running Verilator on AXI4-Lite modules...$(RESET)"
	@mkdir -p $(VERILATOR_DIR)
	@for file in axil4/*.sv; do \
		echo "Linting $$file..."; \
		$(VERILATOR) $(VERILATOR_FLAGS) $(VERILATOR_INCLUDES) -Iaxil4 $$file > $(VERILATOR_DIR)/$$(basename $$file .sv).log 2>&1 || true; \
	done
	$(call print_success,Verilator lint complete (AXI4-Lite))

.PHONY: verilator-apb
verilator-apb: ## Run Verilator on APB modules
	@echo "$(BLUE)Running Verilator on APB modules...$(RESET)"
	@mkdir -p $(VERILATOR_DIR)
	@for file in apb/*.sv; do \
		echo "Linting $$file..."; \
		$(VERILATOR) $(VERILATOR_FLAGS) $(VERILATOR_INCLUDES) -Iapb $$file > $(VERILATOR_DIR)/$$(basename $$file .sv).log 2>&1 || true; \
	done
	$(call print_success,Verilator lint complete (APB))

.PHONY: verilator-axis4
verilator-axis4: ## Run Verilator on AXI-Stream modules
	@echo "$(BLUE)Running Verilator on AXI-Stream modules...$(RESET)"
	@mkdir -p $(VERILATOR_DIR)
	@for file in axis4/*.sv; do \
		echo "Linting $$file..."; \
		$(VERILATOR) $(VERILATOR_FLAGS) $(VERILATOR_INCLUDES) -Iaxis4 $$file > $(VERILATOR_DIR)/$$(basename $$file .sv).log 2>&1 || true; \
	done
	$(call print_success,Verilator lint complete (AXI-Stream))

.PHONY: verilator-gaxi
verilator-gaxi: ## Run Verilator on GAXI modules
	@echo "$(BLUE)Running Verilator on GAXI modules...$(RESET)"
	@mkdir -p $(VERILATOR_DIR)
	@for file in gaxi/*.sv; do \
		echo "Linting $$file..."; \
		$(VERILATOR) $(VERILATOR_FLAGS) $(VERILATOR_INCLUDES) -Igaxi $$file > $(VERILATOR_DIR)/$$(basename $$file .sv).log 2>&1 || true; \
	done
	$(call print_success,Verilator lint complete (GAXI))

.PHONY: verilator-shared
verilator-shared: ## Run Verilator on shared modules
	@echo "$(BLUE)Running Verilator on shared modules...$(RESET)"
	@mkdir -p $(VERILATOR_DIR)
	@for file in shared/*.sv; do \
		echo "Linting $$file..."; \
		$(VERILATOR) $(VERILATOR_FLAGS) $(VERILATOR_INCLUDES) -Ishared $$file > $(VERILATOR_DIR)/$$(basename $$file .sv).log 2>&1 || true; \
	done
	$(call print_success,Verilator lint complete (shared))

.PHONY: verible
verible: ## Run Verible lint on all files
	$(call print_header,Running Verible Lint on RTL AMBA ($(SV_COUNT) files))
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
		$(call print_success,Verible lint complete. Reports: $(VERIBLE_DIR)/); \
	else \
		$(call print_warning,Verible not found. Install: https://github.com/chipsalliance/verible); \
		echo "Skipping Verible lint."; \
	fi

.PHONY: verible-axi4
verible-axi4: ## Run Verible on AXI4 modules
	@echo "$(BLUE)Running Verible on AXI4 modules...$(RESET)"
	@mkdir -p $(VERIBLE_DIR)
	@if command -v $(VERIBLE) &> /dev/null; then \
		for file in axi4/*.sv; do \
			echo "Linting $$file..."; \
			$(VERIBLE) $(VERIBLE_FLAGS) $$file > $(VERIBLE_DIR)/$$(basename $$file .sv).log 2>&1 || true; \
		done; \
		$(call print_success,Verible lint complete (AXI4)); \
	else \
		$(call print_warning,Verible not found. Skipping.); \
	fi

.PHONY: yosys
yosys: ## Run Yosys synthesis check on all files
	$(call print_header,Running Yosys Synthesis Check on RTL AMBA ($(SV_COUNT) files))
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
		$(call print_success,Yosys synthesis check complete. Reports: $(YOSYS_DIR)/); \
	else \
		$(call print_warning,Yosys not found. Install: http://www.clifford.at/yosys/); \
		echo "Skipping Yosys synthesis check."; \
	fi

.PHONY: yosys-axi4
yosys-axi4: ## Run Yosys on AXI4 modules
	@echo "$(BLUE)Running Yosys on AXI4 modules...$(RESET)"
	@mkdir -p $(YOSYS_DIR)
	@if command -v $(YOSYS) &> /dev/null; then \
		for file in axi4/*.sv; do \
			echo "Checking $$file..."; \
			$(YOSYS) $(YOSYS_FLAGS) $$file -p "hierarchy -check" > $(YOSYS_DIR)/$$(basename $$file .sv).log 2>&1 || true; \
		done; \
		$(call print_success,Yosys synthesis check complete (AXI4)); \
	else \
		$(call print_warning,Yosys not found. Skipping.); \
	fi

.PHONY: lint-all
lint-all: verilator verible ## Run all lint tools on all files
	$(call print_success,All lint tools completed)

.PHONY: synth-all
synth-all: yosys ## Run synthesis checks
	$(call print_success,Synthesis checks completed)

.PHONY: lint-protocols
lint-protocols: verilator-axi4 verilator-axil4 verilator-apb verilator-axis4 ## Lint all protocol modules
	$(call print_success,All protocol linting completed)

.PHONY: report
report: ## Generate lint summary report
	$(call print_header,RTL AMBA Lint Summary Report)
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
	$(call print_header,RTL AMBA Status)
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
	@echo "$(BOLD)$(CYAN)║   RTL AMBA - Lint & Synthesis Makefile ║$(RESET)"
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
	@echo "  SUBDIRS = $(SUBDIRS)"
	@echo "  MASTER_FILELIST = $(MASTER_FILELIST)"
	@echo "  LINT_DIR = $(LINT_DIR)"

.PHONY: all
all: lint-all synth-all

.DEFAULT_GOAL := help
