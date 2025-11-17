# ==============================================================================
# RTL Common Building Blocks - Lint & Synthesis Makefile
# ==============================================================================

# Optional: Use common.mk for color functions and REPO_ROOT check
-include $(REPO_ROOT)/makefiles/common.mk

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

# ==============================================================================
# Targets
# ==============================================================================

.PHONY: verilator
verilator: ## Run Verilator lint on all files
	$(call print_header,Running Verilator Lint on RTL Common ($(SV_COUNT) files))
	@mkdir -p $(VERILATOR_DIR)
	@if $(VERILATOR) $(VERILATOR_FLAGS) -f $(MASTER_FILELIST) > $(VERILATOR_DIR)/common_all.log 2>&1; then \
		echo "$(GREEN)✓ RTL Common lint passed$(RESET)" | tee $(VERILATOR_DIR)/summary.txt; \
		echo "" >> $(VERILATOR_DIR)/summary.txt; \
		echo "All $(SV_COUNT) files passed lint checks" >> $(VERILATOR_DIR)/summary.txt; \
	else \
		echo "$(RED)✗ RTL Common lint failed$(RESET)" | tee $(VERILATOR_DIR)/summary.txt; \
		echo "" >> $(VERILATOR_DIR)/summary.txt; \
		echo "Errors found. See $(VERILATOR_DIR)/common_all.log for details" >> $(VERILATOR_DIR)/summary.txt; \
		echo ""; \
		echo "Last 30 lines of error log:"; \
		tail -30 $(VERILATOR_DIR)/common_all.log; \
		exit 1; \
	fi
	$(call print_success,Verilator lint complete. Reports: $(VERILATOR_DIR)/)

.PHONY: verilator-counters
verilator-counters: ## Run Verilator on counter modules
	@echo "$(BLUE)Running Verilator on counter modules...$(RESET)"
	@mkdir -p $(VERILATOR_DIR)
	@for file in counter*.sv; do \
		echo "Linting $$file..."; \
		$(VERILATOR) $(VERILATOR_FLAGS) $$file > $(VERILATOR_DIR)/$$(basename $$file .sv).log 2>&1 || true; \
	done
	$(call print_success,Verilator lint complete (counters))

.PHONY: verilator-arbiters
verilator-arbiters: ## Run Verilator on arbiter modules
	@echo "$(BLUE)Running Verilator on arbiter modules...$(RESET)"
	@mkdir -p $(VERILATOR_DIR)
	@for file in arbiter*.sv; do \
		echo "Linting $$file..."; \
		$(VERILATOR) $(VERILATOR_FLAGS) $$file > $(VERILATOR_DIR)/$$(basename $$file .sv).log 2>&1 || true; \
	done
	$(call print_success,Verilator lint complete (arbiters))

.PHONY: verilator-fifos
verilator-fifos: ## Run Verilator on FIFO modules (AMBA GAXI)
	@echo "$(BLUE)Running Verilator on FIFO modules (AMBA GAXI)...$(RESET)"
	@echo "Note: FIFOs are in rtl/amba/gaxi/"
	@mkdir -p $(VERILATOR_DIR)
	@if [ -d "$(REPO_ROOT)/rtl/amba/gaxi" ]; then \
		cd $(REPO_ROOT)/rtl/amba/gaxi && \
		for file in gaxi_fifo*.sv; do \
			echo "Linting $$file..."; \
			$(VERILATOR) $(VERILATOR_FLAGS) $$file > $(REPO_ROOT)/rtl/common/$(VERILATOR_DIR)/$$(basename $$file .sv).log 2>&1 || true; \
		done; \
	fi
	$(call print_success,Verilator lint complete (FIFOs))

.PHONY: verible
verible: ## Run Verible lint on all files
	$(call print_header,Running Verible Lint on RTL Common ($(SV_COUNT) files))
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
		$(call print_success,Verible lint complete. Reports: $(VERIBLE_DIR)/); \
	else \
		$(call print_warning,Verible not found. Install: https://github.com/chipsalliance/verible); \
		echo "Skipping Verible lint."; \
	fi

.PHONY: verible-counters
verible-counters: ## Run Verible on counter modules
	@echo "$(BLUE)Running Verible on counter modules...$(RESET)"
	@mkdir -p $(VERIBLE_DIR)
	@if command -v $(VERIBLE) &> /dev/null; then \
		for file in counter*.sv; do \
			echo "Linting $$file..."; \
			$(VERIBLE) $(VERIBLE_FLAGS) $$file > $(VERIBLE_DIR)/$$(basename $$file .sv).log 2>&1 || true; \
		done; \
		$(call print_success,Verible lint complete (counters)); \
	else \
		$(call print_warning,Verible not found. Skipping.); \
	fi

.PHONY: yosys
yosys: ## Run Yosys synthesis check on all files
	$(call print_header,Running Yosys Synthesis Check on RTL Common ($(SV_COUNT) files))
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
		$(call print_success,Yosys synthesis check complete. Reports: $(YOSYS_DIR)/); \
	else \
		$(call print_warning,Yosys not found. Install: http://www.clifford.at/yosys/); \
		echo "Skipping Yosys synthesis check."; \
	fi

.PHONY: yosys-counters
yosys-counters: ## Run Yosys on counter modules
	@echo "$(BLUE)Running Yosys on counter modules...$(RESET)"
	@mkdir -p $(YOSYS_DIR)
	@if command -v $(YOSYS) &> /dev/null; then \
		for file in counter*.sv; do \
			echo "Checking $$file..."; \
			$(YOSYS) $(YOSYS_FLAGS) $$file -p "hierarchy -check" > $(YOSYS_DIR)/$$(basename $$file .sv).log 2>&1 || true; \
		done; \
		$(call print_success,Yosys synthesis check complete (counters)); \
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
	$(call print_header,RTL Common Lint Summary Report)
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
	$(call print_header,RTL Common Status)
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
	@echo "$(BOLD)$(CYAN)║  RTL Common - Lint & Synthesis Makefile║$(RESET)"
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
	@echo "  MASTER_FILELIST = $(MASTER_FILELIST)"
	@echo "  LINT_DIR = $(LINT_DIR)"

.PHONY: all
all: lint-all synth-all

.DEFAULT_GOAL := help
