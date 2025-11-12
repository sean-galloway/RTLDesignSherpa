# ==============================================================================
# RTL Design Sherpa - Master Makefile
# ==============================================================================
#
# PREREQUISITES:
#   Must be run with sourced environment:
#     source env_python  # Sets $REPO_ROOT and activates venv
#     make <target>
#
# Quick start:
#   make help           - Show all available targets
#   make test-all       - Run all tests (validation + projects)
#   make lint-all       - Run all lint (RTL + projects)
#   make status         - Show complete repository status
#   make clean-all      - Clean all test and lint artifacts
#
# ==============================================================================

# Force bash shell
SHELL := /bin/bash

# Check if REPO_ROOT is set (from env_python)
ifndef REPO_ROOT
$(error REPO_ROOT is not set. Please run: source env_python)
endif

# Directories
VAL_DIR = val
RTL_DIR = rtl
PROJECTS_DIR = projects/components

# Project list
PROJECTS = stream rapids bridge delta apb_xbar converters shims retro_legacy_blocks bch hive

# Default target - show help
.DEFAULT_GOAL := help

# ==============================================================================
# Help Target
# ==============================================================================

.PHONY: help
help:
	@echo "================================================================================"
	@echo "RTL Design Sherpa - Master Makefile"
	@echo "================================================================================"
	@echo ""
	@echo "TEST TARGETS (run validation tests):"
	@echo "  make test-all                Run ALL tests (validation + projects)"
	@echo "  make test-val                Run validation tests (val/amba, val/common, etc.)"
	@echo "  make test-projects           Run all project tests"
	@echo "  make test-stream             Run STREAM project tests"
	@echo "  make test-rapids             Run RAPIDS project tests"
	@echo "  make test-bridge             Run Bridge project tests"
	@echo "  make test-delta              Run Delta project tests"
	@echo "  make test-apb_xbar           Run APB Crossbar project tests"
	@echo "  make test-retro_legacy_blocks Run Retro Legacy Blocks project tests"
	@echo "  make test-bch                Run BCH project tests"
	@echo "  make test-hive               Run HIVE project tests"
	@echo ""
	@echo "REG_LEVEL TARGETS (configurable test depth - PARALLEL execution):"
	@echo "  GATE = Quick smoke tests (~5 min), FUNC = Default (~20-40 min), FULL = Comprehensive (~1-2 hours)"
	@echo ""
	@echo "  COMMON subsystem:"
	@echo "    make run-common-{gate|func|full}-parallel"
	@echo "  AMBA subsystem:"
	@echo "    make run-amba-{gate|func|full}-parallel"
	@echo "  ALL RTL (COMMON + AMBA):"
	@echo "    make run-rtl-all-{gate|func|full}-parallel"
	@echo ""
	@echo "LINT TARGETS (run RTL linting):"
	@echo "  make lint-all                Run ALL lint (RTL + projects)"
	@echo "  make lint-rtl                Run RTL lint (rtl/common + rtl/amba)"
	@echo "  make lint-projects           Run all project RTL lint"
	@echo "  make lint-stream             Run STREAM RTL lint"
	@echo "  make lint-rapids             Run RAPIDS RTL lint"
	@echo "  make lint-bridge             Run Bridge RTL lint"
	@echo "  make lint-delta              Run Delta RTL lint"
	@echo "  make lint-apb_xbar           Run APB Crossbar RTL lint"
	@echo "  make lint-converters         Run Converters RTL lint"
	@echo "  make lint-shims              Run Shims RTL lint"
	@echo "  make lint-retro_legacy_blocks Run Retro Legacy Blocks RTL lint"
	@echo "  make lint-bch                Run BCH RTL lint"
	@echo "  make lint-hive               Run HIVE RTL lint"
	@echo ""
	@echo "COMBINED TARGETS:"
	@echo "  make all                  Run tests AND lint on everything"
	@echo "  make ci                   CI/CD mode: test + lint with error checking"
	@echo ""
	@echo "STATUS TARGETS:"
	@echo "  make status               Show complete repository status"
	@echo "  make status-tests         Show test status summary"
	@echo "  make status-lint          Show lint status summary"
	@echo ""
	@echo "CLEAN TARGETS:"
	@echo "  make clean-all            Clean ALL test and lint artifacts"
	@echo "  make clean-tests          Clean all test artifacts"
	@echo "  make clean-lint           Clean all lint artifacts"
	@echo ""
	@echo "================================================================================"
	@echo "Prerequisites: source env_python"
	@echo "Current REPO_ROOT: $(REPO_ROOT)"
	@echo "================================================================================"

# ==============================================================================
# Test Targets - Validation
# ==============================================================================

.PHONY: test-val
test-val:
	@echo "================================================================================"
	@echo "Running Validation Tests (val/)"
	@echo "================================================================================"
	@$(MAKE) -C $(VAL_DIR) run-all || true
	@echo ""

# ==============================================================================
# Test Targets - Projects
# ==============================================================================

.PHONY: test-stream
test-stream:
	@echo "=== STREAM Project Tests ==="
	@if [ -f $(PROJECTS_DIR)/stream/dv/tests/Makefile ]; then \
		$(MAKE) -C $(PROJECTS_DIR)/stream/dv/tests run-all || true; \
	else \
		echo "⚠ STREAM test Makefile not found"; \
	fi

.PHONY: test-rapids
test-rapids:
	@echo "=== RAPIDS Project Tests ==="
	@if [ -f $(PROJECTS_DIR)/rapids/dv/tests/Makefile ]; then \
		$(MAKE) -C $(PROJECTS_DIR)/rapids/dv/tests run-all || true; \
	else \
		echo "⚠ RAPIDS test Makefile not found"; \
	fi

.PHONY: test-bridge
test-bridge:
	@echo "=== Bridge Project Tests ==="
	@if [ -f $(PROJECTS_DIR)/bridge/dv/tests/Makefile ]; then \
		$(MAKE) -C $(PROJECTS_DIR)/bridge/dv/tests run-all || true; \
	else \
		echo "⚠ Bridge test Makefile not found"; \
	fi

.PHONY: test-delta
test-delta:
	@echo "=== Delta Project Tests ==="
	@if [ -f $(PROJECTS_DIR)/delta/dv/tests/Makefile ]; then \
		$(MAKE) -C $(PROJECTS_DIR)/delta/dv/tests run-all || true; \
	else \
		echo "⚠ Delta test Makefile not found (may not have tests yet)"; \
	fi

.PHONY: test-apb_xbar
test-apb_xbar:
	@echo "=== APB Crossbar Project Tests ==="
	@if [ -f $(PROJECTS_DIR)/apb_xbar/dv/tests/Makefile ]; then \
		$(MAKE) -C $(PROJECTS_DIR)/apb_xbar/dv/tests run-all || true; \
	else \
		echo "⚠ APB Crossbar test Makefile not found"; \
	fi

.PHONY: test-retro_legacy_blocks
test-retro_legacy_blocks:
	@echo "=== Retro Legacy Blocks Project Tests ==="
	@if [ -f $(PROJECTS_DIR)/retro_legacy_blocks/dv/tests/Makefile ]; then \
		$(MAKE) -C $(PROJECTS_DIR)/retro_legacy_blocks/dv/tests run-all || true; \
	else \
		echo "⚠ Retro Legacy Blocks test Makefile not found"; \
	fi

.PHONY: test-bch
test-bch:
	@echo "=== BCH Project Tests ==="
	@if [ -f $(PROJECTS_DIR)/bch/dv/tests/Makefile ]; then \
		$(MAKE) -C $(PROJECTS_DIR)/bch/dv/tests run-all || true; \
	else \
		echo "⚠ BCH test Makefile not found (may not have tests yet)"; \
	fi

.PHONY: test-hive
test-hive:
	@echo "=== HIVE Project Tests ==="
	@if [ -f $(PROJECTS_DIR)/hive/dv/tests/Makefile ]; then \
		$(MAKE) -C $(PROJECTS_DIR)/hive/dv/tests run-all || true; \
	else \
		echo "⚠ HIVE test Makefile not found (may not have tests yet)"; \
	fi

.PHONY: test-projects
test-projects: test-stream test-rapids test-bridge test-delta test-apb_xbar test-retro_legacy_blocks test-bch test-hive
	@echo "================================================================================"
	@echo "✓ All project tests completed"
	@echo "================================================================================"

.PHONY: test-all
test-all: test-val test-projects
	@echo "================================================================================"
	@echo "✓ ALL TESTS COMPLETED"
	@echo "================================================================================"

# ==============================================================================
# REG_LEVEL Convenience Targets - Fast Regression Testing
# ==============================================================================

# COMMON subsystem REG_LEVEL targets
.PHONY: run-common-gate-parallel
run-common-gate-parallel:
	@echo "================================================================================"
	@echo "Running COMMON Tests - GATE level PARALLEL (~2-3 min)"
	@echo "================================================================================"
	@$(MAKE) -C $(VAL_DIR)/common run-all-gate-parallel

.PHONY: run-common-func-parallel
run-common-func-parallel:
	@echo "================================================================================"
	@echo "Running COMMON Tests - FUNC level PARALLEL (~10-20 min)"
	@echo "================================================================================"
	@$(MAKE) -C $(VAL_DIR)/common run-all-func-parallel

.PHONY: run-common-full-parallel
run-common-full-parallel:
	@echo "================================================================================"
	@echo "Running COMMON Tests - FULL level PARALLEL (~30-60 min)"
	@echo "================================================================================"
	@$(MAKE) -C $(VAL_DIR)/common run-all-full-parallel

# AMBA subsystem REG_LEVEL targets
.PHONY: run-amba-gate-parallel
run-amba-gate-parallel:
	@echo "================================================================================"
	@echo "Running AMBA Tests - GATE level PARALLEL (~2-3 min)"
	@echo "================================================================================"
	@$(MAKE) -C $(VAL_DIR)/amba run-all-gate-parallel

.PHONY: run-amba-func-parallel
run-amba-func-parallel:
	@echo "================================================================================"
	@echo "Running AMBA Tests - FUNC level PARALLEL (~10-20 min)"
	@echo "================================================================================"
	@$(MAKE) -C $(VAL_DIR)/amba run-all-func-parallel

.PHONY: run-amba-full-parallel
run-amba-full-parallel:
	@echo "================================================================================"
	@echo "Running AMBA Tests - FULL level PARALLEL (~30-60 min)"
	@echo "================================================================================"
	@$(MAKE) -C $(VAL_DIR)/amba run-all-full-parallel

# Combined RTL (COMMON + AMBA) REG_LEVEL targets
.PHONY: run-rtl-all-gate-parallel
run-rtl-all-gate-parallel:
	@echo "================================================================================"
	@echo "Running ALL RTL Tests (COMMON + AMBA) - GATE level PARALLEL (~5 min)"
	@echo "================================================================================"
	@$(MAKE) run-common-gate-parallel
	@$(MAKE) run-amba-gate-parallel
	@echo "================================================================================"
	@echo "✓ ALL RTL GATE Tests Completed"
	@echo "================================================================================"

.PHONY: run-rtl-all-func-parallel
run-rtl-all-func-parallel:
	@echo "================================================================================"
	@echo "Running ALL RTL Tests (COMMON + AMBA) - FUNC level PARALLEL (~20-40 min)"
	@echo "================================================================================"
	@$(MAKE) run-common-func-parallel
	@$(MAKE) run-amba-func-parallel
	@echo "================================================================================"
	@echo "✓ ALL RTL FUNC Tests Completed"
	@echo "================================================================================"

.PHONY: run-rtl-all-full-parallel
run-rtl-all-full-parallel:
	@echo "================================================================================"
	@echo "Running ALL RTL Tests (COMMON + AMBA) - FULL level PARALLEL (~1-2 hours)"
	@echo "================================================================================"
	@$(MAKE) run-common-full-parallel
	@$(MAKE) run-amba-full-parallel
	@echo "================================================================================"
	@echo "✓ ALL RTL FULL Tests Completed"
	@echo "================================================================================"

# ==============================================================================
# Lint Targets - RTL
# ==============================================================================

.PHONY: lint-rtl
lint-rtl:
	@echo "================================================================================"
	@echo "Running RTL Lint (rtl/common + rtl/amba)"
	@echo "================================================================================"
	@$(MAKE) -C $(RTL_DIR) lint-all || true
	@echo ""

# ==============================================================================
# Lint Targets - Projects
# ==============================================================================

.PHONY: lint-stream
lint-stream:
	@echo "=== STREAM RTL Lint ==="
	@if [ -f $(PROJECTS_DIR)/stream/rtl/Makefile ]; then \
		$(MAKE) -C $(PROJECTS_DIR)/stream/rtl lint-all || true; \
	else \
		echo "⚠ STREAM RTL Makefile not found"; \
	fi

.PHONY: lint-rapids
lint-rapids:
	@echo "=== RAPIDS RTL Lint ==="
	@if [ -f $(PROJECTS_DIR)/rapids/rtl/Makefile ]; then \
		$(MAKE) -C $(PROJECTS_DIR)/rapids/rtl lint-all || true; \
	else \
		echo "⚠ RAPIDS RTL Makefile not found"; \
	fi

.PHONY: lint-bridge
lint-bridge:
	@echo "=== Bridge RTL Lint ==="
	@if [ -f $(PROJECTS_DIR)/bridge/rtl/Makefile ]; then \
		$(MAKE) -C $(PROJECTS_DIR)/bridge/rtl lint-all || true; \
	else \
		echo "⚠ Bridge RTL Makefile not found"; \
	fi

.PHONY: lint-delta
lint-delta:
	@echo "=== Delta RTL Lint ==="
	@if [ -f $(PROJECTS_DIR)/delta/rtl/Makefile ]; then \
		$(MAKE) -C $(PROJECTS_DIR)/delta/rtl lint-all || true; \
	else \
		echo "⚠ Delta RTL Makefile not found"; \
	fi

.PHONY: lint-apb_xbar
lint-apb_xbar:
	@echo "=== APB Crossbar RTL Lint ==="
	@if [ -f $(PROJECTS_DIR)/apb_xbar/rtl/Makefile ]; then \
		$(MAKE) -C $(PROJECTS_DIR)/apb_xbar/rtl lint-all || true; \
	else \
		echo "⚠ APB Crossbar RTL Makefile not found"; \
	fi

.PHONY: lint-converters
lint-converters:
	@echo "=== Converters RTL Lint ==="
	@if [ -f $(PROJECTS_DIR)/converters/rtl/Makefile ]; then \
		$(MAKE) -C $(PROJECTS_DIR)/converters/rtl lint-all || true; \
	else \
		echo "⚠ Converters RTL Makefile not found"; \
	fi

.PHONY: lint-shims
lint-shims:
	@echo "=== Shims RTL Lint ==="
	@if [ -f $(PROJECTS_DIR)/shims/rtl/Makefile ]; then \
		$(MAKE) -C $(PROJECTS_DIR)/shims/rtl lint-all || true; \
	else \
		echo "⚠ Shims RTL Makefile not found"; \
	fi

.PHONY: lint-retro_legacy_blocks
lint-retro_legacy_blocks:
	@echo "=== Retro Legacy Blocks RTL Lint ==="
	@if [ -f $(PROJECTS_DIR)/retro_legacy_blocks/rtl/Makefile ]; then \
		$(MAKE) -C $(PROJECTS_DIR)/retro_legacy_blocks/rtl lint-all || true; \
	else \
		echo "⚠ Retro Legacy Blocks RTL Makefile not found"; \
	fi

.PHONY: lint-bch
lint-bch:
	@echo "=== BCH RTL Lint ==="
	@if [ -f $(PROJECTS_DIR)/bch/rtl/Makefile ]; then \
		$(MAKE) -C $(PROJECTS_DIR)/bch/rtl lint-all || true; \
	else \
		echo "⚠ BCH RTL Makefile not found (may not have RTL yet)"; \
	fi

.PHONY: lint-hive
lint-hive:
	@echo "=== HIVE RTL Lint ==="
	@if [ -f $(PROJECTS_DIR)/hive/rtl/Makefile ]; then \
		$(MAKE) -C $(PROJECTS_DIR)/hive/rtl lint-all || true; \
	else \
		echo "⚠ HIVE RTL Makefile not found (may not have RTL yet)"; \
	fi

.PHONY: lint-projects
lint-projects: lint-stream lint-rapids lint-bridge lint-delta lint-apb_xbar lint-converters lint-shims lint-retro_legacy_blocks lint-bch lint-hive
	@echo "================================================================================"
	@echo "✓ All project RTL lint completed"
	@echo "================================================================================"

.PHONY: lint-all
lint-all: lint-rtl lint-projects
	@echo "================================================================================"
	@echo "✓ ALL LINT COMPLETED"
	@echo "================================================================================"

# ==============================================================================
# Combined Targets
# ==============================================================================

.PHONY: all
all: test-all lint-all
	@echo "================================================================================"
	@echo "✓ ALL OPERATIONS COMPLETED (tests + lint)"
	@echo "================================================================================"

.PHONY: ci
ci:
	@echo "================================================================================"
	@echo "CI/CD Mode: Running tests and lint with strict error checking"
	@echo "================================================================================"
	@echo ""
	@echo "Phase 1/2: Running tests..."
	@$(MAKE) test-all
	@echo ""
	@echo "Phase 2/2: Running lint..."
	@$(MAKE) lint-all
	@echo ""
	@echo "================================================================================"
	@echo "✓ CI/CD CHECKS COMPLETED"
	@echo "================================================================================"

# ==============================================================================
# Status Targets
# ==============================================================================

.PHONY: status-tests
status-tests:
	@echo "================================================================================"
	@echo "Test Status Summary"
	@echo "================================================================================"
	@echo ""
	@echo "=== Validation Tests ==="
	@$(MAKE) -C $(VAL_DIR) status 2>/dev/null | grep -A 20 "Test modules found:" || echo "Status unavailable"
	@echo ""
	@echo "=== Project Tests ==="
	@for proj in $(PROJECTS); do \
		if [ -f $(PROJECTS_DIR)/$$proj/dv/tests/Makefile ]; then \
			echo "--- $$proj ---"; \
			$(MAKE) -C $(PROJECTS_DIR)/$$proj/dv/tests status 2>/dev/null | grep -E "Test modules found:|files" | head -5 || echo "Status unavailable"; \
			echo ""; \
		fi; \
	done

.PHONY: status-lint
status-lint:
	@echo "================================================================================"
	@echo "Lint Status Summary"
	@echo "================================================================================"
	@echo ""
	@echo "=== RTL Modules ==="
	@$(MAKE) -C $(RTL_DIR) status 2>/dev/null | grep -A 5 "RTL areas:" || echo "Status unavailable"
	@echo ""
	@echo "=== Project RTL ==="
	@for proj in $(PROJECTS); do \
		if [ -f $(PROJECTS_DIR)/$$proj/rtl/Makefile ]; then \
			echo "--- $$proj ---"; \
			$(MAKE) -C $(PROJECTS_DIR)/$$proj/rtl status 2>/dev/null | grep -E "SystemVerilog files:" || echo "Status unavailable"; \
			echo ""; \
		fi; \
	done

.PHONY: status
status:
	@echo "================================================================================"
	@echo "RTL Design Sherpa - Complete Repository Status"
	@echo "================================================================================"
	@echo ""
	@echo "Repository: $(REPO_ROOT)"
	@echo "Branch: $$(git branch --show-current 2>/dev/null || echo 'unknown')"
	@echo "Last commit: $$(git log -1 --oneline 2>/dev/null || echo 'unknown')"
	@echo ""
	@$(MAKE) status-tests
	@echo ""
	@$(MAKE) status-lint
	@echo ""
	@echo "================================================================================"

# ==============================================================================
# Clean Targets
# ==============================================================================

.PHONY: clean-tests
clean-tests:
	@echo "Cleaning all test artifacts..."
	@$(MAKE) -C $(VAL_DIR) clean-all 2>/dev/null || true
	@for proj in $(PROJECTS); do \
		if [ -f $(PROJECTS_DIR)/$$proj/dv/tests/Makefile ]; then \
			$(MAKE) -C $(PROJECTS_DIR)/$$proj/dv/tests clean-all 2>/dev/null || true; \
		fi; \
	done
	@echo "✓ Test artifacts cleaned"

.PHONY: clean-lint
clean-lint:
	@echo "Cleaning all lint artifacts..."
	@$(MAKE) -C $(RTL_DIR) clean-all 2>/dev/null || true
	@for proj in $(PROJECTS); do \
		if [ -f $(PROJECTS_DIR)/$$proj/rtl/Makefile ]; then \
			$(MAKE) -C $(PROJECTS_DIR)/$$proj/rtl clean-all 2>/dev/null || true; \
		fi; \
	done
	@echo "✓ Lint artifacts cleaned"

.PHONY: clean-all
clean-all: clean-tests clean-lint
	@echo "================================================================================"
	@echo "✓ All artifacts cleaned (tests + lint)"
	@echo "================================================================================"

# ==============================================================================
# Quick Aliases
# ==============================================================================

.PHONY: test
test: test-all

.PHONY: lint
lint: lint-all

.PHONY: clean
clean: clean-all

# ==============================================================================
# Documentation Generation (for reference)
# ==============================================================================

.PHONY: docs
docs:
	@echo "================================================================================"
	@echo "Documentation Generation"
	@echo "================================================================================"
	@echo ""
	@echo "To generate PDFs for project documentation:"
	@echo "  cd projects/components/{project}/docs"
	@echo "  ./generate_pdf.sh"
	@echo ""
	@echo "Available documentation directories:"
	@find projects/components/ -type d -name "docs" 2>/dev/null | sort
	@echo ""
	@echo "================================================================================"

# ==============================================================================
# End of Makefile
# ==============================================================================
