# ==============================================================================
# Projects/Components - Master Makefile
# ==============================================================================
#
# PREREQUISITES:
#   Must be run with sourced environment:
#     source $REPO_ROOT/env_python
#     cd $REPO_ROOT/projects/components
#     make <target>
#
# Quick start:
#   make help           - Show all available targets
#   make test-all       - Run ALL component tests
#   make lint-all       - Run ALL component lint
#   make status         - Show status of all components
#
# ==============================================================================

# Force bash shell
SHELL := /bin/bash

# Check if REPO_ROOT is set (from env_python)
ifndef REPO_ROOT
$(error REPO_ROOT is not set. Please run: source $$REPO_ROOT/env_python)
endif

# Component list - only components with working dv/tests/Makefile
# To add a component: 1) create dv/tests/Makefile with run-all-* targets, 2) add to this list
COMPONENTS = stream rapids bridge apb_xbar converters retro_legacy_blocks

# Components that exist but don't have test Makefiles yet (for reference):
# - bch, delta, misc - have dv/tests dir but no Makefile

# Colors for output (if supported)
BOLD := $(shell tput bold 2>/dev/null)
RESET := $(shell tput sgr0 2>/dev/null)
GREEN := $(shell tput setaf 2 2>/dev/null)
YELLOW := $(shell tput setaf 3 2>/dev/null)
RED := $(shell tput setaf 1 2>/dev/null)

# Default target
.DEFAULT_GOAL := help

# ==============================================================================
# Help Target
# ==============================================================================

.PHONY: help
help:
	@echo "================================================================================"
	@echo "Projects/Components Master Makefile"
	@echo "================================================================================"
	@echo ""
	@echo "TEST TARGETS (run tests on all components):"
	@echo "  make test-all             Run tests for ALL components"
	@echo "  make test-stream          Run STREAM tests"
	@echo "  make test-rapids          Run RAPIDS tests"
	@echo "  make test-bridge          Run Bridge tests"
	@echo "  make test-apb_xbar        Run APB Crossbar tests"
	@echo "  make test-converters      Run Converters tests"
	@echo "  make test-retro_legacy_blocks  Run Retro Legacy Blocks tests"
	@echo ""
	@echo "REG_LEVEL TEST TARGETS (configurable test depth):"
	@echo "  GATE = Quick smoke (~5 min/component), FUNC = Default (~30 min/component), FULL = Comprehensive (~4 hr/component)"
	@echo ""
	@echo "  make test-all-{gate|func|full}         All components"
	@echo "  make test-{component}-{gate|func|full} Specific component"
	@echo "  Example: make test-stream-gate"
	@echo ""
	@echo "PARALLEL TEST TARGETS (48 workers per component):"
	@echo "  make test-all-parallel             All components, parallel"
	@echo "  make test-all-{gate|func|full}-parallel"
	@echo "  Example: make test-all-func-parallel"
	@echo ""
	@echo "LINT TARGETS (run lint on all component RTL):"
	@echo "  make lint-all             Lint ALL component RTL"
	@echo "  make lint-stream          Lint STREAM RTL"
	@echo "  make lint-rapids          Lint RAPIDS RTL"
	@echo "  make lint-bridge          Lint Bridge RTL"
	@echo "  make lint-apb_xbar        Lint APB Crossbar RTL"
	@echo "  make lint-converters      Lint Converters RTL"
	@echo "  make lint-retro_legacy_blocks  Lint Retro Legacy Blocks RTL"
	@echo ""
	@echo "STATUS TARGETS:"
	@echo "  make status               Show status of all components"
	@echo "  make status-tests         Show test status summary"
	@echo "  make status-lint          Show lint status summary"
	@echo ""
	@echo "CLEAN TARGETS:"
	@echo "  make clean-all            Clean ALL component artifacts"
	@echo "  make clean-tests          Clean all test artifacts"
	@echo "  make clean-lint           Clean all lint artifacts"
	@echo "  make clean-stream         Clean STREAM artifacts"
	@echo "  make clean-rapids         Clean RAPIDS artifacts"
	@echo "  # ... (per-component clean targets)"
	@echo ""
	@echo "COMBINED TARGETS:"
	@echo "  make all                  Run tests AND lint on all components"
	@echo "  make ci                   CI/CD mode: gate tests + lint"
	@echo ""
	@echo "QUICK SHORTCUTS (run gate/func/full on all components):"
	@echo "  make gate                 Quick smoke tests (parallel, ~5 min/component)"
	@echo "  make func                 Functional coverage (parallel, ~30 min/component)"
	@echo "  make full                 Comprehensive tests (parallel, ~4 hr/component)"
	@echo "  make gate-serial          GATE tests, serial execution"
	@echo "  make func-serial          FUNC tests, serial execution"
	@echo "  make full-serial          FULL tests, serial execution"
	@echo ""
	@echo "================================================================================"
	@echo "Prerequisites: source $(REPO_ROOT)/env_python"
	@echo "Current REPO_ROOT: $(REPO_ROOT)"
	@echo "Components: $(COMPONENTS)"
	@echo "================================================================================"

# ==============================================================================
# Test Targets - All Components
# ==============================================================================

.PHONY: test-all
test-all:
	@echo "$(BOLD)================================================================================$(RESET)"
	@echo "$(BOLD)Running Tests for ALL Components (FUNC level, serial)$(RESET)"
	@echo "$(BOLD)================================================================================$(RESET)"
	@for comp in $(COMPONENTS); do \
		echo ""; \
		echo "$(BOLD)$(GREEN)==> Testing $$comp$(RESET)"; \
		echo ""; \
		$(MAKE) -C $$comp/dv/tests run-all || exit 1; \
	done
	@echo ""
	@echo "$(BOLD)$(GREEN)✓ All component tests complete$(RESET)"

.PHONY: test-all-parallel
test-all-parallel:
	@echo "$(BOLD)================================================================================$(RESET)"
	@echo "$(BOLD)Running Tests for ALL Components (FUNC level, parallel)$(RESET)"
	@echo "$(BOLD)================================================================================$(RESET)"
	@for comp in $(COMPONENTS); do \
		echo ""; \
		echo "$(BOLD)$(GREEN)==> Testing $$comp (parallel - 48 workers)$(RESET)"; \
		echo ""; \
		$(MAKE) -C $$comp/dv/tests run-all-parallel || exit 1; \
	done
	@echo ""
	@echo "$(BOLD)$(GREEN)✓ All component tests complete$(RESET)"

# ==============================================================================
# Test Targets - REG_LEVEL Variants (All Components)
# ==============================================================================

.PHONY: test-all-gate
test-all-gate:
	@echo "$(BOLD)================================================================================$(RESET)"
	@echo "$(BOLD)Running Tests for ALL Components (GATE level - quick smoke)$(RESET)"
	@echo "$(BOLD)================================================================================$(RESET)"
	@for comp in $(COMPONENTS); do \
		echo ""; \
		echo "$(BOLD)$(GREEN)==> Testing $$comp (GATE level)$(RESET)"; \
		echo ""; \
		$(MAKE) -C $$comp/dv/tests run-all-gate || exit 1; \
	done
	@echo ""
	@echo "$(BOLD)$(GREEN)✓ All component gate tests complete$(RESET)"

.PHONY: test-all-func
test-all-func:
	@echo "$(BOLD)================================================================================$(RESET)"
	@echo "$(BOLD)Running Tests for ALL Components (FUNC level - functional coverage)$(RESET)"
	@echo "$(BOLD)================================================================================$(RESET)"
	@for comp in $(COMPONENTS); do \
		echo ""; \
		echo "$(BOLD)$(GREEN)==> Testing $$comp (FUNC level)$(RESET)"; \
		echo ""; \
		$(MAKE) -C $$comp/dv/tests run-all-func || exit 1; \
	done
	@echo ""
	@echo "$(BOLD)$(GREEN)✓ All component functional tests complete$(RESET)"

.PHONY: test-all-full
test-all-full:
	@echo "$(BOLD)================================================================================$(RESET)"
	@echo "$(BOLD)Running Tests for ALL Components (FULL level - comprehensive)$(RESET)"
	@echo "$(BOLD)================================================================================$(RESET)"
	@for comp in $(COMPONENTS); do \
		echo ""; \
		echo "$(BOLD)$(GREEN)==> Testing $$comp (FULL level)$(RESET)"; \
		echo ""; \
		$(MAKE) -C $$comp/dv/tests run-all-full || exit 1; \
	done
	@echo ""
	@echo "$(BOLD)$(GREEN)✓ All component comprehensive tests complete$(RESET)"

# Parallel versions
.PHONY: test-all-gate-parallel
test-all-gate-parallel:
	@echo "$(BOLD)================================================================================$(RESET)"
	@echo "$(BOLD)Running Tests for ALL Components (GATE level, parallel)$(RESET)"
	@echo "$(BOLD)================================================================================$(RESET)"
	@for comp in $(COMPONENTS); do \
		echo ""; \
		echo "$(BOLD)$(GREEN)==> Testing $$comp (GATE, 48 workers)$(RESET)"; \
		echo ""; \
		$(MAKE) -C $$comp/dv/tests run-all-gate-parallel || exit 1; \
	done
	@echo ""
	@echo "$(BOLD)$(GREEN)✓ All component gate tests complete$(RESET)"

.PHONY: test-all-func-parallel
test-all-func-parallel:
	@echo "$(BOLD)================================================================================$(RESET)"
	@echo "$(BOLD)Running Tests for ALL Components (FUNC level, parallel)$(RESET)"
	@echo "$(BOLD)================================================================================$(RESET)"
	@for comp in $(COMPONENTS); do \
		echo ""; \
		echo "$(BOLD)$(GREEN)==> Testing $$comp (FUNC, 48 workers)$(RESET)"; \
		echo ""; \
		$(MAKE) -C $$comp/dv/tests run-all-func-parallel || exit 1; \
	done
	@echo ""
	@echo "$(BOLD)$(GREEN)✓ All component functional tests complete$(RESET)"

.PHONY: test-all-full-parallel
test-all-full-parallel:
	@echo "$(BOLD)================================================================================$(RESET)"
	@echo "$(BOLD)Running Tests for ALL Components (FULL level, parallel)$(RESET)"
	@echo "$(BOLD)================================================================================$(RESET)"
	@for comp in $(COMPONENTS); do \
		echo ""; \
		echo "$(BOLD)$(GREEN)==> Testing $$comp (FULL, 48 workers)$(RESET)"; \
		echo ""; \
		$(MAKE) -C $$comp/dv/tests run-all-full-parallel || exit 1; \
	done
	@echo ""
	@echo "$(BOLD)$(GREEN)✓ All component comprehensive tests complete$(RESET)"

# ==============================================================================
# Test Targets - Individual Components
# ==============================================================================

# Template for individual component test targets
define COMPONENT_TEST_TARGETS
.PHONY: test-$(1)
test-$(1):
	@echo "$(BOLD)Running $(1) tests (FUNC level)$(RESET)"
	@$(MAKE) -C $(1)/dv/tests run-all

.PHONY: test-$(1)-gate
test-$(1)-gate:
	@echo "$(BOLD)Running $(1) tests (GATE level)$(RESET)"
	@$(MAKE) -C $(1)/dv/tests run-all-gate

.PHONY: test-$(1)-func
test-$(1)-func:
	@echo "$(BOLD)Running $(1) tests (FUNC level)$(RESET)"
	@$(MAKE) -C $(1)/dv/tests run-all-func

.PHONY: test-$(1)-full
test-$(1)-full:
	@echo "$(BOLD)Running $(1) tests (FULL level)$(RESET)"
	@$(MAKE) -C $(1)/dv/tests run-all-full

.PHONY: test-$(1)-parallel
test-$(1)-parallel:
	@echo "$(BOLD)Running $(1) tests (FUNC level, parallel)$(RESET)"
	@$(MAKE) -C $(1)/dv/tests run-all-parallel

.PHONY: test-$(1)-gate-parallel
test-$(1)-gate-parallel:
	@echo "$(BOLD)Running $(1) tests (GATE level, parallel)$(RESET)"
	@$(MAKE) -C $(1)/dv/tests run-all-gate-parallel

.PHONY: test-$(1)-func-parallel
test-$(1)-func-parallel:
	@echo "$(BOLD)Running $(1) tests (FUNC level, parallel)$(RESET)"
	@$(MAKE) -C $(1)/dv/tests run-all-func-parallel

.PHONY: test-$(1)-full-parallel
test-$(1)-full-parallel:
	@echo "$(BOLD)Running $(1) tests (FULL level, parallel)$(RESET)"
	@$(MAKE) -C $(1)/dv/tests run-all-full-parallel
endef

# Generate targets for each component
$(foreach comp,$(COMPONENTS),$(eval $(call COMPONENT_TEST_TARGETS,$(comp))))

# ==============================================================================
# Lint Targets - All Components
# ==============================================================================

.PHONY: lint-all
lint-all:
	@echo "$(BOLD)================================================================================$(RESET)"
	@echo "$(BOLD)Running Lint for ALL Component RTL$(RESET)"
	@echo "$(BOLD)================================================================================$(RESET)"
	@for comp in $(COMPONENTS); do \
		echo ""; \
		echo "$(BOLD)$(YELLOW)==> Linting $$comp RTL$(RESET)"; \
		echo ""; \
		$(MAKE) -C $$comp/rtl lint-all || exit 1; \
	done
	@echo ""
	@echo "$(BOLD)$(GREEN)✓ All component lint complete$(RESET)"

# ==============================================================================
# Lint Targets - Individual Components
# ==============================================================================

# Template for individual component lint targets
define COMPONENT_LINT_TARGETS
.PHONY: lint-$(1)
lint-$(1):
	@echo "$(BOLD)Linting $(1) RTL$(RESET)"
	@$(MAKE) -C $(1)/rtl lint-all
endef

# Generate targets for each component
$(foreach comp,$(COMPONENTS),$(eval $(call COMPONENT_LINT_TARGETS,$(comp))))

# ==============================================================================
# Status Targets
# ==============================================================================

.PHONY: status
status:
	@echo "$(BOLD)================================================================================$(RESET)"
	@echo "$(BOLD)Projects/Components Status$(RESET)"
	@echo "$(BOLD)================================================================================$(RESET)"
	@echo ""
	@echo "$(BOLD)Components:$(RESET) $(COMPONENTS)"
	@echo ""
	@for comp in $(COMPONENTS); do \
		echo "$(BOLD)==> $$comp$(RESET)"; \
		echo "  Location: $(REPO_ROOT)/projects/components/$$comp"; \
		echo -n "  RTL files:   "; find $$comp/rtl -name "*.sv" 2>/dev/null | wc -l; \
		echo -n "  Test files:  "; find $$comp/dv/tests -name "test_*.py" 2>/dev/null | wc -l; \
		echo -n "  Lint status: "; \
		if [ -d "$$comp/rtl/lint_reports" ]; then \
			echo "$(GREEN)Reports exist$(RESET)"; \
		else \
			echo "$(YELLOW)Not run$(RESET)"; \
		fi; \
		echo ""; \
	done
	@echo "Environment:"
	@echo "  REPO_ROOT: $(REPO_ROOT)"
	@echo "================================================================================"

.PHONY: status-tests
status-tests:
	@echo "$(BOLD)================================================================================$(RESET)"
	@echo "$(BOLD)Component Test Status$(RESET)"
	@echo "$(BOLD)================================================================================$(RESET)"
	@for comp in $(COMPONENTS); do \
		echo ""; \
		echo "$(BOLD)$$comp:$(RESET)"; \
		$(MAKE) -C $$comp/dv/tests status 2>/dev/null || echo "  No test status available"; \
	done
	@echo "================================================================================"

.PHONY: status-lint
status-lint:
	@echo "$(BOLD)================================================================================$(RESET)"
	@echo "$(BOLD)Component Lint Status$(RESET)"
	@echo "$(BOLD)================================================================================$(RESET)"
	@for comp in $(COMPONENTS); do \
		echo ""; \
		echo "$(BOLD)$$comp:$(RESET)"; \
		$(MAKE) -C $$comp/rtl status 2>/dev/null || echo "  No lint status available"; \
	done
	@echo "================================================================================"

# ==============================================================================
# Clean Targets
# ==============================================================================

.PHONY: clean-all
clean-all: clean-tests clean-lint
	@echo "$(BOLD)$(GREEN)✓ All component artifacts cleaned$(RESET)"

.PHONY: clean-tests
clean-tests:
	@echo "$(BOLD)Cleaning all component test artifacts...$(RESET)"
	@for comp in $(COMPONENTS); do \
		echo "  Cleaning $$comp tests..."; \
		$(MAKE) -C $$comp/dv/tests clean-all 2>/dev/null || true; \
	done
	@echo "$(BOLD)$(GREEN)✓ Test artifacts cleaned$(RESET)"

.PHONY: clean-lint
clean-lint:
	@echo "$(BOLD)Cleaning all component lint artifacts...$(RESET)"
	@for comp in $(COMPONENTS); do \
		echo "  Cleaning $$comp lint..."; \
		$(MAKE) -C $$comp/rtl clean-all 2>/dev/null || true; \
	done
	@echo "$(BOLD)$(GREEN)✓ Lint artifacts cleaned$(RESET)"

# Template for individual component clean targets
define COMPONENT_CLEAN_TARGETS
.PHONY: clean-$(1)
clean-$(1):
	@echo "$(BOLD)Cleaning $(1) artifacts...$(RESET)"
	@$(MAKE) -C $(1)/dv/tests clean-all 2>/dev/null || true
	@$(MAKE) -C $(1)/rtl clean-all 2>/dev/null || true
	@echo "$(BOLD)$(GREEN)✓ $(1) artifacts cleaned$(RESET)"
endef

# Generate targets for each component
$(foreach comp,$(COMPONENTS),$(eval $(call COMPONENT_CLEAN_TARGETS,$(comp))))

# ==============================================================================
# Combined Targets
# ==============================================================================

.PHONY: all
all: test-all lint-all
	@echo "$(BOLD)$(GREEN)✓ All component tests and lint complete$(RESET)"

.PHONY: ci
ci: test-all-gate-parallel lint-all
	@echo "$(BOLD)$(GREEN)✓ CI validation complete (gate tests + lint)$(RESET)"

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
# Shortcut Targets (gate/func/full)
# ==============================================================================
# These are convenient shortcuts for running all component tests at each level

.PHONY: gate
gate: test-all-gate-parallel
	@echo "$(BOLD)$(GREEN)✓ GATE tests complete (all components)$(RESET)"

.PHONY: func
func: test-all-func-parallel
	@echo "$(BOLD)$(GREEN)✓ FUNC tests complete (all components)$(RESET)"

.PHONY: full
full: test-all-full-parallel
	@echo "$(BOLD)$(GREEN)✓ FULL tests complete (all components)$(RESET)"

# Serial versions (if parallel causes issues)
.PHONY: gate-serial
gate-serial: test-all-gate
	@echo "$(BOLD)$(GREEN)✓ GATE tests complete (serial)$(RESET)"

.PHONY: func-serial
func-serial: test-all-func
	@echo "$(BOLD)$(GREEN)✓ FUNC tests complete (serial)$(RESET)"

.PHONY: full-serial
full-serial: test-all-full
	@echo "$(BOLD)$(GREEN)✓ FULL tests complete (serial)$(RESET)"

# ==============================================================================
# End of Makefile
# ==============================================================================
