# ==============================================================================
# RTL Design Sherpa - Master Makefile
# ==============================================================================
#
# Bootstrap (no env_python needed):
#   make setup          - Full setup from scratch (apt + venv + formal tools)
#   make setup-no-sudo  - Setup without apt (venv + formal tools only)
#   make setup-hooks    - Install git hooks (SV declaration order check)
#   make install        - Create venv and install Python dependencies only
#   make doctor         - Check that all required tools are available
#   make count          - LOC / file counts for RTL, tests, framework
#
# After setup:
#   source env_python   - Activate venv and set REPO_ROOT
#   make help           - Show all available targets
#   make test-all       - Run all tests (validation + projects)
#   make lint-all       - Run all lint (RTL + projects)
#   make status         - Show complete repository status
#   make clean-all      - Clean all test and lint artifacts
#
# ==============================================================================

# Force bash shell
SHELL := /bin/bash

# Repo root for bootstrap targets (works without env_python)
MAKEFILE_DIR := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))

# ==============================================================================
# Bootstrap Targets (no env_python required)
# ==============================================================================

.PHONY: install
install:
	@echo "================================================================================"
	@echo "Installing RTL Design Sherpa Python environment"
	@echo "================================================================================"
	@if [ ! -d "$(MAKEFILE_DIR)venv" ]; then \
		echo "Creating virtual environment..."; \
		python3 -m venv "$(MAKEFILE_DIR)venv"; \
	else \
		echo "Virtual environment already exists at $(MAKEFILE_DIR)venv"; \
	fi
	@echo "Upgrading pip..."
	@"$(MAKEFILE_DIR)venv/bin/pip" install --upgrade pip
	@echo "Installing requirements..."
	@"$(MAKEFILE_DIR)venv/bin/pip" install -r "$(MAKEFILE_DIR)requirements.txt"
	@echo ""
	@echo "================================================================================"
	@echo "Done. Next steps:"
	@echo "  source env_python      # activate venv + set paths"
	@echo "  make doctor            # verify all tools"
	@echo "  make test-all          # run full test suite"
	@echo "================================================================================"

.PHONY: doctor
doctor:
	@echo "================================================================================"
	@echo "RTL Design Sherpa - Tool Check"
	@echo "================================================================================"
	@echo ""
	@printf "  %-22s " "Python 3:" && (python3 --version 2>/dev/null || echo "MISSING")
	@printf "  %-22s " "Verilator:" && (verilator --version 2>/dev/null | head -1 || echo "MISSING")
	@printf "  %-22s " "Verible:" && (verible-verilog-lint --version 2>/dev/null | head -1 || echo "MISSING (add to PATH)")
	@printf "  %-22s " "GTKWave:" && (which gtkwave 2>/dev/null && echo "OK" || echo "MISSING (optional)")
	@printf "  %-22s " "Yosys:" && (yosys --version 2>/dev/null | head -1 || echo "MISSING (optional)")
	@printf "  %-22s " "SymbiYosys:" && (sby --version 2>/dev/null | head -1 || echo "MISSING (run: bash bin/install_formal_tools.sh)")
	@printf "  %-22s " "Boolector:" && (which boolector >/dev/null 2>&1 && echo "OK" || echo "MISSING (formal solver)")
	@printf "  %-22s " "z3:" && (which z3 >/dev/null 2>&1 && echo "OK" || echo "MISSING (optional solver)")
	@printf "  %-22s " "Venv:" && (test -f "$(MAKEFILE_DIR)venv/bin/python3" && echo "OK ($(MAKEFILE_DIR)venv)" || echo "MISSING (run: make install)")
	@printf "  %-22s " "CocoTB:" && ("$(MAKEFILE_DIR)venv/bin/python3" -c "import cocotb; print(cocotb.__version__)" 2>/dev/null || echo "MISSING (run: make install)")
	@printf "  %-22s " "REPO_ROOT:" && (test -n "$$REPO_ROOT" && echo "$$REPO_ROOT" || echo "NOT SET (run: source env_python)")
	@printf "  %-22s " "Git hooks:" && (test -x .git/hooks/pre-commit && echo "OK (pre-commit installed)" || echo "NOT INSTALLED (run: make setup-hooks)")
	@echo ""
	@echo "================================================================================"

.PHONY: count
count:
	@echo "================================================================================"
	@echo "RTL Design Sherpa - Codebase Stats"
	@echo "================================================================================"
	@echo ""
	@printf "  %-35s " "RTL (*.sv):" && find "$(MAKEFILE_DIR)rtl" -name "*.sv" 2>/dev/null | wc -l | xargs printf "%s files, " && find "$(MAKEFILE_DIR)rtl" -name "*.sv" -exec cat {} + 2>/dev/null | wc -l | xargs printf "%s lines\n"
	@printf "  %-35s " "Project RTL (*.sv):" && find "$(MAKEFILE_DIR)projects" -name "*.sv" 2>/dev/null | wc -l | xargs printf "%s files, " && find "$(MAKEFILE_DIR)projects" -name "*.sv" -exec cat {} + 2>/dev/null | wc -l | xargs printf "%s lines\n"
	@printf "  %-35s " "Tests (test_*.py):" && find "$(MAKEFILE_DIR)val" "$(MAKEFILE_DIR)projects" -name "test_*.py" 2>/dev/null | wc -l | xargs printf "%s files, " && find "$(MAKEFILE_DIR)val" "$(MAKEFILE_DIR)projects" -name "test_*.py" -exec cat {} + 2>/dev/null | wc -l | xargs printf "%s lines\n"
	@printf "  %-35s " "CocoTBFramework (*.py):" && find "$(MAKEFILE_DIR)bin/TBClasses" -name "*.py" 2>/dev/null | wc -l | xargs printf "%s files, " && find "$(MAKEFILE_DIR)bin/TBClasses" -name "*.py" -exec cat {} + 2>/dev/null | wc -l | xargs printf "%s lines\n"
	@printf "  %-35s " "Documentation (*.md):" && find "$(MAKEFILE_DIR)docs" -name "*.md" 2>/dev/null | wc -l | xargs printf "%s files\n"
	@echo ""
	@echo "================================================================================"

# ==============================================================================
# Environment Check (required for all targets below this point)
# ==============================================================================

.PHONY: setup
setup:
	@bash bin/setup_from_scratch.sh

.PHONY: setup-no-sudo
setup-no-sudo:
	@bash bin/setup_from_scratch.sh --skip-apt

.PHONY: setup-hooks
setup-hooks: ## Install git hooks (declaration-order check on .sv commits)
	@echo "================================================================================"
	@echo "Installing git hooks"
	@echo "================================================================================"
	@mkdir -p .git/hooks
	@for hook in tools/hooks/*; do \
		name=$$(basename "$$hook"); \
		cp "$$hook" ".git/hooks/$$name"; \
		chmod +x ".git/hooks/$$name"; \
		echo "  Installed $$name"; \
	done
	@echo ""
	@echo "Hooks installed. They run automatically on each commit."
	@echo "Bypass (emergency): git commit --no-verify"
	@echo "================================================================================"

# Only enforce REPO_ROOT for non-bootstrap targets
BOOTSTRAP_TARGETS := install doctor count setup setup-no-sudo setup-hooks
ifneq ($(filter-out $(BOOTSTRAP_TARGETS),$(MAKECMDGOALS)),)
ifndef REPO_ROOT
$(error REPO_ROOT is not set. Please run: source env_python)
endif
endif

# Also require REPO_ROOT when no target is specified (default = help)
ifeq ($(MAKECMDGOALS),)
ifndef REPO_ROOT
$(error REPO_ROOT is not set. Run 'make install' or 'source env_python && make help')
endif
endif

# Directories
VAL_DIR = val
RTL_DIR = rtl
PROJECTS_DIR = projects/components

# Project list
PROJECTS = stream rapids bridge delta apb_xbar converters shims retro_legacy_blocks bch hive

# Include generated test targets from test_environments.toml
# Regenerate: python3 bin/generate_test_targets.py
-include test_targets.mk

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
	@echo "UNIFIED REG_LEVEL TARGETS (ALL environments - val/ + projects/):"
	@echo "  GATE = Quick smoke tests, FUNC = Functional coverage, FULL = Comprehensive"
	@echo ""
	@echo "  make gate                 GATE + results table (serial across envs)"
	@echo "  make func                 FUNC + results table (serial across envs)"
	@echo "  make full                 FULL + results table (serial across envs)"
	@echo "  make gate-parallel        GATE - ALL environments concurrently"
	@echo "  make func-parallel        FUNC - ALL environments concurrently"
	@echo "  make full-parallel        FULL - ALL environments concurrently"
	@echo "  make gate-serial          GATE across ALL environments (serial, no xdist)"
	@echo "  make func-serial          FUNC across ALL environments (serial, no xdist)"
	@echo "  make full-serial          FULL across ALL environments (serial, no xdist)"
	@echo ""
	@echo "PER-SUBSYSTEM REG_LEVEL TARGETS (parallel):"
	@echo "  COMMON:  make run-common-{gate|func|full}-parallel"
	@echo "  AMBA:    make run-amba-{gate|func|full}-parallel"
	@echo "  RTL ALL: make run-rtl-all-{gate|func|full}-parallel"
	@echo ""
	@echo "GENERATED TEST TARGETS (from test_environments.toml):"
	@echo "  make help-envs                Show all generated test + coverage targets"
	@echo "  make test-{env}               Run FUNC parallel (e.g. test-val-common, test-stream)"
	@echo "  make test-{env}-{gate|func|full}          Per-level"
	@echo "  make test-{env}-{level}-waves              With waveforms"
	@echo "  make test-{env}-{level}-serial             Sequential"
	@echo "  make test-all-{gate|func|full}             All environments"
	@echo "  make coverage-{env}           Per-component coverage"
	@echo "  make coverage-all             All components"
	@echo "  make coverage-unified         Cross-component dashboard"
	@echo ""
	@echo "FORMAL VERIFICATION:"
	@echo "  make formal                  Run all formal proofs"
	@echo "  make formal-common           Building blocks (arbiter, counter, FIFO)"
	@echo "  make formal-quick            Quick proof (counter_bin only, ~seconds)"
	@echo "  make formal-check-tools      Check sby/boolector/z3 installed"
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
	@echo "COMBINED TARGETS (tests + lint at each level):"
	@echo "  make all-gate             GATE tests + lint (quick checkin)"
	@echo "  make all-func             FUNC tests + lint (functional coverage)"
	@echo "  make all-full             FULL tests + lint (comprehensive)"
	@echo "  make all-full-coverage    FULL tests + coverage + lint + reports (maximal)"
	@echo "  make all                  Alias for all-func"
	@echo "  make ci                   Alias for all-gate (commit gate)"
	@echo ""
	@echo "RESULTS AGGREGATION:"
	@echo "  make results              Aggregate test results (rich table)"
	@echo "  make results-gate         Run GATE tests and show results table"
	@echo "  make results-func         Run FUNC tests and show results table"
	@echo "  make results-full         Run FULL tests and show results table"
	@echo "  make results-rapids       Run RAPIDS tests and show results table"
	@echo "  make results-stream       Run STREAM tests and show results table"
	@echo "  make results-val          Run val/ tests and show results table"
	@echo "  make results-md           Export results table as markdown"
	@echo ""
	@echo "STATUS TARGETS:"
	@echo "  make status               Show complete repository status"
	@echo "  make status-tests         Show test status summary"
	@echo "  make status-lint          Show lint status summary"
	@echo ""
	@echo "CLEAN TARGETS:
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
# Test Targets - Projects (legacy aliases → generated targets in test_targets.mk)
# ==============================================================================
# Per-project test targets are now generated from test_environments.toml.
# See: make help-envs
#
# These legacy aliases remain for backward compatibility with names that
# use underscores (the generated targets use hyphens).

.PHONY: test-delta
test-delta:
	@echo "=== Delta Project Tests ==="
	@if [ -f $(PROJECTS_DIR)/delta/dv/tests/Makefile ]; then \
		$(MAKE) -C $(PROJECTS_DIR)/delta/dv/tests run-all || true; \
	else \
		echo "Delta test Makefile not found (may not have tests yet)"; \
	fi

.PHONY: test-apb_xbar
test-apb_xbar: test-apb-xbar

.PHONY: test-retro_legacy_blocks
test-retro_legacy_blocks: test-retro-legacy

.PHONY: test-bch
test-bch:
	@echo "=== BCH Project Tests ==="
	@if [ -f $(PROJECTS_DIR)/bch/dv/tests/Makefile ]; then \
		$(MAKE) -C $(PROJECTS_DIR)/bch/dv/tests run-all || true; \
	else \
		echo "BCH test Makefile not found (may not have tests yet)"; \
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
# Unified REG_LEVEL Targets - ALL Environments (val/ + projects/components/)
# ==============================================================================
# These run gate/func/full across the ENTIRE repo: val/common, val/amba,
# val/integ_common, val/integ_amba, and all projects/components.
# Use these as commit gates.

.PHONY: gate
gate: results-gate

.PHONY: func
func: results-func

.PHONY: full
full: results-full

# Parallel versions (run ALL environments concurrently)
.PHONY: gate-parallel
gate-parallel: results-gate-parallel

.PHONY: func-parallel
func-parallel: results-func-parallel

.PHONY: full-parallel
full-parallel: results-full-parallel

# Serial versions (if parallel causes resource contention)
.PHONY: gate-serial
gate-serial:
	@echo "================================================================================"
	@echo "GATE (serial) - Quick Smoke Tests (ALL environments)"
	@echo "================================================================================"
	@$(MAKE) -C $(VAL_DIR)/common run-all-gate
	@$(MAKE) -C $(VAL_DIR)/amba run-all-gate
	@$(MAKE) -C $(VAL_DIR)/integ_common run-all 2>/dev/null || true
	@$(MAKE) -C $(VAL_DIR)/integ_amba run-all 2>/dev/null || true
	@$(MAKE) -C $(PROJECTS_DIR) test-all-gate
	@echo "================================================================================"
	@echo "GATE (serial) COMPLETE"
	@echo "================================================================================"

.PHONY: func-serial
func-serial:
	@echo "================================================================================"
	@echo "FUNC (serial) - Functional Coverage Tests (ALL environments)"
	@echo "================================================================================"
	@$(MAKE) -C $(VAL_DIR)/common run-all-func
	@$(MAKE) -C $(VAL_DIR)/amba run-all-func
	@$(MAKE) -C $(VAL_DIR)/integ_common run-all 2>/dev/null || true
	@$(MAKE) -C $(VAL_DIR)/integ_amba run-all 2>/dev/null || true
	@$(MAKE) -C $(PROJECTS_DIR) test-all-func
	@echo "================================================================================"
	@echo "FUNC (serial) COMPLETE"
	@echo "================================================================================"

.PHONY: full-serial
full-serial:
	@echo "================================================================================"
	@echo "FULL (serial) - Comprehensive Tests (ALL environments)"
	@echo "================================================================================"
	@$(MAKE) -C $(VAL_DIR)/common run-all-full
	@$(MAKE) -C $(VAL_DIR)/amba run-all-full
	@$(MAKE) -C $(VAL_DIR)/integ_common run-all 2>/dev/null || true
	@$(MAKE) -C $(VAL_DIR)/integ_amba run-all 2>/dev/null || true
	@$(MAKE) -C $(PROJECTS_DIR) test-all-full
	@echo "================================================================================"
	@echo "FULL (serial) COMPLETE"
	@echo "================================================================================"

# ==============================================================================
# Coverage Targets - ALL Environments
# ==============================================================================
# Coverage collection and reporting. Currently supported by STREAM, RAPIDS, Bridge, and Converters.
# Other components will be added as coverage infrastructure is built out.

.PHONY: coverage
coverage:
	@echo "================================================================================"
	@echo "Running Tests with Coverage (all environments that support it)"
	@echo "================================================================================"
	@echo ""
	@echo "Phase 1: STREAM coverage..."
	@if [ -f $(PROJECTS_DIR)/stream/dv/tests/Makefile ]; then \
		$(MAKE) -C $(PROJECTS_DIR)/stream/dv/tests fresh-coverage || true; \
	else \
		echo "  STREAM coverage Makefile not found - skipping"; \
	fi
	@echo ""
	@echo "Phase 2: RAPIDS coverage..."
	@if [ -f $(PROJECTS_DIR)/rapids/dv/tests/Makefile ]; then \
		$(MAKE) -C $(PROJECTS_DIR)/rapids/dv/tests coverage-full-report || true; \
	else \
		echo "  RAPIDS coverage Makefile not found - skipping"; \
	fi
	@echo ""
	@echo "Phase 3: Bridge coverage..."
	@if [ -f $(PROJECTS_DIR)/bridge/dv/tests/Makefile ]; then \
		$(MAKE) -C $(PROJECTS_DIR)/bridge/dv/tests fresh-coverage || true; \
	else \
		echo "  Bridge coverage Makefile not found - skipping"; \
	fi
	@echo ""
	@echo "Phase 4: Converters coverage..."
	@if [ -f $(PROJECTS_DIR)/converters/dv/tests/Makefile ]; then \
		$(MAKE) -C $(PROJECTS_DIR)/converters/dv/tests fresh-coverage || true; \
	else \
		echo "  Converters coverage Makefile not found - skipping"; \
	fi
	@echo ""
	@echo "================================================================================"
	@echo "Coverage collection complete"
	@echo "================================================================================"

.PHONY: coverage-report
coverage-report:
	@echo "================================================================================"
	@echo "Generating Coverage Reports"
	@echo "================================================================================"
	@echo ""
	@echo "STREAM coverage report:"
	@if [ -f $(PROJECTS_DIR)/stream/dv/tests/Makefile ]; then \
		$(MAKE) -C $(PROJECTS_DIR)/stream/dv/tests coverage-report || true; \
	else \
		echo "  Not available"; \
	fi
	@echo ""
	@echo "RAPIDS coverage report:"
	@if [ -f $(PROJECTS_DIR)/rapids/dv/tests/Makefile ]; then \
		$(MAKE) -C $(PROJECTS_DIR)/rapids/dv/tests coverage-report || true; \
	else \
		echo "  Not available"; \
	fi
	@echo ""
	@echo "Bridge coverage report:"
	@if [ -f $(PROJECTS_DIR)/bridge/dv/tests/Makefile ]; then \
		$(MAKE) -C $(PROJECTS_DIR)/bridge/dv/tests coverage-report || true; \
	else \
		echo "  Not available"; \
	fi
	@echo ""
	@echo "Converters coverage report:"
	@if [ -f $(PROJECTS_DIR)/converters/dv/tests/Makefile ]; then \
		$(MAKE) -C $(PROJECTS_DIR)/converters/dv/tests coverage-report || true; \
	else \
		echo "  Not available"; \
	fi
	@echo ""
	@echo "================================================================================"
	@echo "Coverage reports generated"
	@echo "================================================================================"

.PHONY: coverage-unified
coverage-unified:
	@echo "Generating unified cross-component coverage report..."
	python3 bin/cov_utils/unified_coverage_report.py --output coverage_unified_report.md --json coverage_unified_report.json
	@echo "Unified coverage report generated"

.PHONY: clean-coverage
clean-coverage:
	@echo "Cleaning all coverage artifacts..."
	@for proj in $(PROJECTS); do \
		if [ -f $(PROJECTS_DIR)/$$proj/dv/tests/Makefile ]; then \
			$(MAKE) -C $(PROJECTS_DIR)/$$proj/dv/tests clean-coverage 2>/dev/null || true; \
		fi; \
	done
	@rm -rf val/common/coverage_data val/amba/coverage_data
	@rm -f coverage_unified_report.md coverage_unified_report.json
	@echo "Coverage artifacts cleaned"

# Per-component coverage targets are now generated in test_targets.mk.
# See: make help-envs

# ==============================================================================
# Formal Verification Targets
# ==============================================================================
# Requires SymbiYosys + Boolector. Install: bash bin/install_formal_tools.sh

.PHONY: formal
formal:
	@$(MAKE) -C formal formal

.PHONY: formal-common
formal-common:
	@$(MAKE) -C formal formal-common

.PHONY: formal-bridge
formal-bridge:
	@$(MAKE) -C formal formal-bridge

.PHONY: formal-quick
formal-quick:
	@$(MAKE) -C formal formal-quick

.PHONY: formal-check-tools
formal-check-tools:
	@$(MAKE) -C formal check-tools

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
# Combined Targets (tests + lint at each level)
# ==============================================================================

# all-gate: Quick checkin gate (GATE tests + lint)
# Note: gate (results-gate) exits non-zero on test failures; run lint regardless.
.PHONY: all-gate
all-gate:
	@echo "================================================================================"
	@echo "ALL-GATE: GATE tests + lint (quick checkin)"
	@echo "================================================================================"
	@$(MAKE) gate || true
	@$(MAKE) lint-all
	@echo "================================================================================"
	@echo "ALL-GATE COMPLETE"
	@echo "================================================================================"

# all-func: Functional coverage (FUNC tests + lint)
.PHONY: all-func
all-func:
	@echo "================================================================================"
	@echo "ALL-FUNC: FUNC tests + lint (functional coverage)"
	@echo "================================================================================"
	@$(MAKE) func || true
	@$(MAKE) lint-all
	@echo "================================================================================"
	@echo "ALL-FUNC COMPLETE"
	@echo "================================================================================"

# all-full: Comprehensive (FULL tests + lint)
.PHONY: all-full
all-full:
	@echo "================================================================================"
	@echo "ALL-FULL: FULL tests + lint (comprehensive)"
	@echo "================================================================================"
	@$(MAKE) full || true
	@$(MAKE) lint-all
	@echo "================================================================================"
	@echo "ALL-FULL COMPLETE"
	@echo "================================================================================"

# all-full-coverage: Maximal analysis (FULL tests + coverage + lint + reports)
.PHONY: all-full-coverage
all-full-coverage:
	@echo "================================================================================"
	@echo "ALL-FULL-COVERAGE: FULL tests + coverage collection + lint + reports"
	@echo "================================================================================"
	@echo ""
	@echo "Phase 1/4: Running FULL tests (all environments)..."
	@$(MAKE) full
	@echo ""
	@echo "Phase 2/4: Running coverage collection..."
	@$(MAKE) coverage
	@echo ""
	@echo "Phase 3/4: Running lint..."
	@$(MAKE) lint-all
	@echo ""
	@echo "Phase 4/4: Generating coverage reports..."
	@$(MAKE) coverage-report
	@echo ""
	@echo "================================================================================"
	@echo "ALL-FULL-COVERAGE COMPLETE - Tests, coverage, lint, and reports all done"
	@echo "================================================================================"

# Legacy 'all' alias - same as all-func
.PHONY: all
all: all-func

# ci: Quick commit gate (same as all-gate)
.PHONY: ci
ci: all-gate

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
# Results Aggregation Targets
# ==============================================================================
# Run tests and display results in a rich table. Uses bin/aggregate_test_results.py.
# Results are cached as JUnit XML in test_results/.

AGGREGATE = python3 bin/aggregate_test_results.py
RESULTS_DIR = test_results

# Display existing results (no test run)
.PHONY: results
results:
	@$(AGGREGATE) --results-dir $(RESULTS_DIR)

# Run all tests at each level and show table (serial across environments)
.PHONY: results-gate
results-gate:
	@$(AGGREGATE) --run --test-level GATE --results-dir $(RESULTS_DIR)

.PHONY: results-func
results-func:
	@$(AGGREGATE) --run --test-level FUNC --results-dir $(RESULTS_DIR)

.PHONY: results-full
results-full:
	@$(AGGREGATE) --run --test-level FULL --results-dir $(RESULTS_DIR)

# Run all tests at each level in parallel (concurrent across environments)
.PHONY: results-gate-parallel
results-gate-parallel:
	@$(AGGREGATE) --run --parallel --test-level GATE --results-dir $(RESULTS_DIR)

.PHONY: results-func-parallel
results-func-parallel:
	@$(AGGREGATE) --run --parallel --test-level FUNC --results-dir $(RESULTS_DIR)

.PHONY: results-full-parallel
results-full-parallel:
	@$(AGGREGATE) --run --parallel --test-level FULL --results-dir $(RESULTS_DIR)

# Per-area results
.PHONY: results-rapids
results-rapids:
	@$(AGGREGATE) --run --area rapids --test-level $(or $(TEST_LEVEL),GATE) --results-dir $(RESULTS_DIR)

.PHONY: results-stream
results-stream:
	@$(AGGREGATE) --run --area stream --test-level $(or $(TEST_LEVEL),GATE) --results-dir $(RESULTS_DIR)

.PHONY: results-val
results-val:
	@$(AGGREGATE) --run --area val --test-level $(or $(TEST_LEVEL),GATE) --results-dir $(RESULTS_DIR)

# Export as markdown
.PHONY: results-md
results-md:
	@$(AGGREGATE) --results-dir $(RESULTS_DIR) --markdown $(RESULTS_DIR)/results_summary.md

.PHONY: clean-results
clean-results:
	@rm -rf $(RESULTS_DIR)
	@echo "Test results cleaned"

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
clean-all: clean-tests clean-lint clean-results
	@echo "================================================================================"
	@echo "✓ All artifacts cleaned (tests + lint + results)"
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
