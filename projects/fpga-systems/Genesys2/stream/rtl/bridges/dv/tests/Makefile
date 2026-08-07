# ==============================================================================
# Stream Characterization Bridge Test Makefile
# ==============================================================================
#
# Local test runner for the 1x6 AXIL bridge that fronts the
# stream_characterization harness (host master + 5 AXIL slaves + 1 APB slave).
#
# PREREQUISITES:
#   source $REPO_ROOT/env_python
#   cd $REPO_ROOT/projects/NexysA7/stream_characterization/stream_char_framework/rtl/bridges/dv/tests
#   make <target>
#
# Quick start:
#   make help              - Show all targets
#   make run               - Run both auto-generated bridge tests
#   make run-waves         - Same, dumping VCD waveforms
#   make rebuild           - Regenerate bridge RTL + TB + tests, then run
#   make clean             - Remove local sim artifacts
#
# Tests cover:
#   basic_connectivity     - host writes one txn to each slave; verify routing
#   address_decode         - sweep each slave's base addr; verify decode
#
# ==============================================================================

SHELL := /bin/bash

ifndef REPO_ROOT
$(error REPO_ROOT is not set. Please run: source $$REPO_ROOT/env_python)
endif

# ------------------------------------------------------------------------------
# Paths
# ------------------------------------------------------------------------------
BRIDGE_BIN     = $(REPO_ROOT)/projects/components/bridge/bin
BRIDGE_GEN     = $(BRIDGE_BIN)/bridge_generator.py

# Everything bridge-related lives under stream_char_framework/rtl/bridges/.
# Paths below are absolute so the Makefile works the same whether you cd
# here or invoke it from elsewhere.
BRIDGES_ROOT   = $(REPO_ROOT)/projects/NexysA7/stream_characterization/stream_char_framework/rtl/bridges
CONFIG_DIR     = $(BRIDGES_ROOT)/configs
RTL_DIR        = $(BRIDGES_ROOT)/generated
TB_DIR         = $(BRIDGES_ROOT)/dv/tbclasses
TEST_DIR       = $(BRIDGES_ROOT)/dv/tests
FILELIST_DIR   = $(BRIDGES_ROOT)/filelists

BRIDGE_NAME    = bridge_stream_char_axil
PORTS_TOML     = $(CONFIG_DIR)/$(BRIDGE_NAME).toml
CONN_CSV       = $(CONFIG_DIR)/$(BRIDGE_NAME)_connectivity.csv

TEST_FILE      = test_$(BRIDGE_NAME).py

# ------------------------------------------------------------------------------
# Pytest options
# ------------------------------------------------------------------------------
PYTEST           = python3 -m pytest
PYTEST_VERBOSE   = -v
PYTEST_QUIET     = -q
PYTEST_TBSTYLE   = --tb=short
PYTEST_XDIST     = -n 2
PYTEST_RERUNS    = --reruns 3 --reruns-delay 1

.DEFAULT_GOAL := help

# Files that the run targets need; if any are missing, ensure-generated will
# fire `make tests` to recreate them. Lets you do `make clean-all && make run`
# without remembering an explicit regen step.
GENERATED_TEST   = $(TEST_DIR)/$(TEST_FILE)
GENERATED_TB     = $(TB_DIR)/$(BRIDGE_NAME)_tb.py
GENERATED_RTL    = $(RTL_DIR)/$(BRIDGE_NAME)/$(BRIDGE_NAME).sv
GENERATED_FL     = $(FILELIST_DIR)/$(BRIDGE_NAME).f

# ==============================================================================
# Help
# ==============================================================================

.PHONY: help
help:
	@echo "================================================================================"
	@echo "Stream Characterization Bridge Test Makefile"
	@echo "================================================================================"
	@echo ""
	@echo "RUN TARGETS:"
	@echo "  make run                    Run both bridge tests (sequential)"
	@echo "  make run-quiet              Same, less verbose pytest output"
	@echo "  make run-waves              Run with VCD waveform dumps (WAVES=1)"
	@echo "  make run-parallel           Run two cases in parallel (-n 2)"
	@echo "  make run-parallel-waves     Parallel + waves"
	@echo "  make run-basic              Just basic_connectivity"
	@echo "  make run-decode             Just address_decode"
	@echo ""
	@echo "BUILD / REGEN:"
	@echo "  make rtl                    Regenerate RTL only (no tests/TB)"
	@echo "  make tests                  Regenerate RTL + TB + test runner"
	@echo "  make rebuild                clean + tests + run"
	@echo ""
	@echo "CLEAN:"
	@echo "  make clean                  Remove local sim artifacts (.pytest_cache, sim_build, logs)"
	@echo "  make clean-rtl              Delete generated RTL only"
	@echo "  make clean-tests            Delete generated TB + test file"
	@echo "  make clean-all              clean + clean-rtl + clean-tests"
	@echo ""
	@echo "FILES:"
	@echo "  config         $(PORTS_TOML)"
	@echo "  connectivity   $(CONN_CSV)"
	@echo "  test runner    $(TEST_DIR)/$(TEST_FILE)"
	@echo "  TB class       $(TB_DIR)/$(BRIDGE_NAME)_tb.py"
	@echo "  filelist       $(FILELIST_DIR)/$(BRIDGE_NAME).f"
	@echo "================================================================================"

# ==============================================================================
# Run targets
# ==============================================================================
#
# Every run-* target depends on `ensure-generated`, which calls `make tests`
# if any of the generated files are missing. Lets you do
#   make clean-all && make run-parallel-waves
# without an explicit regen step in between.

.PHONY: ensure-generated
ensure-generated:
	@missing=0; \
	for f in $(GENERATED_TEST) $(GENERATED_TB) $(GENERATED_RTL) $(GENERATED_FL); do \
	    if [ ! -f "$$f" ]; then \
	        echo "  missing: $$f"; \
	        missing=1; \
	    fi; \
	done; \
	if [ $$missing -eq 1 ]; then \
	    echo "Generated files missing — running 'make tests' first..."; \
	    $(MAKE) --no-print-directory tests; \
	fi

.PHONY: run
run: ensure-generated
	@echo "Running $(BRIDGE_NAME) auto-tests (sequential)..."
	$(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-quiet
run-quiet: ensure-generated
	$(PYTEST) $(TEST_FILE) $(PYTEST_QUIET) $(PYTEST_TBSTYLE)

.PHONY: run-waves
run-waves: ensure-generated
	@echo "Running $(BRIDGE_NAME) auto-tests with WAVES=1..."
	WAVES=1 $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-parallel
run-parallel: ensure-generated
	@echo "Running $(BRIDGE_NAME) auto-tests in parallel (-n 2)..."
	$(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-parallel-waves
run-parallel-waves: ensure-generated
	WAVES=1 $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-basic
run-basic: ensure-generated
	$(PYTEST) $(TEST_FILE)::test_$(BRIDGE_NAME)_basic_connectivity $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-decode
run-decode: ensure-generated
	$(PYTEST) $(TEST_FILE)::test_$(BRIDGE_NAME)_address_decode $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

# ==============================================================================
# Aliases (stay consistent with bridge component Makefile)
# ==============================================================================

.PHONY: run-all run-all-waves run-all-parallel run-all-parallel-waves
run-all: run
run-all-waves: run-waves
run-all-parallel: run-parallel
run-all-parallel-waves: run-parallel-waves

# ==============================================================================
# Build / regeneration
# ==============================================================================

.PHONY: rtl
rtl:
	@echo "================================================================================"
	@echo "Regenerating $(BRIDGE_NAME) RTL only"
	@echo "================================================================================"
	python3 $(BRIDGE_GEN) \
		--ports $(PORTS_TOML) \
		--connectivity $(CONN_CSV) \
		--name $(BRIDGE_NAME) \
		--output-dir $(RTL_DIR)
	@echo "✅ RTL regenerated at $(RTL_DIR)/$(BRIDGE_NAME)/"

REGEN_BRIDGES = $(REPO_ROOT)/projects/NexysA7/stream_characterization/stream_char_framework/bin/regen_bridges.sh

.PHONY: tests
tests:
	@echo "================================================================================"
	@echo "Regenerating $(BRIDGE_NAME) via shared regen_bridges.sh"
	@echo "================================================================================"
	@$(REGEN_BRIDGES) $(BRIDGE_NAME)
	@echo "   RTL:        $(RTL_DIR)/$(BRIDGE_NAME)/"
	@echo "   TB class:   $(TB_DIR)/$(BRIDGE_NAME)_tb.py"
	@echo "   Test file:  $(TEST_DIR)/$(TEST_FILE)"
	@echo "   Filelist:   $(FILELIST_DIR)/$(BRIDGE_NAME).f"

.PHONY: rebuild
rebuild: clean tests run

# ==============================================================================
# Clean
# ==============================================================================

.PHONY: clean
clean:
	@echo "Cleaning local sim artifacts..."
	rm -rf __pycache__ .pytest_cache sim_build sim_build_* logs
	find . -name "*.pyc" -delete
	find . -name "*.vcd" -delete
	find . -name "*.fst" -delete

.PHONY: clean-rtl
clean-rtl:
	@echo "Deleting generated RTL: $(RTL_DIR)/$(BRIDGE_NAME)/"
	rm -rf $(RTL_DIR)/$(BRIDGE_NAME)
	rm -f $(FILELIST_DIR)/$(BRIDGE_NAME).f

.PHONY: clean-tests
clean-tests:
	@echo "Deleting generated TB + test file..."
	rm -f $(TB_DIR)/$(BRIDGE_NAME)_tb.py
	rm -f $(TEST_DIR)/$(TEST_FILE)

.PHONY: clean-all
clean-all: clean clean-rtl clean-tests
	@echo "✅ Cleaned everything (local artifacts + generated RTL + TB + test)"
