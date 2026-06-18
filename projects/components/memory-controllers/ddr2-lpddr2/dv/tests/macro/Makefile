# ==============================================================================
# DDR2/LPDDR2 Memory-Controller Macro Tests Makefile
# ==============================================================================
#
# Local test runner for macro-level (integration) tests.
#
# Usage:
#   source $REPO_ROOT/env_python              # one-time per shell
#   cd $REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/dv/tests/macro
#   make help                                  # list targets
#   make run                                   # full matrix (~2 min wall)
#   make run-fast                              # single-rank only (~5 s)
#
# ==============================================================================

SHELL := /bin/bash

ifndef REPO_ROOT
$(error REPO_ROOT is not set. Please run: source $$REPO_ROOT/env_python)
endif

# Pytest invocation. Assumes `source env_python` already activated the venv.
PYTEST          := python3 -m pytest
PYTEST_VERBOSE  := -v
PYTEST_TBSTYLE  := --tb=short
PYTEST_XDIST    := -n auto
PYTEST_RERUNS   := --reruns 2 --reruns-delay 1

TEST_FILE       := test_axi_frontend_macro.py

# Default target
.DEFAULT_GOAL := help


#==============================================================================
# Help
#==============================================================================

.PHONY: help
help:
	@echo "=========================================================================="
	@echo " DDR2/LPDDR2 Memory-Controller Macro Tests"
	@echo "=========================================================================="
	@echo ""
	@echo " FULL MATRIX:"
	@echo "   make run                  Full matrix (single-rank + multi-rank)"
	@echo "   make run-waves            Full matrix with VCD dumping"
	@echo "   make run-parallel         Full matrix in parallel (pytest-xdist)"
	@echo "   make run-parallel-waves   Full matrix in parallel with VCD"
	@echo ""
	@echo " BY BUILD CONFIG:"
	@echo "   make run-single           Single-rank scenarios only (NUM_RANKS=1)"
	@echo "   make run-multi            Multi-rank scenarios only (NUM_RANKS=2)"
	@echo "   make run-fast             Alias for run-single (skips multi-rank rebuild)"
	@echo ""
	@echo " BY CATEGORY (pytest -k):"
	@echo "   make run-sanity           smoke / miss / partial_strb / len_mismatch"
	@echo "   make run-stream           wr_stream / rd_stream / mixed_stream"
	@echo "   make run-snarf            snarf_stream / last_write_wins / issued_then_snarf"
	@echo "   make run-ordering         same_id_in_order / mixed_id_ooo"
	@echo "   make run-lifecycle        wr_full_lifecycle / rd_full_lifecycle"
	@echo "   make run-backpressure     wr_cam_full / rd_cam_full / forwarded_backpressure"
	@echo "   make run-sched            scheduler_query_* / b_complete_clears / mark_issued"
	@echo "   make run-misc             concurrent_aw_ar / addr_scheme_sweep"
	@echo ""
	@echo " INDIVIDUAL SCENARIOS (use SCENARIO=<name>):"
	@echo "   make run-one SCENARIO=smoke"
	@echo "   make run-one-waves SCENARIO=snarf_stream"
	@echo ""
	@echo " UTILITY:"
	@echo "   make collect              Collect (do not run) tests"
	@echo "   make list                 Print every parametrized scenario id"
	@echo "   make clean                Remove pytest cache + .pyc"
	@echo "   make clean-all            Also remove local_sim_build/ and logs/"
	@echo ""
	@echo "=========================================================================="


#==============================================================================
# Full matrix
#==============================================================================

.PHONY: run
run:
	@echo "Running full macro matrix (single-rank + multi-rank)..."
	$(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-waves
run-waves:
	@echo "Running full macro matrix with VCD dumps..."
	WAVES=1 $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-parallel
run-parallel:
	@echo "Running full macro matrix in parallel..."
	$(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-parallel-waves
run-parallel-waves:
	@echo "Running full macro matrix in parallel with VCD..."
	WAVES=1 $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)


#==============================================================================
# By build config
#==============================================================================

.PHONY: run-single
run-single:
	@echo "Running single-rank scenarios..."
	$(PYTEST) $(TEST_FILE)::test_axi_frontend_macro $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-multi
run-multi:
	@echo "Running multi-rank scenarios..."
	$(PYTEST) $(TEST_FILE)::test_axi_frontend_macro_multirank $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-fast
run-fast: run-single


#==============================================================================
# By category (pytest -k expression)
#==============================================================================

.PHONY: run-sanity
run-sanity:
	$(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
	  -k "smoke or miss or partial_strb or len_mismatch"

.PHONY: run-stream
run-stream:
	$(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
	  -k "wr_stream or rd_stream or mixed_stream"

.PHONY: run-snarf
run-snarf:
	$(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
	  -k "snarf or last_write_wins or issued_then_snarf"

.PHONY: run-ordering
run-ordering:
	$(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
	  -k "same_id_in_order or mixed_id_ooo"

.PHONY: run-lifecycle
run-lifecycle:
	$(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
	  -k "full_lifecycle"

.PHONY: run-backpressure
run-backpressure:
	$(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
	  -k "cam_full or forwarded_backpressure"

.PHONY: run-sched
run-sched:
	$(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
	  -k "scheduler_query or b_complete_clears or mark_issued"

.PHONY: run-misc
run-misc:
	$(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
	  -k "concurrent_aw_ar or addr_scheme_sweep or multirank"


#==============================================================================
# Single-scenario targets
#==============================================================================

# Usage: make run-one SCENARIO=smoke
.PHONY: run-one
run-one:
	@if [ -z "$(SCENARIO)" ]; then \
	  echo "Error: SCENARIO=<name> is required."; \
	  echo "  e.g. make run-one SCENARIO=snarf_stream"; \
	  exit 1; \
	fi
	$(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) -k "$(SCENARIO)"

.PHONY: run-one-waves
run-one-waves:
	@if [ -z "$(SCENARIO)" ]; then \
	  echo "Error: SCENARIO=<name> is required."; \
	  echo "  e.g. make run-one-waves SCENARIO=snarf_stream"; \
	  exit 1; \
	fi
	WAVES=1 $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) -k "$(SCENARIO)"


#==============================================================================
# Utility
#==============================================================================

.PHONY: collect
collect:
	$(PYTEST) $(TEST_FILE) --collect-only -q

.PHONY: list
list:
	@$(PYTEST) $(TEST_FILE) --collect-only -q 2>/dev/null \
	   | grep -E '\[.*\]$$' \
	   | sed 's/.*\[/  /' \
	   | sed 's/\]$$//'

.PHONY: clean
clean:
	@echo "Cleaning pytest cache + .pyc..."
	rm -rf __pycache__ .pytest_cache
	find . -name "*.pyc" -delete

.PHONY: clean-all
clean-all: clean
	@echo "Cleaning build artifacts + logs..."
	rm -rf local_sim_build logs/*.log logs/results_*.xml
	find . -name "*.vcd" -delete
