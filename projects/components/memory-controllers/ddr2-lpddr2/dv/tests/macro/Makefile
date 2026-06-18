# ==============================================================================
# DDR2/LPDDR2 Memory-Controller Macro Tests Makefile
# ==============================================================================
#
# Local test runner for macro-level (integration) tests.
#
# Test-level methodology (mirrors stream's REG_LEVEL convention):
#
#   GATE  : minimal smoke (~5 s wall) — fast CI sanity, 1 scenario
#   FUNC  : functional coverage (~30 s wall) — default for dev, ~14 scenarios
#   FULL  : comprehensive — every scenario (~2 min wall), 23 scenarios
#
# The TEST_LEVEL variable is reserved for future TB-side stress depth
# (random seeds, iteration counts) — orthogonal to REG_LEVEL. Not used yet.
#
# Usage:
#   source $REPO_ROOT/env_python              # one-time per shell
#   cd $REPO_ROOT/projects/components/memory-controllers/ddr2-lpddr2/dv/tests/macro
#   make help                                  # list targets
#   make run-func                              # default dev run
#   make run-gate                              # fast sanity
#   make run-full                              # comprehensive
#
# ==============================================================================

SHELL := /bin/bash

ifndef REPO_ROOT
$(error REPO_ROOT is not set. Please run: source $$REPO_ROOT/env_python)
endif

PYTEST          := python3 -m pytest
PYTEST_VERBOSE  := -v
PYTEST_TBSTYLE  := --tb=short
PYTEST_XDIST    := -n auto
PYTEST_RERUNS   := --reruns 2 --reruns-delay 1

TEST_FILE       := test_axi_frontend_macro.py

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
	@echo " REGRESSION LEVELS (REG_LEVEL):"
	@echo "   make run-gate                 Minimal smoke   (~5 s,   1 scenario)"
	@echo "   make run-func                 Functional cov  (~30 s, ~14 scenarios)  [DEFAULT]"
	@echo "   make run-full                 Comprehensive   (~2 min, 23 scenarios)"
	@echo ""
	@echo " WITH WAVEFORMS (VCD dumping; WAVES=1):"
	@echo "   make run-gate-waves"
	@echo "   make run-func-waves"
	@echo "   make run-full-waves"
	@echo ""
	@echo " IN PARALLEL (pytest-xdist; -n auto):"
	@echo "   make run-gate-parallel        make run-gate-parallel-waves"
	@echo "   make run-func-parallel        make run-func-parallel-waves"
	@echo "   make run-full-parallel        make run-full-parallel-waves"
	@echo ""
	@echo " BY BUILD CONFIG (orthogonal to level):"
	@echo "   make run-single               NUM_RANKS=1 only"
	@echo "   make run-multi                NUM_RANKS=2 only"
	@echo ""
	@echo " BY CATEGORY (within FULL set):"
	@echo "   make run-sanity / run-stream / run-snarf / run-ordering"
	@echo "   make run-lifecycle / run-backpressure / run-sched / run-misc"
	@echo ""
	@echo " INDIVIDUAL SCENARIO (SCENARIO=<name>):"
	@echo "   make run-one SCENARIO=smoke"
	@echo "   make run-one-waves SCENARIO=snarf_stream"
	@echo ""
	@echo " UTILITY:"
	@echo "   make collect                  Collect (do not run) tests at FUNC"
	@echo "   make list                     Print scenarios in current REG_LEVEL"
	@echo "   make clean                    Remove pytest cache + .pyc"
	@echo "   make clean-all                Also remove local_sim_build/ and logs/"
	@echo ""
	@echo " ENV VARS:"
	@echo "   REG_LEVEL = GATE | FUNC | FULL    (default FUNC)"
	@echo "   WAVES     = 0 | 1                 (default 0)"
	@echo "   SCENARIO  = <scenario name>       (for run-one targets)"
	@echo ""
	@echo "=========================================================================="


#==============================================================================
# Regression-level targets
#==============================================================================

.PHONY: run-gate
run-gate:
	@echo "[REG_LEVEL=GATE] Running minimal smoke..."
	REG_LEVEL=GATE $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-gate-waves
run-gate-waves:
	@echo "[REG_LEVEL=GATE WAVES=1] Running minimal smoke with VCD..."
	REG_LEVEL=GATE WAVES=1 $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-gate-parallel
run-gate-parallel:
	REG_LEVEL=GATE $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-gate-parallel-waves
run-gate-parallel-waves:
	REG_LEVEL=GATE WAVES=1 $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)


.PHONY: run-func
run-func:
	@echo "[REG_LEVEL=FUNC] Running functional coverage..."
	REG_LEVEL=FUNC $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-func-waves
run-func-waves:
	REG_LEVEL=FUNC WAVES=1 $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-func-parallel
run-func-parallel:
	REG_LEVEL=FUNC $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-func-parallel-waves
run-func-parallel-waves:
	REG_LEVEL=FUNC WAVES=1 $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)


.PHONY: run-full
run-full:
	@echo "[REG_LEVEL=FULL] Running comprehensive matrix..."
	REG_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-full-waves
run-full-waves:
	REG_LEVEL=FULL WAVES=1 $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-full-parallel
run-full-parallel:
	REG_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-full-parallel-waves
run-full-parallel-waves:
	REG_LEVEL=FULL WAVES=1 $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)


#==============================================================================
# By build config (orthogonal to REG_LEVEL — runs at REG_LEVEL=FULL)
#==============================================================================

.PHONY: run-single
run-single:
	REG_LEVEL=FULL $(PYTEST) $(TEST_FILE)::test_axi_frontend_macro $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-multi
run-multi:
	REG_LEVEL=FULL $(PYTEST) $(TEST_FILE)::test_axi_frontend_macro_multirank $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)


#==============================================================================
# By category (within FULL set — uses pytest -k filters)
#==============================================================================

.PHONY: run-sanity
run-sanity:
	REG_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
	  -k "smoke or miss or partial_strb or len_mismatch"

.PHONY: run-stream
run-stream:
	REG_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
	  -k "wr_stream or rd_stream or mixed_stream"

.PHONY: run-snarf
run-snarf:
	REG_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
	  -k "snarf or last_write_wins or issued_then_snarf"

.PHONY: run-ordering
run-ordering:
	REG_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
	  -k "same_id_in_order or mixed_id_ooo"

.PHONY: run-lifecycle
run-lifecycle:
	REG_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
	  -k "full_lifecycle"

.PHONY: run-backpressure
run-backpressure:
	REG_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
	  -k "cam_full or forwarded_backpressure"

.PHONY: run-sched
run-sched:
	REG_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
	  -k "scheduler_query or b_complete_clears or mark_issued"

.PHONY: run-misc
run-misc:
	REG_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) \
	  -k "concurrent_aw_ar or addr_scheme_sweep or multirank"


#==============================================================================
# Single-scenario targets
#==============================================================================

.PHONY: run-one
run-one:
	@if [ -z "$(SCENARIO)" ]; then \
	  echo "Error: SCENARIO=<name> is required."; \
	  echo "  e.g. make run-one SCENARIO=snarf_stream"; \
	  exit 1; \
	fi
	REG_LEVEL=FULL $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) -k "$(SCENARIO)"

.PHONY: run-one-waves
run-one-waves:
	@if [ -z "$(SCENARIO)" ]; then \
	  echo "Error: SCENARIO=<name> is required."; \
	  echo "  e.g. make run-one-waves SCENARIO=snarf_stream"; \
	  exit 1; \
	fi
	REG_LEVEL=FULL WAVES=1 $(PYTEST) $(TEST_FILE) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) -k "$(SCENARIO)"


#==============================================================================
# Utility
#==============================================================================

.PHONY: collect
collect:
	REG_LEVEL=FUNC $(PYTEST) $(TEST_FILE) --collect-only -q

.PHONY: list
list:
	@echo "Scenarios at REG_LEVEL=$${REG_LEVEL:-FUNC} (override with REG_LEVEL=GATE|FUNC|FULL):"
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
