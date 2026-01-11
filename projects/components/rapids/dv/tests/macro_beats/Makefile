# ==============================================================================
# RAPIDS Macro Beats Tests Makefile
# ==============================================================================
#
# Local test runner for macro-level beats architecture tests
#
# Usage:
#   cd $REPO_ROOT/projects/components/rapids/dv/tests/macro_beats
#   make <target>
#
# Quick start:
#   make help           - Show available targets
#   make run-all        - Run all tests (FUNC level)
#   make clean          - Clean local artifacts
#
# ==============================================================================

# Force bash shell
SHELL := /bin/bash

# Check if REPO_ROOT is set (from env_python)
ifndef REPO_ROOT
$(error REPO_ROOT is not set. Please run: source $$REPO_ROOT/env_python)
endif

# Pytest options
PYTEST = python3 -m pytest
PYTEST_VERBOSE = -v
PYTEST_QUIET = -q
PYTEST_XDIST = -n 48
PYTEST_TBSTYLE = --tb=short
PYTEST_RERUNS = --reruns 0 --reruns-delay 1

# Pytest-watch options
PTW = ptw
PTW_FLAGS = --runner "pytest --maxfail=1"

# Default target
.DEFAULT_GOAL := help

# ==============================================================================
# Help Target
# ==============================================================================

.PHONY: help
help:
	@echo "================================================================================"
	@echo "RAPIDS Macro Beats Tests Makefile"
	@echo "================================================================================"
	@echo ""
	@echo "QUICK RUN TARGETS:"
	@echo "  make run-all                    Run all tests (FUNC level)"
	@echo "  make run-sched-grp              Run scheduler_group tests"
	@echo "  make run-sched-arr              Run scheduler_group_array tests"
	@echo "  make run-sink-dp                Run sink_datapath tests"
	@echo "  make run-source-dp              Run source_datapath tests"
	@echo "  make run-sink-axis              Run sink_data_path_axis tests"
	@echo "  make run-source-axis            Run source_data_path_axis tests"
	@echo "  make run-snk-sram               Run snk_sram_controller tests"
	@echo "  make run-src-sram               Run src_sram_controller tests"
	@echo ""
	@echo "SCHEDULER GROUP TARGETS (test_beats_scheduler_group.py):"
	@echo "  make run-sched-grp-gate                Run at GATE level"
	@echo "  make run-sched-grp-gate-waves          Run at GATE level with waveforms"
	@echo "  make run-sched-grp-gate-parallel       Run at GATE level in parallel"
	@echo "  make run-sched-grp-gate-parallel-waves Run at GATE level parallel + waves"
	@echo "  make run-sched-grp-func                Run at FUNC level (default)"
	@echo "  make run-sched-grp-func-waves          Run at FUNC level with waveforms"
	@echo "  make run-sched-grp-func-parallel       Run at FUNC level in parallel"
	@echo "  make run-sched-grp-func-parallel-waves Run at FUNC level parallel + waves"
	@echo "  make run-sched-grp-full                Run at FULL level"
	@echo "  make run-sched-grp-full-waves          Run at FULL level with waveforms"
	@echo "  make run-sched-grp-full-parallel       Run at FULL level in parallel"
	@echo "  make run-sched-grp-full-parallel-waves Run at FULL level parallel + waves"
	@echo ""
	@echo "SCHEDULER GROUP ARRAY TARGETS (test_beats_scheduler_group_array.py):"
	@echo "  make run-sched-arr-gate                Run at GATE level"
	@echo "  make run-sched-arr-gate-waves          Run at GATE level with waveforms"
	@echo "  make run-sched-arr-gate-parallel       Run at GATE level in parallel"
	@echo "  make run-sched-arr-gate-parallel-waves Run at GATE level parallel + waves"
	@echo "  make run-sched-arr-func                Run at FUNC level (default)"
	@echo "  make run-sched-arr-func-waves          Run at FUNC level with waveforms"
	@echo "  make run-sched-arr-func-parallel       Run at FUNC level in parallel"
	@echo "  make run-sched-arr-func-parallel-waves Run at FUNC level parallel + waves"
	@echo "  make run-sched-arr-full                Run at FULL level"
	@echo "  make run-sched-arr-full-waves          Run at FULL level with waveforms"
	@echo "  make run-sched-arr-full-parallel       Run at FULL level in parallel"
	@echo "  make run-sched-arr-full-parallel-waves Run at FULL level parallel + waves"
	@echo ""
	@echo "SINK DATAPATH TARGETS (test_sink_datapath.py):"
	@echo "  make run-sink-dp-gate                Run at GATE level"
	@echo "  make run-sink-dp-gate-waves          Run at GATE level with waveforms"
	@echo "  make run-sink-dp-gate-parallel       Run at GATE level in parallel"
	@echo "  make run-sink-dp-gate-parallel-waves Run at GATE level parallel + waves"
	@echo "  make run-sink-dp-func                Run at FUNC level (default)"
	@echo "  make run-sink-dp-func-waves          Run at FUNC level with waveforms"
	@echo "  make run-sink-dp-func-parallel       Run at FUNC level in parallel"
	@echo "  make run-sink-dp-func-parallel-waves Run at FUNC level parallel + waves"
	@echo "  make run-sink-dp-full                Run at FULL level"
	@echo "  make run-sink-dp-full-waves          Run at FULL level with waveforms"
	@echo "  make run-sink-dp-full-parallel       Run at FULL level in parallel"
	@echo "  make run-sink-dp-full-parallel-waves Run at FULL level parallel + waves"
	@echo ""
	@echo "SOURCE DATAPATH TARGETS (test_source_datapath.py):"
	@echo "  make run-source-dp-gate                Run at GATE level"
	@echo "  make run-source-dp-gate-waves          Run at GATE level with waveforms"
	@echo "  make run-source-dp-gate-parallel       Run at GATE level in parallel"
	@echo "  make run-source-dp-gate-parallel-waves Run at GATE level parallel + waves"
	@echo "  make run-source-dp-func                Run at FUNC level (default)"
	@echo "  make run-source-dp-func-waves          Run at FUNC level with waveforms"
	@echo "  make run-source-dp-func-parallel       Run at FUNC level in parallel"
	@echo "  make run-source-dp-func-parallel-waves Run at FUNC level parallel + waves"
	@echo "  make run-source-dp-full                Run at FULL level"
	@echo "  make run-source-dp-full-waves          Run at FULL level with waveforms"
	@echo "  make run-source-dp-full-parallel       Run at FULL level in parallel"
	@echo "  make run-source-dp-full-parallel-waves Run at FULL level parallel + waves"
	@echo ""
	@echo "SINK DATA PATH AXIS TARGETS (test_sink_data_path_axis_test.py):"
	@echo "  make run-sink-axis-gate                Run at GATE level"
	@echo "  make run-sink-axis-gate-waves          Run at GATE level with waveforms"
	@echo "  make run-sink-axis-gate-parallel       Run at GATE level in parallel"
	@echo "  make run-sink-axis-func                Run at FUNC level (default)"
	@echo "  make run-sink-axis-func-waves          Run at FUNC level with waveforms"
	@echo "  make run-sink-axis-func-parallel       Run at FUNC level in parallel"
	@echo "  make run-sink-axis-full                Run at FULL level"
	@echo "  make run-sink-axis-full-waves          Run at FULL level with waveforms"
	@echo "  make run-sink-axis-full-parallel       Run at FULL level in parallel"
	@echo ""
	@echo "SOURCE DATA PATH AXIS TARGETS (test_source_data_path_axis_test.py):"
	@echo "  make run-source-axis-gate                Run at GATE level"
	@echo "  make run-source-axis-gate-waves          Run at GATE level with waveforms"
	@echo "  make run-source-axis-gate-parallel       Run at GATE level in parallel"
	@echo "  make run-source-axis-func                Run at FUNC level (default)"
	@echo "  make run-source-axis-func-waves          Run at FUNC level with waveforms"
	@echo "  make run-source-axis-func-parallel       Run at FUNC level in parallel"
	@echo "  make run-source-axis-full                Run at FULL level"
	@echo "  make run-source-axis-full-waves          Run at FULL level with waveforms"
	@echo "  make run-source-axis-full-parallel       Run at FULL level in parallel"
	@echo ""
	@echo "SNK SRAM CONTROLLER TARGETS (test_snk_sram_controller.py):"
	@echo "  make run-snk-sram-gate                Run at GATE level"
	@echo "  make run-snk-sram-gate-waves          Run at GATE level with waveforms"
	@echo "  make run-snk-sram-gate-parallel       Run at GATE level in parallel"
	@echo "  make run-snk-sram-func                Run at FUNC level (default)"
	@echo "  make run-snk-sram-func-waves          Run at FUNC level with waveforms"
	@echo "  make run-snk-sram-func-parallel       Run at FUNC level in parallel"
	@echo "  make run-snk-sram-full                Run at FULL level"
	@echo "  make run-snk-sram-full-waves          Run at FULL level with waveforms"
	@echo "  make run-snk-sram-full-parallel       Run at FULL level in parallel"
	@echo ""
	@echo "SRC SRAM CONTROLLER TARGETS (test_src_sram_controller.py):"
	@echo "  make run-src-sram-gate                Run at GATE level"
	@echo "  make run-src-sram-gate-waves          Run at GATE level with waveforms"
	@echo "  make run-src-sram-gate-parallel       Run at GATE level in parallel"
	@echo "  make run-src-sram-func                Run at FUNC level (default)"
	@echo "  make run-src-sram-func-waves          Run at FUNC level with waveforms"
	@echo "  make run-src-sram-func-parallel       Run at FUNC level in parallel"
	@echo "  make run-src-sram-full                Run at FULL level"
	@echo "  make run-src-sram-full-waves          Run at FULL level with waveforms"
	@echo "  make run-src-sram-full-parallel       Run at FULL level in parallel"
	@echo ""
	@echo "COMBINED TARGETS:"
	@echo "  make run-all-gate               Run all tests at GATE level"
	@echo "  make run-all-gate-waves         Run all tests at GATE level with waveforms"
	@echo "  make run-all-gate-parallel      Run all tests at GATE level in parallel"
	@echo "  make run-all-func               Run all tests at FUNC level"
	@echo "  make run-all-func-waves         Run all tests at FUNC level with waveforms"
	@echo "  make run-all-func-parallel      Run all tests at FUNC level in parallel"
	@echo "  make run-all-full               Run all tests at FULL level"
	@echo "  make run-all-full-waves         Run all tests at FULL level with waveforms"
	@echo "  make run-all-full-parallel      Run all tests at FULL level in parallel"
	@echo "  make run-all-full-parallel-waves Run all tests at FULL level parallel + waves"
	@echo ""
	@echo "UTILITY TARGETS:"
	@echo "  make collect-sched-grp     Collect (don't run) scheduler_group tests"
	@echo "  make collect-sched-arr     Collect (don't run) scheduler_group_array tests"
	@echo "  make collect-sink-dp       Collect (don't run) sink_datapath tests"
	@echo "  make collect-source-dp     Collect (don't run) source_datapath tests"
	@echo "  make collect-sink-axis     Collect (don't run) sink_axis tests"
	@echo "  make collect-source-axis   Collect (don't run) source_axis tests"
	@echo "  make collect-snk-sram      Collect (don't run) snk_sram tests"
	@echo "  make collect-src-sram      Collect (don't run) src_sram tests"
	@echo "  make clean                 Clean local artifacts"
	@echo "  make clean-all             Clean all test artifacts"
	@echo ""
	@echo "================================================================================"

# ==============================================================================
# Quick Run Targets (Default FUNC level)
# ==============================================================================

.PHONY: run-all
run-all:
	@echo "Running all macro_beats tests (FUNC level)..."
	TEST_LEVEL=FUNC $(PYTEST) . $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sched-grp
run-sched-grp:
	@echo "Running beats_scheduler_group tests (FUNC level)..."
	TEST_LEVEL=FUNC $(PYTEST) test_beats_scheduler_group.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sched-arr
run-sched-arr:
	@echo "Running beats_scheduler_group_array tests (FUNC level)..."
	TEST_LEVEL=FUNC $(PYTEST) test_beats_scheduler_group_array.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sink-dp
run-sink-dp:
	@echo "Running sink_datapath tests (FUNC level)..."
	TEST_LEVEL=FUNC $(PYTEST) test_sink_datapath.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-source-dp
run-source-dp:
	@echo "Running source_datapath tests (FUNC level)..."
	TEST_LEVEL=FUNC $(PYTEST) test_source_datapath.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sink-axis
run-sink-axis:
	@echo "Running sink_data_path_axis tests (FUNC level)..."
	TEST_LEVEL=FUNC $(PYTEST) test_sink_data_path_axis_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-source-axis
run-source-axis:
	@echo "Running source_data_path_axis tests (FUNC level)..."
	TEST_LEVEL=FUNC $(PYTEST) test_source_data_path_axis_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-snk-sram
run-snk-sram:
	@echo "Running snk_sram_controller tests (FUNC level)..."
	TEST_LEVEL=FUNC $(PYTEST) test_snk_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-src-sram
run-src-sram:
	@echo "Running src_sram_controller tests (FUNC level)..."
	TEST_LEVEL=FUNC $(PYTEST) test_src_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

# ==============================================================================
# Scheduler Group Targets (test_beats_scheduler_group.py)
# ==============================================================================

# GATE level
.PHONY: run-sched-grp-gate
run-sched-grp-gate:
	@echo "Running beats_scheduler_group tests at GATE level..."
	TEST_LEVEL=GATE $(PYTEST) test_beats_scheduler_group.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sched-grp-gate-waves
run-sched-grp-gate-waves:
	@echo "Running beats_scheduler_group tests at GATE level with waveforms..."
	WAVES=1 TEST_LEVEL=GATE $(PYTEST) test_beats_scheduler_group.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sched-grp-gate-parallel
run-sched-grp-gate-parallel:
	@echo "Running beats_scheduler_group tests at GATE level in parallel..."
	TEST_LEVEL=GATE $(PYTEST) test_beats_scheduler_group.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-sched-grp-gate-parallel-waves
run-sched-grp-gate-parallel-waves:
	@echo "Running beats_scheduler_group tests at GATE level parallel with waveforms..."
	WAVES=1 TEST_LEVEL=GATE $(PYTEST) test_beats_scheduler_group.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FUNC level
.PHONY: run-sched-grp-func
run-sched-grp-func:
	@echo "Running beats_scheduler_group tests at FUNC level..."
	TEST_LEVEL=FUNC $(PYTEST) test_beats_scheduler_group.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sched-grp-func-waves
run-sched-grp-func-waves:
	@echo "Running beats_scheduler_group tests at FUNC level with waveforms..."
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) test_beats_scheduler_group.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sched-grp-func-parallel
run-sched-grp-func-parallel:
	@echo "Running beats_scheduler_group tests at FUNC level in parallel..."
	TEST_LEVEL=FUNC $(PYTEST) test_beats_scheduler_group.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-sched-grp-func-parallel-waves
run-sched-grp-func-parallel-waves:
	@echo "Running beats_scheduler_group tests at FUNC level parallel with waveforms..."
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) test_beats_scheduler_group.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FULL level
.PHONY: run-sched-grp-full
run-sched-grp-full:
	@echo "Running beats_scheduler_group tests at FULL level..."
	TEST_LEVEL=FULL $(PYTEST) test_beats_scheduler_group.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sched-grp-full-waves
run-sched-grp-full-waves:
	@echo "Running beats_scheduler_group tests at FULL level with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) test_beats_scheduler_group.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sched-grp-full-parallel
run-sched-grp-full-parallel:
	@echo "Running beats_scheduler_group tests at FULL level in parallel..."
	TEST_LEVEL=FULL $(PYTEST) test_beats_scheduler_group.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-sched-grp-full-parallel-waves
run-sched-grp-full-parallel-waves:
	@echo "Running beats_scheduler_group tests at FULL level parallel with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) test_beats_scheduler_group.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# Scheduler Group Array Targets (test_beats_scheduler_group_array.py)
# ==============================================================================

# GATE level
.PHONY: run-sched-arr-gate
run-sched-arr-gate:
	@echo "Running beats_scheduler_group_array tests at GATE level..."
	TEST_LEVEL=GATE $(PYTEST) test_beats_scheduler_group_array.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sched-arr-gate-waves
run-sched-arr-gate-waves:
	@echo "Running beats_scheduler_group_array tests at GATE level with waveforms..."
	WAVES=1 TEST_LEVEL=GATE $(PYTEST) test_beats_scheduler_group_array.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sched-arr-gate-parallel
run-sched-arr-gate-parallel:
	@echo "Running beats_scheduler_group_array tests at GATE level in parallel..."
	TEST_LEVEL=GATE $(PYTEST) test_beats_scheduler_group_array.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-sched-arr-gate-parallel-waves
run-sched-arr-gate-parallel-waves:
	@echo "Running beats_scheduler_group_array tests at GATE level parallel with waveforms..."
	WAVES=1 TEST_LEVEL=GATE $(PYTEST) test_beats_scheduler_group_array.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FUNC level
.PHONY: run-sched-arr-func
run-sched-arr-func:
	@echo "Running beats_scheduler_group_array tests at FUNC level..."
	TEST_LEVEL=FUNC $(PYTEST) test_beats_scheduler_group_array.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sched-arr-func-waves
run-sched-arr-func-waves:
	@echo "Running beats_scheduler_group_array tests at FUNC level with waveforms..."
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) test_beats_scheduler_group_array.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sched-arr-func-parallel
run-sched-arr-func-parallel:
	@echo "Running beats_scheduler_group_array tests at FUNC level in parallel..."
	TEST_LEVEL=FUNC $(PYTEST) test_beats_scheduler_group_array.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-sched-arr-func-parallel-waves
run-sched-arr-func-parallel-waves:
	@echo "Running beats_scheduler_group_array tests at FUNC level parallel with waveforms..."
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) test_beats_scheduler_group_array.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FULL level
.PHONY: run-sched-arr-full
run-sched-arr-full:
	@echo "Running beats_scheduler_group_array tests at FULL level..."
	TEST_LEVEL=FULL $(PYTEST) test_beats_scheduler_group_array.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sched-arr-full-waves
run-sched-arr-full-waves:
	@echo "Running beats_scheduler_group_array tests at FULL level with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) test_beats_scheduler_group_array.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sched-arr-full-parallel
run-sched-arr-full-parallel:
	@echo "Running beats_scheduler_group_array tests at FULL level in parallel..."
	TEST_LEVEL=FULL $(PYTEST) test_beats_scheduler_group_array.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-sched-arr-full-parallel-waves
run-sched-arr-full-parallel-waves:
	@echo "Running beats_scheduler_group_array tests at FULL level parallel with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) test_beats_scheduler_group_array.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# Sink Datapath Targets (test_sink_datapath.py)
# ==============================================================================

# GATE level
.PHONY: run-sink-dp-gate
run-sink-dp-gate:
	@echo "Running sink_datapath tests at GATE level..."
	TEST_LEVEL=GATE $(PYTEST) test_sink_datapath.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sink-dp-gate-waves
run-sink-dp-gate-waves:
	@echo "Running sink_datapath tests at GATE level with waveforms..."
	WAVES=1 TEST_LEVEL=GATE $(PYTEST) test_sink_datapath.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sink-dp-gate-parallel
run-sink-dp-gate-parallel:
	@echo "Running sink_datapath tests at GATE level in parallel..."
	TEST_LEVEL=GATE $(PYTEST) test_sink_datapath.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-sink-dp-gate-parallel-waves
run-sink-dp-gate-parallel-waves:
	@echo "Running sink_datapath tests at GATE level parallel with waveforms..."
	WAVES=1 TEST_LEVEL=GATE $(PYTEST) test_sink_datapath.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FUNC level
.PHONY: run-sink-dp-func
run-sink-dp-func:
	@echo "Running sink_datapath tests at FUNC level..."
	TEST_LEVEL=FUNC $(PYTEST) test_sink_datapath.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sink-dp-func-waves
run-sink-dp-func-waves:
	@echo "Running sink_datapath tests at FUNC level with waveforms..."
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) test_sink_datapath.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sink-dp-func-parallel
run-sink-dp-func-parallel:
	@echo "Running sink_datapath tests at FUNC level in parallel..."
	TEST_LEVEL=FUNC $(PYTEST) test_sink_datapath.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-sink-dp-func-parallel-waves
run-sink-dp-func-parallel-waves:
	@echo "Running sink_datapath tests at FUNC level parallel with waveforms..."
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) test_sink_datapath.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FULL level
.PHONY: run-sink-dp-full
run-sink-dp-full:
	@echo "Running sink_datapath tests at FULL level..."
	TEST_LEVEL=FULL $(PYTEST) test_sink_datapath.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sink-dp-full-waves
run-sink-dp-full-waves:
	@echo "Running sink_datapath tests at FULL level with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) test_sink_datapath.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sink-dp-full-parallel
run-sink-dp-full-parallel:
	@echo "Running sink_datapath tests at FULL level in parallel..."
	TEST_LEVEL=FULL $(PYTEST) test_sink_datapath.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-sink-dp-full-parallel-waves
run-sink-dp-full-parallel-waves:
	@echo "Running sink_datapath tests at FULL level parallel with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) test_sink_datapath.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# Source Datapath Targets (test_source_datapath.py)
# ==============================================================================

# GATE level
.PHONY: run-source-dp-gate
run-source-dp-gate:
	@echo "Running source_datapath tests at GATE level..."
	TEST_LEVEL=GATE $(PYTEST) test_source_datapath.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-source-dp-gate-waves
run-source-dp-gate-waves:
	@echo "Running source_datapath tests at GATE level with waveforms..."
	WAVES=1 TEST_LEVEL=GATE $(PYTEST) test_source_datapath.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-source-dp-gate-parallel
run-source-dp-gate-parallel:
	@echo "Running source_datapath tests at GATE level in parallel..."
	TEST_LEVEL=GATE $(PYTEST) test_source_datapath.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-source-dp-gate-parallel-waves
run-source-dp-gate-parallel-waves:
	@echo "Running source_datapath tests at GATE level parallel with waveforms..."
	WAVES=1 TEST_LEVEL=GATE $(PYTEST) test_source_datapath.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FUNC level
.PHONY: run-source-dp-func
run-source-dp-func:
	@echo "Running source_datapath tests at FUNC level..."
	TEST_LEVEL=FUNC $(PYTEST) test_source_datapath.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-source-dp-func-waves
run-source-dp-func-waves:
	@echo "Running source_datapath tests at FUNC level with waveforms..."
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) test_source_datapath.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-source-dp-func-parallel
run-source-dp-func-parallel:
	@echo "Running source_datapath tests at FUNC level in parallel..."
	TEST_LEVEL=FUNC $(PYTEST) test_source_datapath.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-source-dp-func-parallel-waves
run-source-dp-func-parallel-waves:
	@echo "Running source_datapath tests at FUNC level parallel with waveforms..."
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) test_source_datapath.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FULL level
.PHONY: run-source-dp-full
run-source-dp-full:
	@echo "Running source_datapath tests at FULL level..."
	TEST_LEVEL=FULL $(PYTEST) test_source_datapath.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-source-dp-full-waves
run-source-dp-full-waves:
	@echo "Running source_datapath tests at FULL level with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) test_source_datapath.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-source-dp-full-parallel
run-source-dp-full-parallel:
	@echo "Running source_datapath tests at FULL level in parallel..."
	TEST_LEVEL=FULL $(PYTEST) test_source_datapath.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-source-dp-full-parallel-waves
run-source-dp-full-parallel-waves:
	@echo "Running source_datapath tests at FULL level parallel with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) test_source_datapath.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# Sink Data Path AXIS Targets (test_sink_data_path_axis_test.py)
# ==============================================================================

# GATE level
.PHONY: run-sink-axis-gate
run-sink-axis-gate:
	@echo "Running sink_data_path_axis tests at GATE level..."
	TEST_LEVEL=GATE $(PYTEST) test_sink_data_path_axis_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sink-axis-gate-waves
run-sink-axis-gate-waves:
	@echo "Running sink_data_path_axis tests at GATE level with waveforms..."
	WAVES=1 TEST_LEVEL=GATE $(PYTEST) test_sink_data_path_axis_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sink-axis-gate-parallel
run-sink-axis-gate-parallel:
	@echo "Running sink_data_path_axis tests at GATE level in parallel..."
	TEST_LEVEL=GATE $(PYTEST) test_sink_data_path_axis_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FUNC level
.PHONY: run-sink-axis-func
run-sink-axis-func:
	@echo "Running sink_data_path_axis tests at FUNC level..."
	TEST_LEVEL=FUNC $(PYTEST) test_sink_data_path_axis_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sink-axis-func-waves
run-sink-axis-func-waves:
	@echo "Running sink_data_path_axis tests at FUNC level with waveforms..."
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) test_sink_data_path_axis_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sink-axis-func-parallel
run-sink-axis-func-parallel:
	@echo "Running sink_data_path_axis tests at FUNC level in parallel..."
	TEST_LEVEL=FUNC $(PYTEST) test_sink_data_path_axis_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FULL level
.PHONY: run-sink-axis-full
run-sink-axis-full:
	@echo "Running sink_data_path_axis tests at FULL level..."
	TEST_LEVEL=FULL $(PYTEST) test_sink_data_path_axis_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sink-axis-full-waves
run-sink-axis-full-waves:
	@echo "Running sink_data_path_axis tests at FULL level with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) test_sink_data_path_axis_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-sink-axis-full-parallel
run-sink-axis-full-parallel:
	@echo "Running sink_data_path_axis tests at FULL level in parallel..."
	TEST_LEVEL=FULL $(PYTEST) test_sink_data_path_axis_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# Source Data Path AXIS Targets (test_source_data_path_axis_test.py)
# ==============================================================================

# GATE level
.PHONY: run-source-axis-gate
run-source-axis-gate:
	@echo "Running source_data_path_axis tests at GATE level..."
	TEST_LEVEL=GATE $(PYTEST) test_source_data_path_axis_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-source-axis-gate-waves
run-source-axis-gate-waves:
	@echo "Running source_data_path_axis tests at GATE level with waveforms..."
	WAVES=1 TEST_LEVEL=GATE $(PYTEST) test_source_data_path_axis_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-source-axis-gate-parallel
run-source-axis-gate-parallel:
	@echo "Running source_data_path_axis tests at GATE level in parallel..."
	TEST_LEVEL=GATE $(PYTEST) test_source_data_path_axis_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FUNC level
.PHONY: run-source-axis-func
run-source-axis-func:
	@echo "Running source_data_path_axis tests at FUNC level..."
	TEST_LEVEL=FUNC $(PYTEST) test_source_data_path_axis_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-source-axis-func-waves
run-source-axis-func-waves:
	@echo "Running source_data_path_axis tests at FUNC level with waveforms..."
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) test_source_data_path_axis_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-source-axis-func-parallel
run-source-axis-func-parallel:
	@echo "Running source_data_path_axis tests at FUNC level in parallel..."
	TEST_LEVEL=FUNC $(PYTEST) test_source_data_path_axis_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FULL level
.PHONY: run-source-axis-full
run-source-axis-full:
	@echo "Running source_data_path_axis tests at FULL level..."
	TEST_LEVEL=FULL $(PYTEST) test_source_data_path_axis_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-source-axis-full-waves
run-source-axis-full-waves:
	@echo "Running source_data_path_axis tests at FULL level with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) test_source_data_path_axis_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-source-axis-full-parallel
run-source-axis-full-parallel:
	@echo "Running source_data_path_axis tests at FULL level in parallel..."
	TEST_LEVEL=FULL $(PYTEST) test_source_data_path_axis_test.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# SNK SRAM Controller Targets (test_snk_sram_controller.py)
# ==============================================================================

# GATE level
.PHONY: run-snk-sram-gate
run-snk-sram-gate:
	@echo "Running snk_sram_controller tests at GATE level..."
	TEST_LEVEL=GATE $(PYTEST) test_snk_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-snk-sram-gate-waves
run-snk-sram-gate-waves:
	@echo "Running snk_sram_controller tests at GATE level with waveforms..."
	WAVES=1 TEST_LEVEL=GATE $(PYTEST) test_snk_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-snk-sram-gate-parallel
run-snk-sram-gate-parallel:
	@echo "Running snk_sram_controller tests at GATE level in parallel..."
	TEST_LEVEL=GATE $(PYTEST) test_snk_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FUNC level
.PHONY: run-snk-sram-func
run-snk-sram-func:
	@echo "Running snk_sram_controller tests at FUNC level..."
	TEST_LEVEL=FUNC $(PYTEST) test_snk_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-snk-sram-func-waves
run-snk-sram-func-waves:
	@echo "Running snk_sram_controller tests at FUNC level with waveforms..."
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) test_snk_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-snk-sram-func-parallel
run-snk-sram-func-parallel:
	@echo "Running snk_sram_controller tests at FUNC level in parallel..."
	TEST_LEVEL=FUNC $(PYTEST) test_snk_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FULL level
.PHONY: run-snk-sram-full
run-snk-sram-full:
	@echo "Running snk_sram_controller tests at FULL level..."
	TEST_LEVEL=FULL $(PYTEST) test_snk_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-snk-sram-full-waves
run-snk-sram-full-waves:
	@echo "Running snk_sram_controller tests at FULL level with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) test_snk_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-snk-sram-full-parallel
run-snk-sram-full-parallel:
	@echo "Running snk_sram_controller tests at FULL level in parallel..."
	TEST_LEVEL=FULL $(PYTEST) test_snk_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# SRC SRAM Controller Targets (test_src_sram_controller.py)
# ==============================================================================

# GATE level
.PHONY: run-src-sram-gate
run-src-sram-gate:
	@echo "Running src_sram_controller tests at GATE level..."
	TEST_LEVEL=GATE $(PYTEST) test_src_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-src-sram-gate-waves
run-src-sram-gate-waves:
	@echo "Running src_sram_controller tests at GATE level with waveforms..."
	WAVES=1 TEST_LEVEL=GATE $(PYTEST) test_src_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-src-sram-gate-parallel
run-src-sram-gate-parallel:
	@echo "Running src_sram_controller tests at GATE level in parallel..."
	TEST_LEVEL=GATE $(PYTEST) test_src_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FUNC level
.PHONY: run-src-sram-func
run-src-sram-func:
	@echo "Running src_sram_controller tests at FUNC level..."
	TEST_LEVEL=FUNC $(PYTEST) test_src_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-src-sram-func-waves
run-src-sram-func-waves:
	@echo "Running src_sram_controller tests at FUNC level with waveforms..."
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) test_src_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-src-sram-func-parallel
run-src-sram-func-parallel:
	@echo "Running src_sram_controller tests at FUNC level in parallel..."
	TEST_LEVEL=FUNC $(PYTEST) test_src_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FULL level
.PHONY: run-src-sram-full
run-src-sram-full:
	@echo "Running src_sram_controller tests at FULL level..."
	TEST_LEVEL=FULL $(PYTEST) test_src_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-src-sram-full-waves
run-src-sram-full-waves:
	@echo "Running src_sram_controller tests at FULL level with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) test_src_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-src-sram-full-parallel
run-src-sram-full-parallel:
	@echo "Running src_sram_controller tests at FULL level in parallel..."
	TEST_LEVEL=FULL $(PYTEST) test_src_sram_controller.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# Combined Targets (All Tests)
# ==============================================================================

# Test files list (only existing test files)
ALL_TESTS = test_beats_scheduler_group.py test_beats_scheduler_group_array.py \
            test_sink_data_path_axis_test.py test_source_data_path_axis_test.py \
            test_snk_sram_controller.py test_src_sram_controller.py

# GATE level
.PHONY: run-all-gate
run-all-gate:
	@echo "Running all tests at GATE level..."
	TEST_LEVEL=GATE $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-all-gate-waves
run-all-gate-waves:
	@echo "Running all tests at GATE level with waveforms..."
	WAVES=1 TEST_LEVEL=GATE $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-all-gate-parallel
run-all-gate-parallel:
	@echo "Running all tests at GATE level in parallel..."
	TEST_LEVEL=GATE $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FUNC level
.PHONY: run-all-func
run-all-func:
	@echo "Running all tests at FUNC level..."
	TEST_LEVEL=FUNC $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-all-func-waves
run-all-func-waves:
	@echo "Running all tests at FUNC level with waveforms..."
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-all-func-parallel
run-all-func-parallel:
	@echo "Running all tests at FUNC level in parallel..."
	TEST_LEVEL=FUNC $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FULL level
.PHONY: run-all-full
run-all-full:
	@echo "Running ALL tests at FULL level..."
	TEST_LEVEL=FULL $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-all-full-waves
run-all-full-waves:
	@echo "Running ALL tests at FULL level with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-all-full-parallel
run-all-full-parallel:
	@echo "Running ALL tests at FULL level in parallel..."
	TEST_LEVEL=FULL $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-all-full-parallel-waves
run-all-full-parallel-waves:
	@echo "Running ALL tests at FULL level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# Utility Targets
# ==============================================================================

.PHONY: collect-sched-grp
collect-sched-grp:
	@echo "Collecting beats_scheduler_group tests..."
	$(PYTEST) test_beats_scheduler_group.py --collect-only

.PHONY: collect-sched-arr
collect-sched-arr:
	@echo "Collecting beats_scheduler_group_array tests..."
	$(PYTEST) test_beats_scheduler_group_array.py --collect-only

.PHONY: collect-sink-dp
collect-sink-dp:
	@echo "Collecting sink_datapath tests..."
	$(PYTEST) test_sink_datapath.py --collect-only

.PHONY: collect-source-dp
collect-source-dp:
	@echo "Collecting source_datapath tests..."
	$(PYTEST) test_source_datapath.py --collect-only

.PHONY: collect-sink-axis
collect-sink-axis:
	@echo "Collecting sink_data_path_axis tests..."
	$(PYTEST) test_sink_data_path_axis_test.py --collect-only

.PHONY: collect-source-axis
collect-source-axis:
	@echo "Collecting source_data_path_axis tests..."
	$(PYTEST) test_source_data_path_axis_test.py --collect-only

.PHONY: collect-snk-sram
collect-snk-sram:
	@echo "Collecting snk_sram_controller tests..."
	$(PYTEST) test_snk_sram_controller.py --collect-only

.PHONY: collect-src-sram
collect-src-sram:
	@echo "Collecting src_sram_controller tests..."
	$(PYTEST) test_src_sram_controller.py --collect-only

.PHONY: clean
clean:
	@echo "Cleaning local artifacts..."
	rm -rf __pycache__ .pytest_cache *.pyc

.PHONY: clean-all
clean-all: clean
	@echo "Cleaning all test artifacts..."
	rm -rf local_sim_build logs
	find . -name "*.vcd" -delete
	find . -name "*.log" -delete
