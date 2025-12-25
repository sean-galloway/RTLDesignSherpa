# ==============================================================================
# AMBA Subsystem Test Makefile
# ==============================================================================
#
# PREREQUISITES:
#   Must be run with sourced environment:
#     source $REPO_ROOT/env_python  # Sets $REPO_ROOT and activates venv
#     cd $REPO_ROOT/val/amba
#     make <target>
#
# Quick start:
#   make help           - Show all available targets
#   make run-all        - Run all AMBA tests
#   make run-apb        - Run all APB tests
#   make run-axi4       - Run all AXI4 tests
#   make run-axil4      - Run all AXI4-Lite tests
#   make clean-all      - Clean all test artifacts
#
# Advanced:
#   make run-all-parallel   - Run all tests in parallel (logical cores)
#   make run-apb-parallel   - Run APB tests in parallel
#   make run-axi4-parallel  - Run AXI4 tests in parallel
#   make collect-all        - Collect (don't run) all tests
#   make status             - Show test status and coverage
#
# ==============================================================================

# Force bash shell (required for source command)
SHELL := /bin/bash

# Check if REPO_ROOT is set (from env_python)
ifndef REPO_ROOT
$(error REPO_ROOT is not set. Please run: source $$REPO_ROOT/env_python)
endif

# Repository root comes from environment (set by env_python)
# No path calculation needed - works from any project location!

# Pytest options
PYTEST = python3 -m pytest
PYTEST_VERBOSE = -v
PYTEST_QUIET = -q
PYTEST_XDIST = -n 48  # parallel workers (48 with unique test names)
PYTEST_TBSTYLE = --tb=short
PYTEST_RERUNS = --reruns 3 --reruns-delay 1  # retry failed tests up to 3 times with 1s delay

# Default target - show help
.DEFAULT_GOAL := help

# ==============================================================================
# Help Target
# ==============================================================================

.PHONY: help
help:
	@echo "================================================================================"
	@echo "AMBA Test Makefile - Available Targets"
	@echo "================================================================================"
	@echo ""
	@echo "MASTER REGRESSION TARGETS (Recommended):"
	@echo "  make run-amba-gate            GATE: 73 tests (~1 hr) - Quick smoke"
	@echo "  make run-amba-func            FUNC: 160 tests (~4 hr) - Daily regression"
	@echo "  make run-amba-full            FULL: 582 tests (~30 hr) - Weekly regression"
	@echo "  make run-amba-gate-parallel   GATE parallel (~20 min)"
	@echo "  make run-amba-func-parallel   FUNC parallel (~1.5 hr)"
	@echo "  make run-amba-full-parallel   FULL parallel (~10 hr)"
	@echo ""
	@echo "  Coverage: GAXI, AXI4 (core+monitors), AXIL4 (core+monitors)"
	@echo ""
	@echo "RUN TARGETS (by Protocol):"
	@echo "  make run-apb              Run all APB protocol tests"
	@echo "  make run-apb-parallel     Run APB tests in parallel"
	@echo "  make run-axi4             Run all AXI4 full protocol tests"
	@echo "  make run-axi4-parallel    Run AXI4 tests in parallel"
	@echo "  make run-axil4            Run all AXI4-Lite protocol tests"
	@echo "  make run-axil4-parallel   Run AXI4-Lite tests in parallel"
	@echo "  make run-axi5             Run all AXI5 protocol tests"
	@echo "  make run-axi5-parallel    Run AXI5 tests in parallel"
	@echo "  make run-axis             Run all AXI-Stream (AXIS4) tests"
	@echo "  make run-axis-parallel    Run AXI-Stream tests in parallel"
	@echo "  make run-axis5            Run all AXIS5 protocol tests"
	@echo "  make run-axis5-parallel   Run AXIS5 tests in parallel"
	@echo "  make run-apb5             Run all APB5 protocol tests"
	@echo "  make run-apb5-parallel    Run APB5 tests in parallel"
	@echo "  make run-all              Run all AMBA tests"
	@echo "  make run-all-parallel     Run all tests in parallel"
	@echo ""
	@echo "AMBA VERSION TARGETS (group by protocol version):"
	@echo "  make run-amba4            Run all AMBA4 tests (APB+AXI4+AXIL4+AXIS)"
	@echo "  make run-amba4-parallel   Run AMBA4 tests in parallel"
	@echo "  make run-amba5            Run all AMBA5 tests (APB5+AXI5+AXIS5)"
	@echo "  make run-amba5-parallel   Run AMBA5 tests in parallel"
	@echo ""
	@echo "  AMBA4 REG_LEVEL targets:"
	@echo "    make run-amba4-gate / run-amba4-gate-parallel"
	@echo "    make run-amba4-func / run-amba4-func-parallel"
	@echo "    make run-amba4-full / run-amba4-full-parallel"
	@echo ""
	@echo "  AMBA5 REG_LEVEL targets:"
	@echo "    make run-amba5-gate / run-amba5-gate-parallel"
	@echo "    make run-amba5-func / run-amba5-func-parallel"
	@echo "    make run-amba5-full / run-amba5-full-parallel"
	@echo ""
	@echo "REG_LEVEL TARGETS (configurable test depth for ALL tests):"
	@echo "  GATE = Quick smoke tests, FUNC = Default, FULL = Comprehensive"
	@echo ""
	@echo "  Serial execution:"
	@echo "    make run-all-{gate|func|full}"
	@echo "  Parallel execution (recommended):"
	@echo "    make run-all-{gate|func|full}-parallel"
	@echo ""
	@echo "RUN TARGETS (by Function):"
	@echo "  make run-monitors         Run all monitor tests (AXI4/AXIL4)"
	@echo "  make run-monitors-parallel Run monitor tests in parallel"
	@echo "  make run-arbiters         Run all arbiter tests"
	@echo "  make run-arbiters-parallel Run arbiter tests in parallel"
	@echo "  make run-splitters        Run all AXI splitter tests"
	@echo "  make run-splitters-parallel Run splitter tests in parallel"
	@echo "  make run-gaxi             Run all GAXI (Generic AXI) tests"
	@echo "  make run-gaxi-parallel    Run GAXI tests in parallel"
	@echo ""
	@echo "  GAXI Buffer Tests (skid/fifo/regslice):"
	@echo "  make run-gaxi-gate        GATE: 7 tests (~5 min)"
	@echo "  make run-gaxi-func        FUNC: 19 tests (~20 min)"
	@echo "  make run-gaxi-full        FULL: 126 tests (~2 hr)"
	@echo "  make run-gaxi-gate-parallel   GATE parallel (~2 min)"
	@echo "  make run-gaxi-func-parallel   FUNC parallel (~8 min)"
	@echo "  make run-gaxi-full-parallel   FULL parallel (~45 min)"
	@echo ""
	@echo "  ALL GAXI Tests (buffers + async + drop FIFOs):"
	@echo "  make run-gaxi-all-gate       GATE: 15 tests (~15 min)"
	@echo "  make run-gaxi-all-func       FUNC: 38 tests (~90 min)"
	@echo "  make run-gaxi-all-full       FULL: 192 tests (~8 hr)"
	@echo "  make run-gaxi-all-gate-parallel  GATE parallel (~5 min)"
	@echo "  make run-gaxi-all-func-parallel  FUNC parallel (~25 min)"
	@echo "  make run-gaxi-all-full-parallel  FULL parallel (~2 hr)"
	@echo ""
	@echo "  AXI4 Master Tests (rd+wr):"
	@echo "  make run-axi4-master-gate       GATE: 4 tests (~4 min)"
	@echo "  make run-axi4-master-func       FUNC: 16 tests (~30 min)"
	@echo "  make run-axi4-master-full       FULL: 96 tests (~3 hr)"
	@echo "  make run-axi4-master-gate-parallel  GATE parallel (~2 min)"
	@echo "  make run-axi4-master-func-parallel  FUNC parallel (~12 min)"
	@echo "  make run-axi4-master-full-parallel  FULL parallel (~1 hr)"
	@echo ""
	@echo "  AXI4 Slave Tests (rd+wr):"
	@echo "  make run-axi4-slave-gate        GATE: 4 tests (~4 min)"
	@echo "  make run-axi4-slave-func        FUNC: 16 tests (~30 min)"
	@echo "  make run-axi4-slave-full        FULL: 96 tests (~3 hr)"
	@echo "  make run-axi4-slave-gate-parallel   GATE parallel (~2 min)"
	@echo "  make run-axi4-slave-func-parallel   FUNC parallel (~12 min)"
	@echo "  make run-axi4-slave-full-parallel   FULL parallel (~1 hr)"
	@echo ""
	@echo "  ALL AXI4 Core Tests (master+slave):"
	@echo "  make run-axi4-all-gate          GATE: 8 tests (~8 min)"
	@echo "  make run-axi4-all-func          FUNC: 32 tests (~60 min)"
	@echo "  make run-axi4-all-full          FULL: 192 tests (~6 hr)"
	@echo "  make run-axi4-all-gate-parallel     GATE parallel (~4 min)"
	@echo "  make run-axi4-all-func-parallel     FUNC parallel (~24 min)"
	@echo "  make run-axi4-all-full-parallel     FULL parallel (~2 hr)"
	@echo ""
	@echo "  AXI4 Monitor Master Tests (rd+wr, base+CG):"
	@echo "  make run-axi4-mon-master-gate       GATE: 5 tests (~5 min)"
	@echo "  make run-axi4-mon-master-func       FUNC: 13 tests (~45 min)"
	@echo "  make run-axi4-mon-master-full       FULL: 37 tests (~4 hr)"
	@echo "  make run-axi4-mon-master-gate-parallel  GATE parallel (~2 min)"
	@echo "  make run-axi4-mon-master-func-parallel  FUNC parallel (~18 min)"
	@echo "  make run-axi4-mon-master-full-parallel  FULL parallel (~1.5 hr)"
	@echo ""
	@echo "  AXI4 Monitor Slave Tests (rd+wr, base+CG):"
	@echo "  make run-axi4-mon-slave-gate        GATE: 4 tests (~5 min)"
	@echo "  make run-axi4-mon-slave-func        FUNC: 12 tests (~45 min)"
	@echo "  make run-axi4-mon-slave-full        FULL: 36 tests (~4 hr)"
	@echo "  make run-axi4-mon-slave-gate-parallel   GATE parallel (~2 min)"
	@echo "  make run-axi4-mon-slave-func-parallel   FUNC parallel (~18 min)"
	@echo "  make run-axi4-mon-slave-full-parallel   FULL parallel (~1.5 hr)"
	@echo ""
	@echo "  ALL AXI4 Monitor Tests (master+slave, all 8 files):"
	@echo "  make run-axi4-mon-all-gate          GATE: 9 tests (~10 min)"
	@echo "  make run-axi4-mon-all-func          FUNC: 25 tests (~90 min)"
	@echo "  make run-axi4-mon-all-full          FULL: 73 tests (~8 hr)"
	@echo "  make run-axi4-mon-all-gate-parallel     GATE parallel (~4 min)"
	@echo "  make run-axi4-mon-all-func-parallel     FUNC parallel (~35 min)"
	@echo "  make run-axi4-mon-all-full-parallel     FULL parallel (~3 hr)"
	@echo ""
	@echo "  make run-cdc              Run CDC (Clock Domain Crossing) tests"
	@echo "  make run-cdc-parallel     Run CDC tests in parallel"
	@echo "  make run-utils            Run utility tests (clock gate, PeakRDL)"
	@echo "  make run-utils-parallel   Run utility tests in parallel"
	@echo ""
	@echo "RUN TARGETS (Individual Protocols):"
	@echo "  make run-apb-master       Run APB master tests only"
	@echo "  make run-apb-slave        Run APB slave tests only"
	@echo "  make run-apb-monitor      Run APB monitor tests only"
	@echo "  make run-axi4-master      Run AXI4 master tests (rd + wr)"
	@echo "  make run-axi4-master-parallel  Run AXI4 master tests in parallel"
	@echo "  make run-axi4-slave       Run AXI4 slave tests (rd + wr)"
	@echo "  make run-axi4-slave-parallel   Run AXI4 slave tests in parallel"
	@echo "  make run-axil4-master     Run AXI4-Lite master tests (rd + wr)"
	@echo "  make run-axil4-master-parallel Run AXI4-Lite master tests in parallel"
	@echo "  make run-axil4-slave      Run AXI4-Lite slave tests (rd + wr)"
	@echo "  make run-axil4-slave-parallel  Run AXI4-Lite slave tests in parallel"
	@echo ""
	@echo "  AXI5 Core Tests (rd+wr):"
	@echo "  make run-axi5-master-gate       GATE: 4 tests (~4 min)"
	@echo "  make run-axi5-master-func       FUNC: 16 tests (~30 min)"
	@echo "  make run-axi5-master-full       FULL: 96 tests (~3 hr)"
	@echo "  make run-axi5-slave-gate        GATE: 4 tests (~4 min)"
	@echo "  make run-axi5-slave-func        FUNC: 16 tests (~30 min)"
	@echo "  make run-axi5-slave-full        FULL: 96 tests (~3 hr)"
	@echo ""
	@echo "  ALL AXI5 Tests (core+monitors+CG):"
	@echo "  make run-axi5-all-gate          GATE: ~20 tests (~15 min)"
	@echo "  make run-axi5-all-func          FUNC: ~68 tests (~2 hr)"
	@echo "  make run-axi5-all-full          FULL: ~300 tests (~10 hr)"
	@echo "  make run-axi5-all-gate-parallel     GATE parallel (~8 min)"
	@echo "  make run-axi5-all-func-parallel     FUNC parallel (~45 min)"
	@echo "  make run-axi5-all-full-parallel     FULL parallel (~4 hr)"
	@echo ""
	@echo "  AXI5 Monitor Master Tests (rd+wr, base+CG):"
	@echo "  make run-axi5-mon-master-gate       GATE: 4 tests (~5 min)"
	@echo "  make run-axi5-mon-master-func       FUNC: 12 tests (~45 min)"
	@echo "  make run-axi5-mon-master-full       FULL: 36 tests (~4 hr)"
	@echo "  make run-axi5-mon-master-gate-parallel  GATE parallel (~2 min)"
	@echo "  make run-axi5-mon-master-func-parallel  FUNC parallel (~18 min)"
	@echo "  make run-axi5-mon-master-full-parallel  FULL parallel (~1.5 hr)"
	@echo ""
	@echo "  AXI5 Monitor Slave Tests (rd+wr, base+CG):"
	@echo "  make run-axi5-mon-slave-gate        GATE: 4 tests (~5 min)"
	@echo "  make run-axi5-mon-slave-func        FUNC: 12 tests (~45 min)"
	@echo "  make run-axi5-mon-slave-full        FULL: 36 tests (~4 hr)"
	@echo "  make run-axi5-mon-slave-gate-parallel   GATE parallel (~2 min)"
	@echo "  make run-axi5-mon-slave-func-parallel   FUNC parallel (~18 min)"
	@echo "  make run-axi5-mon-slave-full-parallel   FULL parallel (~1.5 hr)"
	@echo ""
	@echo "  ALL AXI5 Monitor Tests (master+slave, all 8 files):"
	@echo "  make run-axi5-mon-all-gate          GATE: 8 tests (~10 min)"
	@echo "  make run-axi5-mon-all-func          FUNC: 24 tests (~90 min)"
	@echo "  make run-axi5-mon-all-full          FULL: 72 tests (~8 hr)"
	@echo "  make run-axi5-mon-all-gate-parallel     GATE parallel (~4 min)"
	@echo "  make run-axi5-mon-all-func-parallel     FUNC parallel (~35 min)"
	@echo "  make run-axi5-mon-all-full-parallel     FULL parallel (~3 hr)"
	@echo ""
	@echo "  AXI5 Clock-Gated Tests (rd+wr, master+slave, no monitors):"
	@echo "  make run-axi5-cg-gate               GATE: 4 tests (~5 min)"
	@echo "  make run-axi5-cg-func               FUNC: 12 tests (~45 min)"
	@echo "  make run-axi5-cg-full               FULL: 36 tests (~4 hr)"
	@echo "  make run-axi5-cg-gate-parallel      GATE parallel (~2 min)"
	@echo "  make run-axi5-cg-func-parallel      FUNC parallel (~18 min)"
	@echo "  make run-axi5-cg-full-parallel      FULL parallel (~1.5 hr)"
	@echo ""
	@echo "  APB5 Tests (master+slave+monitor+CDC+CG+stubs):"
	@echo "  make run-apb5                   Run all APB5 tests"
	@echo "  make run-apb5-parallel          Run APB5 tests in parallel"
	@echo "  make run-apb5-master            Run APB5 master tests"
	@echo "  make run-apb5-slave             Run APB5 slave tests"
	@echo "  make run-apb5-monitor           Run APB5 monitor tests"
	@echo "  make run-apb5-cg                Run APB5 clock-gated tests"
	@echo "  make run-apb5-cdc               Run APB5 CDC tests"
	@echo "  make run-apb5-stub              Run APB5 stub tests"
	@echo ""
	@echo "  AXIS5 Tests (master+slave+CG):"
	@echo "  make run-axis5                  Run all AXIS5 tests"
	@echo "  make run-axis5-parallel         Run AXIS5 tests in parallel"
	@echo "  make run-axis5-master           Run AXIS5 master tests"
	@echo "  make run-axis5-slave            Run AXIS5 slave tests"
	@echo "  make run-axis5-cg               Run AXIS5 clock-gated tests"
	@echo ""
	@echo "COLLECTION TARGETS (verify tests, don't run):"
	@echo "  make collect-apb          Collect APB (AMBA4) tests"
	@echo "  make collect-apb5         Collect APB5 tests"
	@echo "  make collect-axi4         Collect AXI4 tests"
	@echo "  make collect-axil4        Collect AXI4-Lite tests"
	@echo "  make collect-axi5         Collect AXI5 tests"
	@echo "  make collect-axis         Collect AXIS (AMBA4) tests"
	@echo "  make collect-axis5        Collect AXIS5 tests"
	@echo "  make collect-amba4        Collect all AMBA4 tests"
	@echo "  make collect-amba5        Collect all AMBA5 tests"
	@echo "  make collect-all          Collect all tests"
	@echo ""
	@echo "CLEAN TARGETS:"
	@echo "  make clean-all            Remove all test artifacts"
	@echo "  make clean-logs           Remove all log files"
	@echo "  make clean-pycache        Remove Python cache files"
	@echo "  make clean-build          Remove simulation build directories"
	@echo "  make clean-vcd            Remove VCD waveform files"
	@echo ""
	@echo "UTILITY TARGETS:"
	@echo "  make list-apb             List all APB (AMBA4) test modules"
	@echo "  make list-apb5            List all APB5 test modules"
	@echo "  make list-axi4            List all AXI4 test modules"
	@echo "  make list-axil4           List all AXI4-Lite test modules"
	@echo "  make list-axi5            List all AXI5 test modules"
	@echo "  make list-axis            List all AXIS (AMBA4) test modules"
	@echo "  make list-axis5           List all AXIS5 test modules"
	@echo "  make list-amba4           List all AMBA4 test modules"
	@echo "  make list-amba5           List all AMBA5 test modules"
	@echo "  make list-all             List all test modules"
	@echo "  make status               Show test status and coverage"
	@echo ""
	@echo "================================================================================"
	@echo "Prerequisites: source $(REPO_ROOT)/env_python"
	@echo "Current REPO_ROOT: $(REPO_ROOT)"
	@echo "================================================================================"

# ==============================================================================
# Run Targets - By Protocol
# ==============================================================================

.PHONY: run-apb
run-apb:
	@echo "================================================================================"
	@echo "Running AMBA APB Tests"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_apb_*.py

.PHONY: run-apb-parallel
run-apb-parallel:
	@echo "================================================================================"
	@echo "Running AMBA APB Tests (Parallel)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_apb_*.py

.PHONY: run-axi4
run-axi4:
	@echo "================================================================================"
	@echo "Running AMBA AXI4 Full Protocol Tests"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_*.py

.PHONY: run-axi4-parallel
run-axi4-parallel:
	@echo "================================================================================"
	@echo "Running AMBA AXI4 Full Protocol Tests (Parallel)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_axi4_*.py

.PHONY: run-axil4
run-axil4:
	@echo "================================================================================"
	@echo "Running AMBA AXI4-Lite Protocol Tests"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axil4_*.py

.PHONY: run-axil4-parallel
run-axil4-parallel:
	@echo "================================================================================"
	@echo "Running AMBA AXI4-Lite Protocol Tests (Parallel)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_axil4_*.py

.PHONY: run-axis
run-axis:
	@echo "================================================================================"
	@echo "Running AMBA AXI-Stream Protocol Tests"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axis_*.py

.PHONY: run-axis-parallel
run-axis-parallel:
	@echo "================================================================================"
	@echo "Running AMBA AXI-Stream Protocol Tests (Parallel)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_axis_*.py

# =============================================================================
# AXIS5 Protocol Tests
# =============================================================================

.PHONY: run-axis5
run-axis5:
	@echo "================================================================================"
	@echo "Running AMBA AXIS5 Protocol Tests"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axis5_*.py

.PHONY: run-axis5-parallel
run-axis5-parallel:
	@echo "================================================================================"
	@echo "Running AMBA AXIS5 Protocol Tests (Parallel)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_axis5_*.py

.PHONY: run-axis5-master
run-axis5-master:
	@echo "Running AXIS5 master tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axis5_master*.py

.PHONY: run-axis5-slave
run-axis5-slave:
	@echo "Running AXIS5 slave tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axis5_slave*.py

.PHONY: run-axis5-cg
run-axis5-cg:
	@echo "Running AXIS5 clock-gated tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axis5_*_cg.py

# =============================================================================
# APB5 Protocol Tests
# =============================================================================

.PHONY: run-apb5
run-apb5:
	@echo "================================================================================"
	@echo "Running AMBA APB5 Protocol Tests"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_apb5_*.py

.PHONY: run-apb5-parallel
run-apb5-parallel:
	@echo "================================================================================"
	@echo "Running AMBA APB5 Protocol Tests (Parallel)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_apb5_*.py

.PHONY: run-apb5-master
run-apb5-master:
	@echo "Running APB5 master tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_apb5_master.py test_apb5_master_cg.py test_apb5_master_stub.py

.PHONY: run-apb5-slave
run-apb5-slave:
	@echo "Running APB5 slave tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_apb5_slave.py test_apb5_slave_cg.py test_apb5_slave_cdc.py test_apb5_slave_cdc_cg.py test_apb5_slave_stub.py

.PHONY: run-apb5-monitor
run-apb5-monitor:
	@echo "Running APB5 monitor tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_apb5_monitor.py

.PHONY: run-apb5-cg
run-apb5-cg:
	@echo "Running APB5 clock-gated tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_apb5_master_cg.py test_apb5_slave_cg.py test_apb5_slave_cdc_cg.py

.PHONY: run-apb5-cdc
run-apb5-cdc:
	@echo "Running APB5 CDC tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_apb5_slave_cdc.py test_apb5_slave_cdc_cg.py

.PHONY: run-apb5-stub
run-apb5-stub:
	@echo "Running APB5 stub tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_apb5_master_stub.py test_apb5_slave_stub.py

# =============================================================================
# AMBA4 Combined Tests (APB + AXI4 + AXIL4 + AXIS)
# =============================================================================

.PHONY: run-amba4
run-amba4:
	@echo "================================================================================"
	@echo "Running ALL AMBA4 Protocol Tests (APB + AXI4 + AXIL4 + AXIS)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_apb_*.py test_axi4_*.py test_axil4_*.py test_axis_*.py

.PHONY: run-amba4-parallel
run-amba4-parallel:
	@echo "================================================================================"
	@echo "Running ALL AMBA4 Protocol Tests (Parallel)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_apb_*.py test_axi4_*.py test_axil4_*.py test_axis_*.py

# AMBA4 REG_LEVEL Targets
.PHONY: run-amba4-gate
run-amba4-gate:
	@echo "================================================================================"
	@echo "Running AMBA4 Tests at GATE Level (APB + AXI4 + AXIL4 + AXIS)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_apb_*.py test_axi4_*.py test_axil4_*.py test_axis_*.py

.PHONY: run-amba4-func
run-amba4-func:
	@echo "================================================================================"
	@echo "Running AMBA4 Tests at FUNC Level (APB + AXI4 + AXIL4 + AXIS)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_apb_*.py test_axi4_*.py test_axil4_*.py test_axis_*.py

.PHONY: run-amba4-full
run-amba4-full:
	@echo "================================================================================"
	@echo "Running AMBA4 Tests at FULL Level (APB + AXI4 + AXIL4 + AXIS)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_apb_*.py test_axi4_*.py test_axil4_*.py test_axis_*.py

.PHONY: run-amba4-gate-parallel
run-amba4-gate-parallel:
	@echo "================================================================================"
	@echo "Running AMBA4 Tests at GATE Level (Parallel)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_apb_*.py test_axi4_*.py test_axil4_*.py test_axis_*.py

.PHONY: run-amba4-func-parallel
run-amba4-func-parallel:
	@echo "================================================================================"
	@echo "Running AMBA4 Tests at FUNC Level (Parallel)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_apb_*.py test_axi4_*.py test_axil4_*.py test_axis_*.py

.PHONY: run-amba4-full-parallel
run-amba4-full-parallel:
	@echo "================================================================================"
	@echo "Running AMBA4 Tests at FULL Level (Parallel)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_apb_*.py test_axi4_*.py test_axil4_*.py test_axis_*.py

# =============================================================================
# AMBA5 Combined Tests (APB5 + AXI5 + AXIS5)
# =============================================================================

.PHONY: run-amba5
run-amba5:
	@echo "================================================================================"
	@echo "Running ALL AMBA5 Protocol Tests (APB5 + AXI5 + AXIS5)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_apb5_*.py test_axi5_*.py test_axis5_*.py

.PHONY: run-amba5-parallel
run-amba5-parallel:
	@echo "================================================================================"
	@echo "Running ALL AMBA5 Protocol Tests (Parallel)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_apb5_*.py test_axi5_*.py test_axis5_*.py

# AMBA5 REG_LEVEL Targets
.PHONY: run-amba5-gate
run-amba5-gate:
	@echo "================================================================================"
	@echo "Running AMBA5 Tests at GATE Level (APB5 + AXI5 + AXIS5)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_apb5_*.py test_axi5_*.py test_axis5_*.py

.PHONY: run-amba5-func
run-amba5-func:
	@echo "================================================================================"
	@echo "Running AMBA5 Tests at FUNC Level (APB5 + AXI5 + AXIS5)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_apb5_*.py test_axi5_*.py test_axis5_*.py

.PHONY: run-amba5-full
run-amba5-full:
	@echo "================================================================================"
	@echo "Running AMBA5 Tests at FULL Level (APB5 + AXI5 + AXIS5)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_apb5_*.py test_axi5_*.py test_axis5_*.py

.PHONY: run-amba5-gate-parallel
run-amba5-gate-parallel:
	@echo "================================================================================"
	@echo "Running AMBA5 Tests at GATE Level (Parallel)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_apb5_*.py test_axi5_*.py test_axis5_*.py

.PHONY: run-amba5-func-parallel
run-amba5-func-parallel:
	@echo "================================================================================"
	@echo "Running AMBA5 Tests at FUNC Level (Parallel)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_apb5_*.py test_axi5_*.py test_axis5_*.py

.PHONY: run-amba5-full-parallel
run-amba5-full-parallel:
	@echo "================================================================================"
	@echo "Running AMBA5 Tests at FULL Level (Parallel)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_apb5_*.py test_axi5_*.py test_axis5_*.py

# =============================================================================
# Master AMBA Regression Targets (GATE/FUNC/FULL)
# =============================================================================
# These run ALL major AMBA test groups at specified REG_LEVEL
# Includes: GAXI, AXI4 core, AXI4 monitors, AXIL4 core, AXIL4 monitors
# Test counts approximate - exact counts depend on which tests have REG_LEVEL

.PHONY: run-amba-gate
run-amba-gate:
	@echo "================================================================================"
	@echo "Running COMPLETE AMBA Regression at GATE Level (Quick Smoke Test)"
	@echo "================================================================================"
	@echo "Test groups: GAXI, AXI4 (core+monitors), AXIL4 (core+monitors)"
	@echo "Expected: 73 tests (~1 hour)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_gaxi_*.py test_axi4_*.py test_axil4_*.py

.PHONY: run-amba-func
run-amba-func:
	@echo "================================================================================"
	@echo "Running COMPLETE AMBA Regression at FUNC Level (Functional Validation)"
	@echo "================================================================================"
	@echo "Test groups: GAXI, AXI4 (core+monitors), AXIL4 (core+monitors)"
	@echo "Expected: 160 tests (~4 hours)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_gaxi_*.py test_axi4_*.py test_axil4_*.py

.PHONY: run-amba-full
run-amba-full:
	@echo "================================================================================"
	@echo "Running COMPLETE AMBA Regression at FULL Level (Comprehensive Validation)"
	@echo "================================================================================"
	@echo "Test groups: GAXI, AXI4 (core+monitors), AXIL4 (core+monitors)"
	@echo "Expected: 582 tests (~30 hours)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_gaxi_*.py test_axi4_*.py test_axil4_*.py

.PHONY: run-amba-gate-parallel
run-amba-gate-parallel:
	@echo "================================================================================"
	@echo "Running COMPLETE AMBA Regression at GATE Level (Parallel)"
	@echo "Expected: 73 tests (~20 min with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_gaxi_*.py test_axi4_*.py test_axil4_*.py

.PHONY: run-amba-func-parallel
run-amba-func-parallel:
	@echo "================================================================================"
	@echo "Running COMPLETE AMBA Regression at FUNC Level (Parallel)"
	@echo "Expected: 160 tests (~1.5 hours with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_gaxi_*.py test_axi4_*.py test_axil4_*.py

.PHONY: run-amba-full-parallel
run-amba-full-parallel:
	@echo "================================================================================"
	@echo "Running COMPLETE AMBA Regression at FULL Level (Parallel)"
	@echo "Expected: 582 tests (~10 hours with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_gaxi_*.py test_axi4_*.py test_axil4_*.py

.PHONY: run-all
run-all:
	@echo "================================================================================"
	@echo "Running ALL AMBA Tests (no REG_LEVEL filtering)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-parallel
run-all-parallel:
	@echo "================================================================================"
	@echo "Running ALL AMBA Tests (Parallel - logical cores)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_*.py

# REG_LEVEL Variants - Run all tests with specific regression levels
.PHONY: run-all-gate
run-all-gate:
	@echo "================================================================================"
	@echo "Running ALL AMBA Tests - GATE level (minimal params, ~5-10 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-func
run-all-func:
	@echo "================================================================================"
	@echo "Running ALL AMBA Tests - FUNC level (default params, ~30-60 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-full
run-all-full:
	@echo "================================================================================"
	@echo "Running ALL AMBA Tests - FULL level (comprehensive, ~2-4 hours)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*.py

.PHONY: run-all-gate-parallel
run-all-gate-parallel:
	@echo "================================================================================"
	@echo "Running ALL AMBA Tests - GATE level PARALLEL (~2-3 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_*.py

.PHONY: run-all-func-parallel
run-all-func-parallel:
	@echo "================================================================================"
	@echo "Running ALL AMBA Tests - FUNC level PARALLEL (~10-20 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_*.py

.PHONY: run-all-full-parallel
run-all-full-parallel:
	@echo "================================================================================"
	@echo "Running ALL AMBA Tests - FULL level PARALLEL (~30-60 min)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_*.py

# ==============================================================================
# Run Targets - By Function
# ==============================================================================

.PHONY: run-monitors
run-monitors:
	@echo "Running AMBA monitor tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_*_mon*.py

.PHONY: run-monitors-parallel
run-monitors-parallel:
	@echo "Running AMBA monitor tests (Parallel)..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_*_mon*.py

.PHONY: run-arbiters
run-arbiters:
	@echo "Running AMBA arbiter tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_arbiter_*.py

.PHONY: run-arbiters-parallel
run-arbiters-parallel:
	@echo "Running AMBA arbiter tests (Parallel)..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_arbiter_*.py

.PHONY: run-splitters
run-splitters:
	@echo "Running AXI splitter tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi_*splitter*.py test_axi_split_*.py

.PHONY: run-splitters-parallel
run-splitters-parallel:
	@echo "Running AXI splitter tests (Parallel)..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi_*splitter*.py test_axi_split_*.py

.PHONY: run-gaxi
run-gaxi:
	@echo "Running GAXI (Generic AXI) tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_gaxi_*.py

.PHONY: run-gaxi-parallel
run-gaxi-parallel:
	@echo "Running GAXI (Generic AXI) tests (Parallel)..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_gaxi_*.py

# REG_LEVEL Control for GAXI Buffer Tests
# GATE: Quick smoke test (7 tests, ~5 min)
# FUNC: Functional coverage (19 tests, ~20 min) - default
# FULL: Comprehensive validation (126 tests, ~2 hours)

.PHONY: run-gaxi-gate
run-gaxi-gate:
	@echo "================================================================================"
	@echo "Running GAXI Buffer Tests at GATE level (smoke test)"
	@echo "Tests: test_gaxi_skid_buffer, test_gaxi_fifo_sync, test_gaxi_regslice"
	@echo "Expected: 7 tests (~5 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_gaxi_skid_buffer.py test_gaxi_fifo_sync.py test_gaxi_regslice.py

.PHONY: run-gaxi-func
run-gaxi-func:
	@echo "================================================================================"
	@echo "Running GAXI Buffer Tests at FUNC level (functional coverage)"
	@echo "Tests: test_gaxi_skid_buffer, test_gaxi_fifo_sync, test_gaxi_regslice"
	@echo "Expected: 19 tests (~20 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_gaxi_skid_buffer.py test_gaxi_fifo_sync.py test_gaxi_regslice.py

.PHONY: run-gaxi-full
run-gaxi-full:
	@echo "================================================================================"
	@echo "Running GAXI Buffer Tests at FULL level (comprehensive validation)"
	@echo "Tests: test_gaxi_skid_buffer, test_gaxi_fifo_sync, test_gaxi_regslice"
	@echo "Expected: 126 tests (~2 hours)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_gaxi_skid_buffer.py test_gaxi_fifo_sync.py test_gaxi_regslice.py

# Parallel versions of REG_LEVEL targets
.PHONY: run-gaxi-gate-parallel
run-gaxi-gate-parallel:
	@echo "================================================================================"
	@echo "Running GAXI Buffer Tests at GATE level (parallel)"
	@echo "Tests: test_gaxi_skid_buffer, test_gaxi_fifo_sync, test_gaxi_regslice"
	@echo "Expected: 7 tests (~2 min with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_gaxi_skid_buffer.py test_gaxi_fifo_sync.py test_gaxi_regslice.py

.PHONY: run-gaxi-func-parallel
run-gaxi-func-parallel:
	@echo "================================================================================"
	@echo "Running GAXI Buffer Tests at FUNC level (parallel)"
	@echo "Tests: test_gaxi_skid_buffer, test_gaxi_fifo_sync, test_gaxi_regslice"
	@echo "Expected: 19 tests (~8 min with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_gaxi_skid_buffer.py test_gaxi_fifo_sync.py test_gaxi_regslice.py

.PHONY: run-gaxi-full-parallel
run-gaxi-full-parallel:
	@echo "================================================================================"
	@echo "Running GAXI Buffer Tests at FULL level (parallel)"
	@echo "Tests: test_gaxi_skid_buffer, test_gaxi_fifo_sync, test_gaxi_regslice"
	@echo "Expected: 126 tests (~45 min with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_gaxi_skid_buffer.py test_gaxi_fifo_sync.py test_gaxi_regslice.py

# ALL GAXI Tests (buffers + async + drop FIFOs)
# Total test counts:
#   GATE: 15 tests (~15 min)
#   FUNC: 38 tests (~90 min)
#   FULL: 192 tests (~8 hours)

.PHONY: run-gaxi-all-gate
run-gaxi-all-gate:
	@echo "================================================================================"
	@echo "Running ALL GAXI Tests at GATE level (smoke test)"
	@echo "Tests: buffers (skid/fifo/regslice) + async + drop FIFOs"
	@echo "Expected: 15 tests (~15 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_gaxi_skid_buffer.py test_gaxi_fifo_sync.py test_gaxi_regslice.py test_gaxi_buffer_async.py test_gaxi_drop_fifo_sync.py test_gaxi_drop_fifo_capacity.py

.PHONY: run-gaxi-all-func
run-gaxi-all-func:
	@echo "================================================================================"
	@echo "Running ALL GAXI Tests at FUNC level (functional coverage)"
	@echo "Tests: buffers (skid/fifo/regslice) + async + drop FIFOs"
	@echo "Expected: 38 tests (~90 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_gaxi_skid_buffer.py test_gaxi_fifo_sync.py test_gaxi_regslice.py test_gaxi_buffer_async.py test_gaxi_drop_fifo_sync.py test_gaxi_drop_fifo_capacity.py

.PHONY: run-gaxi-all-full
run-gaxi-all-full:
	@echo "================================================================================"
	@echo "Running ALL GAXI Tests at FULL level (comprehensive validation)"
	@echo "Tests: buffers (skid/fifo/regslice) + async + drop FIFOs"
	@echo "Expected: 192 tests (~8 hours)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_gaxi_skid_buffer.py test_gaxi_fifo_sync.py test_gaxi_regslice.py test_gaxi_buffer_async.py test_gaxi_drop_fifo_sync.py test_gaxi_drop_fifo_capacity.py

# Parallel versions of ALL GAXI tests
.PHONY: run-gaxi-all-gate-parallel
run-gaxi-all-gate-parallel:
	@echo "================================================================================"
	@echo "Running ALL GAXI Tests at GATE level (parallel)"
	@echo "Tests: buffers (skid/fifo/regslice) + async + drop FIFOs"
	@echo "Expected: 15 tests (~5 min with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_gaxi_skid_buffer.py test_gaxi_fifo_sync.py test_gaxi_regslice.py test_gaxi_buffer_async.py test_gaxi_drop_fifo_sync.py test_gaxi_drop_fifo_capacity.py

.PHONY: run-gaxi-all-func-parallel
run-gaxi-all-func-parallel:
	@echo "================================================================================"
	@echo "Running ALL GAXI Tests at FUNC level (parallel)"
	@echo "Tests: buffers (skid/fifo/regslice) + async + drop FIFOs"
	@echo "Expected: 38 tests (~25 min with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_gaxi_skid_buffer.py test_gaxi_fifo_sync.py test_gaxi_regslice.py test_gaxi_buffer_async.py test_gaxi_drop_fifo_sync.py test_gaxi_drop_fifo_capacity.py

.PHONY: run-gaxi-all-full-parallel
run-gaxi-all-full-parallel:
	@echo "================================================================================"
	@echo "Running ALL GAXI Tests at FULL level (parallel)"
	@echo "Tests: buffers (skid/fifo/regslice) + async + drop FIFOs"
	@echo "Expected: 96 tests (~1 hour with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_gaxi_skid_buffer.py test_gaxi_fifo_sync.py test_gaxi_regslice.py test_gaxi_buffer_async.py test_gaxi_drop_fifo_sync.py test_gaxi_drop_fifo_capacity.py

# =============================================================================
# AXI4 Core Tests (Master + Slave, Read + Write)
# =============================================================================
# Test counts:
#   Master (rd+wr): GATE=4, FUNC=16, FULL=96
#   Slave (rd+wr):  GATE=4, FUNC=16, FULL=96
#   ALL AXI4:       GATE=8, FUNC=32, FULL=192

# AXI4 Master Tests (Read + Write)
.PHONY: run-axi4-master-gate
run-axi4-master-gate:
	@echo "================================================================================"
	@echo "Running AXI4 Master Tests at GATE level (smoke test)"
	@echo "Tests: test_axi4_master_rd, test_axi4_master_wr"
	@echo "Expected: 4 tests (~4 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_master_rd.py test_axi4_master_wr.py

.PHONY: run-axi4-master-func
run-axi4-master-func:
	@echo "================================================================================"
	@echo "Running AXI4 Master Tests at FUNC level (functional coverage)"
	@echo "Tests: test_axi4_master_rd, test_axi4_master_wr"
	@echo "Expected: 16 tests (~30 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_master_rd.py test_axi4_master_wr.py

.PHONY: run-axi4-master-full
run-axi4-master-full:
	@echo "================================================================================"
	@echo "Running AXI4 Master Tests at FULL level (comprehensive validation)"
	@echo "Tests: test_axi4_master_rd, test_axi4_master_wr"
	@echo "Expected: 96 tests (~3 hours)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_master_rd.py test_axi4_master_wr.py

.PHONY: run-axi4-master-gate-parallel
run-axi4-master-gate-parallel:
	@echo "================================================================================"
	@echo "Running AXI4 Master Tests at GATE level (parallel)"
	@echo "Tests: test_axi4_master_rd, test_axi4_master_wr"
	@echo "Expected: 4 tests (~2 min with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi4_master_rd.py test_axi4_master_wr.py

.PHONY: run-axi4-master-func-parallel
run-axi4-master-func-parallel:
	@echo "================================================================================"
	@echo "Running AXI4 Master Tests at FUNC level (parallel)"
	@echo "Tests: test_axi4_master_rd, test_axi4_master_wr"
	@echo "Expected: 16 tests (~12 min with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi4_master_rd.py test_axi4_master_wr.py

.PHONY: run-axi4-master-full-parallel
run-axi4-master-full-parallel:
	@echo "================================================================================"
	@echo "Running AXI4 Master Tests at FULL level (parallel)"
	@echo "Tests: test_axi4_master_rd, test_axi4_master_wr"
	@echo "Expected: 96 tests (~1 hour with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi4_master_rd.py test_axi4_master_wr.py

# AXI4 Slave Tests (Read + Write)
.PHONY: run-axi4-slave-gate
run-axi4-slave-gate:
	@echo "================================================================================"
	@echo "Running AXI4 Slave Tests at GATE level (smoke test)"
	@echo "Tests: test_axi4_slave_rd, test_axi4_slave_wr"
	@echo "Expected: 4 tests (~4 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_slave_rd.py test_axi4_slave_wr.py

.PHONY: run-axi4-slave-func
run-axi4-slave-func:
	@echo "================================================================================"
	@echo "Running AXI4 Slave Tests at FUNC level (functional coverage)"
	@echo "Tests: test_axi4_slave_rd, test_axi4_slave_wr"
	@echo "Expected: 16 tests (~30 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_slave_rd.py test_axi4_slave_wr.py

.PHONY: run-axi4-slave-full
run-axi4-slave-full:
	@echo "================================================================================"
	@echo "Running AXI4 Slave Tests at FULL level (comprehensive validation)"
	@echo "Tests: test_axi4_slave_rd, test_axi4_slave_wr"
	@echo "Expected: 96 tests (~3 hours)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_slave_rd.py test_axi4_slave_wr.py

.PHONY: run-axi4-slave-gate-parallel
run-axi4-slave-gate-parallel:
	@echo "================================================================================"
	@echo "Running AXI4 Slave Tests at GATE level (parallel)"
	@echo "Tests: test_axi4_slave_rd, test_axi4_slave_wr"
	@echo "Expected: 4 tests (~2 min with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi4_slave_rd.py test_axi4_slave_wr.py

.PHONY: run-axi4-slave-func-parallel
run-axi4-slave-func-parallel:
	@echo "================================================================================"
	@echo "Running AXI4 Slave Tests at FUNC level (parallel)"
	@echo "Tests: test_axi4_slave_rd, test_axi4_slave_wr"
	@echo "Expected: 16 tests (~12 min with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi4_slave_rd.py test_axi4_slave_wr.py

.PHONY: run-axi4-slave-full-parallel
run-axi4-slave-full-parallel:
	@echo "================================================================================"
	@echo "Running AXI4 Slave Tests at FULL level (parallel)"
	@echo "Tests: test_axi4_slave_rd, test_axi4_slave_wr"
	@echo "Expected: 96 tests (~1 hour with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi4_slave_rd.py test_axi4_slave_wr.py

# ALL AXI4 Core Tests (Master + Slave, Read + Write)
.PHONY: run-axi4-all-gate
run-axi4-all-gate:
	@echo "================================================================================"
	@echo "Running ALL AXI4 Core Tests at GATE level (smoke test)"
	@echo "Tests: master (rd+wr) + slave (rd+wr)"
	@echo "Expected: 8 tests (~8 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_master_rd.py test_axi4_master_wr.py test_axi4_slave_rd.py test_axi4_slave_wr.py

.PHONY: run-axi4-all-func
run-axi4-all-func:
	@echo "================================================================================"
	@echo "Running ALL AXI4 Core Tests at FUNC level (functional coverage)"
	@echo "Tests: master (rd+wr) + slave (rd+wr)"
	@echo "Expected: 32 tests (~60 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_master_rd.py test_axi4_master_wr.py test_axi4_slave_rd.py test_axi4_slave_wr.py

.PHONY: run-axi4-all-full
run-axi4-all-full:
	@echo "================================================================================"
	@echo "Running ALL AXI4 Core Tests at FULL level (comprehensive validation)"
	@echo "Tests: master (rd+wr) + slave (rd+wr)"
	@echo "Expected: 192 tests (~6 hours)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_master_rd.py test_axi4_master_wr.py test_axi4_slave_rd.py test_axi4_slave_wr.py

.PHONY: run-axi4-all-gate-parallel
run-axi4-all-gate-parallel:
	@echo "================================================================================"
	@echo "Running ALL AXI4 Core Tests at GATE level (parallel)"
	@echo "Tests: master (rd+wr) + slave (rd+wr)"
	@echo "Expected: 8 tests (~4 min with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi4_master_rd.py test_axi4_master_wr.py test_axi4_slave_rd.py test_axi4_slave_wr.py

.PHONY: run-axi4-all-func-parallel
run-axi4-all-func-parallel:
	@echo "================================================================================"
	@echo "Running ALL AXI4 Core Tests at FUNC level (parallel)"
	@echo "Tests: master (rd+wr) + slave (rd+wr)"
	@echo "Expected: 32 tests (~24 min with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi4_master_rd.py test_axi4_master_wr.py test_axi4_slave_rd.py test_axi4_slave_wr.py

.PHONY: run-axi4-all-full-parallel
run-axi4-all-full-parallel:
	@echo "================================================================================"
	@echo "Running ALL AXI4 Core Tests at FULL level (parallel)"
	@echo "Tests: master (rd+wr) + slave (rd+wr)"
	@echo "Expected: 192 tests (~2 hours with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi4_master_rd.py test_axi4_master_wr.py test_axi4_slave_rd.py test_axi4_slave_wr.py

# =============================================================================
# AXI4 Monitor Tests (Master + Slave, Read + Write, base + CG versions)
# =============================================================================
# Test counts (8 monitor test files, each has test + wavedrom):
#   Master (rd+wr+rd_cg+wr_cg): GATE=4+1, FUNC=12+1, FULL=36+1 (wavedrom only in non-CG rd)
#   Slave (rd+wr+rd_cg+wr_cg):  GATE=4+1, FUNC=12+1, FULL=36+1
#   ALL Monitors:               GATE=9, FUNC=25, FULL=73

# AXI4 Monitor Master Tests (Read + Write, base + CG)
.PHONY: run-axi4-mon-master-gate
run-axi4-mon-master-gate:
	@echo "================================================================================"
	@echo "Running AXI4 Master Monitor Tests at GATE level (smoke test)"
	@echo "Tests: test_axi4_master_rd_mon, test_axi4_master_rd_mon_cg, test_axi4_master_wr_mon, test_axi4_master_wr_mon_cg"
	@echo "Expected: 5 tests (~5 min) - 4 monitor + 1 wavedrom"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_master_rd_mon.py test_axi4_master_rd_mon_cg.py test_axi4_master_wr_mon.py test_axi4_master_wr_mon_cg.py

.PHONY: run-axi4-mon-master-func
run-axi4-mon-master-func:
	@echo "================================================================================"
	@echo "Running AXI4 Master Monitor Tests at FUNC level (functional coverage)"
	@echo "Tests: test_axi4_master_rd_mon, test_axi4_master_rd_mon_cg, test_axi4_master_wr_mon, test_axi4_master_wr_mon_cg"
	@echo "Expected: 13 tests (~45 min) - 12 monitor + 1 wavedrom"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_master_rd_mon.py test_axi4_master_rd_mon_cg.py test_axi4_master_wr_mon.py test_axi4_master_wr_mon_cg.py

.PHONY: run-axi4-mon-master-full
run-axi4-mon-master-full:
	@echo "================================================================================"
	@echo "Running AXI4 Master Monitor Tests at FULL level (comprehensive validation)"
	@echo "Tests: test_axi4_master_rd_mon, test_axi4_master_rd_mon_cg, test_axi4_master_wr_mon, test_axi4_master_wr_mon_cg"
	@echo "Expected: 37 tests (~4 hours) - 36 monitor + 1 wavedrom"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_master_rd_mon.py test_axi4_master_rd_mon_cg.py test_axi4_master_wr_mon.py test_axi4_master_wr_mon_cg.py

.PHONY: run-axi4-mon-master-gate-parallel
run-axi4-mon-master-gate-parallel:
	@echo "================================================================================"
	@echo "Running AXI4 Master Monitor Tests at GATE level (parallel)"
	@echo "Expected: 5 tests (~2 min with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi4_master_rd_mon.py test_axi4_master_rd_mon_cg.py test_axi4_master_wr_mon.py test_axi4_master_wr_mon_cg.py

.PHONY: run-axi4-mon-master-func-parallel
run-axi4-mon-master-func-parallel:
	@echo "================================================================================"
	@echo "Running AXI4 Master Monitor Tests at FUNC level (parallel)"
	@echo "Expected: 13 tests (~18 min with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi4_master_rd_mon.py test_axi4_master_rd_mon_cg.py test_axi4_master_wr_mon.py test_axi4_master_wr_mon_cg.py

.PHONY: run-axi4-mon-master-full-parallel
run-axi4-mon-master-full-parallel:
	@echo "================================================================================"
	@echo "Running AXI4 Master Monitor Tests at FULL level (parallel)"
	@echo "Expected: 37 tests (~1.5 hours with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi4_master_rd_mon.py test_axi4_master_rd_mon_cg.py test_axi4_master_wr_mon.py test_axi4_master_wr_mon_cg.py

# AXI4 Monitor Slave Tests (Read + Write, base + CG)
.PHONY: run-axi4-mon-slave-gate
run-axi4-mon-slave-gate:
	@echo "================================================================================"
	@echo "Running AXI4 Slave Monitor Tests at GATE level (smoke test)"
	@echo "Tests: test_axi4_slave_rd_mon, test_axi4_slave_rd_mon_cg, test_axi4_slave_wr_mon, test_axi4_slave_wr_mon_cg"
	@echo "Expected: 4 tests (~5 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_slave_rd_mon.py test_axi4_slave_rd_mon_cg.py test_axi4_slave_wr_mon.py test_axi4_slave_wr_mon_cg.py

.PHONY: run-axi4-mon-slave-func
run-axi4-mon-slave-func:
	@echo "================================================================================"
	@echo "Running AXI4 Slave Monitor Tests at FUNC level (functional coverage)"
	@echo "Tests: test_axi4_slave_rd_mon, test_axi4_slave_rd_mon_cg, test_axi4_slave_wr_mon, test_axi4_slave_wr_mon_cg"
	@echo "Expected: 12 tests (~45 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_slave_rd_mon.py test_axi4_slave_rd_mon_cg.py test_axi4_slave_wr_mon.py test_axi4_slave_wr_mon_cg.py

.PHONY: run-axi4-mon-slave-full
run-axi4-mon-slave-full:
	@echo "================================================================================"
	@echo "Running AXI4 Slave Monitor Tests at FULL level (comprehensive validation)"
	@echo "Tests: test_axi4_slave_rd_mon, test_axi4_slave_rd_mon_cg, test_axi4_slave_wr_mon, test_axi4_slave_wr_mon_cg"
	@echo "Expected: 36 tests (~4 hours)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_slave_rd_mon.py test_axi4_slave_rd_mon_cg.py test_axi4_slave_wr_mon.py test_axi4_slave_wr_mon_cg.py

.PHONY: run-axi4-mon-slave-gate-parallel
run-axi4-mon-slave-gate-parallel:
	@echo "================================================================================"
	@echo "Running AXI4 Slave Monitor Tests at GATE level (parallel)"
	@echo "Expected: 4 tests (~2 min with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi4_slave_rd_mon.py test_axi4_slave_rd_mon_cg.py test_axi4_slave_wr_mon.py test_axi4_slave_wr_mon_cg.py

.PHONY: run-axi4-mon-slave-func-parallel
run-axi4-mon-slave-func-parallel:
	@echo "================================================================================"
	@echo "Running AXI4 Slave Monitor Tests at FUNC level (parallel)"
	@echo "Expected: 12 tests (~18 min with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi4_slave_rd_mon.py test_axi4_slave_rd_mon_cg.py test_axi4_slave_wr_mon.py test_axi4_slave_wr_mon_cg.py

.PHONY: run-axi4-mon-slave-full-parallel
run-axi4-mon-slave-full-parallel:
	@echo "================================================================================"
	@echo "Running AXI4 Slave Monitor Tests at FULL level (parallel)"
	@echo "Expected: 36 tests (~1.5 hours with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi4_slave_rd_mon.py test_axi4_slave_rd_mon_cg.py test_axi4_slave_wr_mon.py test_axi4_slave_wr_mon_cg.py

# ALL AXI4 Monitor Tests (Master + Slave, all 8 files)
.PHONY: run-axi4-mon-all-gate
run-axi4-mon-all-gate:
	@echo "================================================================================"
	@echo "Running ALL AXI4 Monitor Tests at GATE level (smoke test)"
	@echo "Tests: master (rd+wr+rd_cg+wr_cg) + slave (rd+wr+rd_cg+wr_cg)"
	@echo "Expected: 9 tests (~10 min) - 8 monitor + 1 wavedrom"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_master_rd_mon.py test_axi4_master_rd_mon_cg.py test_axi4_master_wr_mon.py test_axi4_master_wr_mon_cg.py test_axi4_slave_rd_mon.py test_axi4_slave_rd_mon_cg.py test_axi4_slave_wr_mon.py test_axi4_slave_wr_mon_cg.py

.PHONY: run-axi4-mon-all-func
run-axi4-mon-all-func:
	@echo "================================================================================"
	@echo "Running ALL AXI4 Monitor Tests at FUNC level (functional coverage)"
	@echo "Tests: master (rd+wr+rd_cg+wr_cg) + slave (rd+wr+rd_cg+wr_cg)"
	@echo "Expected: 25 tests (~90 min) - 24 monitor + 1 wavedrom"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_master_rd_mon.py test_axi4_master_rd_mon_cg.py test_axi4_master_wr_mon.py test_axi4_master_wr_mon_cg.py test_axi4_slave_rd_mon.py test_axi4_slave_rd_mon_cg.py test_axi4_slave_wr_mon.py test_axi4_slave_wr_mon_cg.py

.PHONY: run-axi4-mon-all-full
run-axi4-mon-all-full:
	@echo "================================================================================"
	@echo "Running ALL AXI4 Monitor Tests at FULL level (comprehensive validation)"
	@echo "Tests: master (rd+wr+rd_cg+wr_cg) + slave (rd+wr+rd_cg+wr_cg)"
	@echo "Expected: 73 tests (~8 hours) - 72 monitor + 1 wavedrom"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_master_rd_mon.py test_axi4_master_rd_mon_cg.py test_axi4_master_wr_mon.py test_axi4_master_wr_mon_cg.py test_axi4_slave_rd_mon.py test_axi4_slave_rd_mon_cg.py test_axi4_slave_wr_mon.py test_axi4_slave_wr_mon_cg.py

.PHONY: run-axi4-mon-all-gate-parallel
run-axi4-mon-all-gate-parallel:
	@echo "================================================================================"
	@echo "Running ALL AXI4 Monitor Tests at GATE level (parallel)"
	@echo "Expected: 9 tests (~4 min with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi4_master_rd_mon.py test_axi4_master_rd_mon_cg.py test_axi4_master_wr_mon.py test_axi4_master_wr_mon_cg.py test_axi4_slave_rd_mon.py test_axi4_slave_rd_mon_cg.py test_axi4_slave_wr_mon.py test_axi4_slave_wr_mon_cg.py

.PHONY: run-axi4-mon-all-func-parallel
run-axi4-mon-all-func-parallel:
	@echo "================================================================================"
	@echo "Running ALL AXI4 Monitor Tests at FUNC level (parallel)"
	@echo "Expected: 25 tests (~35 min with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi4_master_rd_mon.py test_axi4_master_rd_mon_cg.py test_axi4_master_wr_mon.py test_axi4_master_wr_mon_cg.py test_axi4_slave_rd_mon.py test_axi4_slave_rd_mon_cg.py test_axi4_slave_wr_mon.py test_axi4_slave_wr_mon_cg.py

.PHONY: run-axi4-mon-all-full-parallel
run-axi4-mon-all-full-parallel:
	@echo "================================================================================"
	@echo "Running ALL AXI4 Monitor Tests at FULL level (parallel)"
	@echo "Expected: 73 tests (~3 hours with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi4_master_rd_mon.py test_axi4_master_rd_mon_cg.py test_axi4_master_wr_mon.py test_axi4_master_wr_mon_cg.py test_axi4_slave_rd_mon.py test_axi4_slave_rd_mon_cg.py test_axi4_slave_wr_mon.py test_axi4_slave_wr_mon_cg.py

.PHONY: run-cdc
run-cdc:
	@echo "Running CDC (Clock Domain Crossing) tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_cdc_*.py test_*_cdc*.py

.PHONY: run-cdc-parallel
run-cdc-parallel:
	@echo "Running CDC (Clock Domain Crossing) tests (Parallel)..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_cdc_*.py test_*_cdc*.py

.PHONY: run-utils
run-utils:
	@echo "Running utility tests (clock gate, PeakRDL)..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_amba_clock_gate*.py test_peakrdl*.py

.PHONY: run-utils-parallel
run-utils-parallel:
	@echo "Running utility tests (clock gate, PeakRDL) (Parallel)..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_amba_clock_gate*.py test_peakrdl*.py

# ==============================================================================
# Run Targets - Individual Protocol Components
# ==============================================================================

.PHONY: run-apb-master
run-apb-master:
	@echo "Running APB master tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_apb_master.py

.PHONY: run-apb-slave
run-apb-slave:
	@echo "Running APB slave tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_apb_slave*.py

.PHONY: run-apb-monitor
run-apb-monitor:
	@echo "Running APB monitor tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_apb_monitor.py

.PHONY: run-axi4-master
run-axi4-master:
	@echo "Running AXI4 master tests (read + write)..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_master_*.py

.PHONY: run-axi4-master-parallel
run-axi4-master-parallel:
	@echo "Running AXI4 master tests (Parallel)..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi4_master_*.py

.PHONY: run-axi4-slave
run-axi4-slave:
	@echo "Running AXI4 slave tests (read + write)..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_slave_*.py

.PHONY: run-axi4-slave-parallel
run-axi4-slave-parallel:
	@echo "Running AXI4 slave tests (Parallel)..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi4_slave_*.py

.PHONY: run-axi4-master-rd
run-axi4-master-rd:
	@echo "Running AXI4 master read tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_master_rd*.py

.PHONY: run-axi4-master-wr
run-axi4-master-wr:
	@echo "Running AXI4 master write tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_master_wr*.py

.PHONY: run-axi4-slave-rd
run-axi4-slave-rd:
	@echo "Running AXI4 slave read tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_slave_rd*.py

.PHONY: run-axi4-slave-wr
run-axi4-slave-wr:
	@echo "Running AXI4 slave write tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi4_slave_wr*.py

.PHONY: run-axil4-master
run-axil4-master:
	@echo "Running AXI4-Lite master tests (read + write)..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axil4_master_*.py

.PHONY: run-axil4-master-parallel
run-axil4-master-parallel:
	@echo "Running AXI4-Lite master tests (Parallel)..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axil4_master_*.py

.PHONY: run-axil4-slave
run-axil4-slave:
	@echo "Running AXI4-Lite slave tests (read + write)..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axil4_slave_*.py

.PHONY: run-axil4-slave-parallel
run-axil4-slave-parallel:
	@echo "Running AXI4-Lite slave tests (Parallel)..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axil4_slave_*.py

# ==============================================================================
# Collection Targets (verify tests without running)
# ==============================================================================

.PHONY: collect-apb
collect-apb:
	@echo "Collecting AMBA APB tests..."
	$(PYTEST) --collect-only test_apb_*.py

.PHONY: collect-axi4
collect-axi4:
	@echo "Collecting AMBA AXI4 tests..."
	$(PYTEST) --collect-only test_axi4_*.py

.PHONY: collect-axil4
collect-axil4:
	@echo "Collecting AMBA AXI4-Lite tests..."
	$(PYTEST) --collect-only test_axil4_*.py

.PHONY: collect-axis
collect-axis:
	@echo "Collecting AMBA AXI-Stream tests..."
	$(PYTEST) --collect-only test_axis_*.py

.PHONY: collect-axi5
collect-axi5:
	@echo "Collecting AMBA AXI5 tests..."
	$(PYTEST) --collect-only test_axi5_*.py

.PHONY: collect-axis5
collect-axis5:
	@echo "Collecting AMBA AXIS5 tests..."
	$(PYTEST) --collect-only test_axis5_*.py

.PHONY: collect-apb5
collect-apb5:
	@echo "Collecting AMBA APB5 tests..."
	$(PYTEST) --collect-only test_apb5_*.py

.PHONY: collect-amba4
collect-amba4:
	@echo "Collecting ALL AMBA4 tests (APB + AXI4 + AXIL4 + AXIS)..."
	$(PYTEST) --collect-only test_apb_*.py test_axi4_*.py test_axil4_*.py test_axis_*.py

.PHONY: collect-amba5
collect-amba5:
	@echo "Collecting ALL AMBA5 tests (APB5 + AXI5 + AXIS5)..."
	$(PYTEST) --collect-only test_apb5_*.py test_axi5_*.py test_axis5_*.py

.PHONY: collect-all
collect-all:
	@echo "Collecting ALL AMBA tests..."
	$(PYTEST) --collect-only test_*.py

# ==============================================================================
# Clean Targets
# ==============================================================================

.PHONY: clean-logs
clean-logs:
	@echo "Cleaning all log files..."
	rm -rf logs/
	find . -type f -name "*.log" -delete
	@echo "✓ Log files cleaned"

.PHONY: clean-pycache
clean-pycache:
	@echo "Cleaning Python cache files..."
	find . -type d -name "__pycache__" -exec rm -rf {} + 2>/dev/null || true
	find . -type f -name "*.pyc" -delete
	@echo "✓ Python cache cleaned"

.PHONY: clean-build
clean-build:
	@echo "Cleaning simulation build directories..."
	rm -rf local_sim_build/
	rm -rf sim_build/
	find . -type d -name "local_sim_build" -exec rm -rf {} + 2>/dev/null || true
	find . -type d -name "sim_build" -exec rm -rf {} + 2>/dev/null || true
	@echo "✓ Build directories cleaned"

.PHONY: clean-vcd
clean-vcd:
	@echo "Cleaning VCD waveform files..."
	find . -type f -name "*.vcd" -delete
	find . -type f -name "*.fst" -delete
	@echo "✓ Waveform files cleaned"

.PHONY: clean-all
clean-all: clean-logs clean-pycache clean-build clean-vcd
	@echo "================================================================================"
	@echo "✓ All AMBA test artifacts cleaned"
	@echo "================================================================================"

# ==============================================================================
# Utility Targets
# ==============================================================================

.PHONY: list-apb
list-apb:
	@echo "AMBA APB Test Modules:"
	@ls test_apb_*.py 2>/dev/null | sort

.PHONY: list-axi4
list-axi4:
	@echo "AMBA AXI4 Test Modules:"
	@ls test_axi4_*.py 2>/dev/null | sort

.PHONY: list-axil4
list-axil4:
	@echo "AMBA AXI4-Lite Test Modules:"
	@ls test_axil4_*.py 2>/dev/null | sort

.PHONY: list-axis
list-axis:
	@echo "AMBA AXI-Stream Test Modules:"
	@ls test_axis_*.py 2>/dev/null | sort

.PHONY: list-axi5
list-axi5:
	@echo "AMBA AXI5 Test Modules:"
	@ls test_axi5_*.py 2>/dev/null | sort

.PHONY: list-axis5
list-axis5:
	@echo "AMBA AXIS5 Test Modules:"
	@ls test_axis5_*.py 2>/dev/null | sort

.PHONY: list-apb5
list-apb5:
	@echo "AMBA APB5 Test Modules:"
	@ls test_apb5_*.py 2>/dev/null | sort

.PHONY: list-amba4
list-amba4:
	@echo "ALL AMBA4 Test Modules (APB + AXI4 + AXIL4 + AXIS):"
	@ls test_apb_*.py test_axi4_*.py test_axil4_*.py test_axis_*.py 2>/dev/null | sort

.PHONY: list-amba5
list-amba5:
	@echo "ALL AMBA5 Test Modules (APB5 + AXI5 + AXIS5):"
	@ls test_apb5_*.py test_axi5_*.py test_axis5_*.py 2>/dev/null | sort

.PHONY: list-all
list-all:
	@echo "All AMBA Test Modules:"
	@ls test_*.py 2>/dev/null | sort

.PHONY: status
status:
	@echo "================================================================================"
	@echo "AMBA Test Status"
	@echo "================================================================================"
	@echo "Test directories:"
	@echo "  Val/AMBA:    $(REPO_ROOT)/val/amba/"
	@echo ""
	@echo "Test modules found:"
	@echo ""
	@echo "  AMBA4 Protocols:"
	@echo -n "    APB:         "
	@ls test_apb_*.py 2>/dev/null | wc -l
	@echo -n "    AXI4:        "
	@ls test_axi4_*.py 2>/dev/null | wc -l
	@echo -n "    AXI4-Lite:   "
	@ls test_axil4_*.py 2>/dev/null | wc -l
	@echo -n "    AXIS:        "
	@ls test_axis_*.py 2>/dev/null | wc -l
	@echo ""
	@echo "  AMBA5 Protocols:"
	@echo -n "    APB5:        "
	@ls test_apb5_*.py 2>/dev/null | wc -l
	@echo -n "    AXI5:        "
	@ls test_axi5_*.py 2>/dev/null | wc -l
	@echo -n "    AXIS5:       "
	@ls test_axis5_*.py 2>/dev/null | wc -l
	@echo ""
	@echo "  Infrastructure:"
	@echo -n "    Arbiters:    "
	@ls test_arbiter_*.py 2>/dev/null | wc -l
	@echo -n "    GAXI:        "
	@ls test_gaxi_*.py 2>/dev/null | wc -l
	@echo ""
	@echo -n "  Total:         "
	@ls test_*.py 2>/dev/null | wc -l
	@echo ""
	@echo "Build artifacts:"
	@echo -n "  local_sim_build dirs: "
	@find . -type d -name "local_sim_build" 2>/dev/null | wc -l
	@echo -n "  Log files:            "
	@find . -type f -name "*.log" 2>/dev/null | wc -l
	@echo -n "  VCD files:            "
	@find . -type f -name "*.vcd" 2>/dev/null | wc -l
	@echo ""
	@echo "Python environment:"
	@echo "  REPO_ROOT: $(REPO_ROOT)"
	@echo "  Virtual env: $(REPO_ROOT)/env_python"
	@echo "================================================================================"

# =============================================================================
# AXI5 Tests (Master + Slave, Read + Write)
# =============================================================================
# Test counts:
#   Master (rd+wr): GATE=4, FUNC=16, FULL=96
#   Slave (rd+wr):  GATE=4, FUNC=16, FULL=96
#   ALL AXI5:       GATE=8, FUNC=32, FULL=192

.PHONY: run-axi5
run-axi5:
	@echo "================================================================================"
	@echo "Running AMBA AXI5 Protocol Tests"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi5_*.py

.PHONY: run-axi5-parallel
run-axi5-parallel:
	@echo "================================================================================"
	@echo "Running AMBA AXI5 Protocol Tests (Parallel)"
	@echo "================================================================================"
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS) test_axi5_*.py

# AXI5 Master Tests (Read + Write)
.PHONY: run-axi5-master
run-axi5-master:
	@echo "Running AXI5 master tests (read + write)..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi5_master_*.py

.PHONY: run-axi5-master-parallel
run-axi5-master-parallel:
	@echo "Running AXI5 master tests (Parallel)..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi5_master_*.py

.PHONY: run-axi5-master-gate
run-axi5-master-gate:
	@echo "================================================================================"
	@echo "Running AXI5 Master Tests at GATE level (smoke test)"
	@echo "Tests: test_axi5_master_rd, test_axi5_master_wr"
	@echo "Expected: 4 tests (~4 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi5_master_rd.py test_axi5_master_wr.py

.PHONY: run-axi5-master-func
run-axi5-master-func:
	@echo "================================================================================"
	@echo "Running AXI5 Master Tests at FUNC level (functional coverage)"
	@echo "Tests: test_axi5_master_rd, test_axi5_master_wr"
	@echo "Expected: 16 tests (~30 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi5_master_rd.py test_axi5_master_wr.py

.PHONY: run-axi5-master-full
run-axi5-master-full:
	@echo "================================================================================"
	@echo "Running AXI5 Master Tests at FULL level (comprehensive validation)"
	@echo "Tests: test_axi5_master_rd, test_axi5_master_wr"
	@echo "Expected: 96 tests (~3 hours)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi5_master_rd.py test_axi5_master_wr.py

.PHONY: run-axi5-master-gate-parallel
run-axi5-master-gate-parallel:
	@echo "================================================================================"
	@echo "Running AXI5 Master Tests at GATE level (parallel)"
	@echo "Tests: test_axi5_master_rd, test_axi5_master_wr"
	@echo "Expected: 4 tests (~2 min with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi5_master_rd.py test_axi5_master_wr.py

.PHONY: run-axi5-master-func-parallel
run-axi5-master-func-parallel:
	@echo "================================================================================"
	@echo "Running AXI5 Master Tests at FUNC level (parallel)"
	@echo "Tests: test_axi5_master_rd, test_axi5_master_wr"
	@echo "Expected: 16 tests (~12 min with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi5_master_rd.py test_axi5_master_wr.py

.PHONY: run-axi5-master-full-parallel
run-axi5-master-full-parallel:
	@echo "================================================================================"
	@echo "Running AXI5 Master Tests at FULL level (parallel)"
	@echo "Tests: test_axi5_master_rd, test_axi5_master_wr"
	@echo "Expected: 96 tests (~1 hour with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi5_master_rd.py test_axi5_master_wr.py

# AXI5 Slave Tests (Read + Write)
.PHONY: run-axi5-slave
run-axi5-slave:
	@echo "Running AXI5 slave tests (read + write)..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi5_slave_*.py

.PHONY: run-axi5-slave-parallel
run-axi5-slave-parallel:
	@echo "Running AXI5 slave tests (Parallel)..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi5_slave_*.py

.PHONY: run-axi5-slave-gate
run-axi5-slave-gate:
	@echo "================================================================================"
	@echo "Running AXI5 Slave Tests at GATE level (smoke test)"
	@echo "Tests: test_axi5_slave_rd, test_axi5_slave_wr"
	@echo "Expected: 4 tests (~4 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi5_slave_rd.py test_axi5_slave_wr.py

.PHONY: run-axi5-slave-func
run-axi5-slave-func:
	@echo "================================================================================"
	@echo "Running AXI5 Slave Tests at FUNC level (functional coverage)"
	@echo "Tests: test_axi5_slave_rd, test_axi5_slave_wr"
	@echo "Expected: 16 tests (~30 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi5_slave_rd.py test_axi5_slave_wr.py

.PHONY: run-axi5-slave-full
run-axi5-slave-full:
	@echo "================================================================================"
	@echo "Running AXI5 Slave Tests at FULL level (comprehensive validation)"
	@echo "Tests: test_axi5_slave_rd, test_axi5_slave_wr"
	@echo "Expected: 96 tests (~3 hours)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi5_slave_rd.py test_axi5_slave_wr.py

.PHONY: run-axi5-slave-gate-parallel
run-axi5-slave-gate-parallel:
	@echo "================================================================================"
	@echo "Running AXI5 Slave Tests at GATE level (parallel)"
	@echo "Tests: test_axi5_slave_rd, test_axi5_slave_wr"
	@echo "Expected: 4 tests (~2 min with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi5_slave_rd.py test_axi5_slave_wr.py

.PHONY: run-axi5-slave-func-parallel
run-axi5-slave-func-parallel:
	@echo "================================================================================"
	@echo "Running AXI5 Slave Tests at FUNC level (parallel)"
	@echo "Tests: test_axi5_slave_rd, test_axi5_slave_wr"
	@echo "Expected: 16 tests (~12 min with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi5_slave_rd.py test_axi5_slave_wr.py

.PHONY: run-axi5-slave-full-parallel
run-axi5-slave-full-parallel:
	@echo "================================================================================"
	@echo "Running AXI5 Slave Tests at FULL level (parallel)"
	@echo "Tests: test_axi5_slave_rd, test_axi5_slave_wr"
	@echo "Expected: 96 tests (~1 hour with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi5_slave_rd.py test_axi5_slave_wr.py

# ALL AXI5 Tests (Master + Slave, Read + Write)
.PHONY: run-axi5-all-gate
run-axi5-all-gate:
	@echo "================================================================================"
	@echo "Running ALL AXI5 Tests at GATE level (smoke test)"
	@echo "Tests: master (rd+wr) + slave (rd+wr) + monitors + CG"
	@echo "Expected: ~20 tests (~15 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi5_*.py

.PHONY: run-axi5-all-func
run-axi5-all-func:
	@echo "================================================================================"
	@echo "Running ALL AXI5 Tests at FUNC level (functional coverage)"
	@echo "Tests: master (rd+wr) + slave (rd+wr) + monitors + CG"
	@echo "Expected: ~68 tests (~2 hr)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi5_*.py

.PHONY: run-axi5-all-full
run-axi5-all-full:
	@echo "================================================================================"
	@echo "Running ALL AXI5 Tests at FULL level (comprehensive validation)"
	@echo "Tests: master (rd+wr) + slave (rd+wr) + monitors + CG"
	@echo "Expected: ~300 tests (~10 hours)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi5_*.py

.PHONY: run-axi5-all-gate-parallel
run-axi5-all-gate-parallel:
	@echo "================================================================================"
	@echo "Running ALL AXI5 Tests at GATE level (parallel)"
	@echo "Tests: master (rd+wr) + slave (rd+wr) + monitors + CG"
	@echo "Expected: ~20 tests (~8 min with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi5_*.py

.PHONY: run-axi5-all-func-parallel
run-axi5-all-func-parallel:
	@echo "================================================================================"
	@echo "Running ALL AXI5 Tests at FUNC level (parallel)"
	@echo "Tests: master (rd+wr) + slave (rd+wr) + monitors + CG"
	@echo "Expected: ~68 tests (~45 min with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi5_*.py

.PHONY: run-axi5-all-full-parallel
run-axi5-all-full-parallel:
	@echo "================================================================================"
	@echo "Running ALL AXI5 Tests at FULL level (parallel)"
	@echo "Tests: master (rd+wr) + slave (rd+wr) + monitors + CG"
	@echo "Expected: ~300 tests (~4 hours with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi5_*.py

# Individual AXI5 test targets
.PHONY: run-axi5-master-rd
run-axi5-master-rd:
	@echo "Running AXI5 master read tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi5_master_rd.py

.PHONY: run-axi5-master-wr
run-axi5-master-wr:
	@echo "Running AXI5 master write tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi5_master_wr.py

.PHONY: run-axi5-slave-rd
run-axi5-slave-rd:
	@echo "Running AXI5 slave read tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi5_slave_rd.py

.PHONY: run-axi5-slave-wr
run-axi5-slave-wr:
	@echo "Running AXI5 slave write tests..."
	$(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi5_slave_wr.py

# =============================================================================
# AXI5 Monitor Tests (Master + Slave, Read + Write, base + CG versions)
# =============================================================================
# Test counts (8 monitor test files):
#   Master (rd_mon+wr_mon+rd_mon_cg+wr_mon_cg): GATE=4, FUNC=12, FULL=36
#   Slave (rd_mon+wr_mon+rd_mon_cg+wr_mon_cg):  GATE=4, FUNC=12, FULL=36
#   ALL Monitors:                               GATE=8, FUNC=24, FULL=72

# AXI5 Monitor Master Tests (Read + Write, base + CG)
.PHONY: run-axi5-mon-master-gate
run-axi5-mon-master-gate:
	@echo "================================================================================"
	@echo "Running AXI5 Master Monitor Tests at GATE level (smoke test)"
	@echo "Tests: test_axi5_master_rd_mon, test_axi5_master_rd_mon_cg, test_axi5_master_wr_mon, test_axi5_master_wr_mon_cg"
	@echo "Expected: 4 tests (~5 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi5_master_rd_mon.py test_axi5_master_rd_mon_cg.py test_axi5_master_wr_mon.py test_axi5_master_wr_mon_cg.py

.PHONY: run-axi5-mon-master-func
run-axi5-mon-master-func:
	@echo "================================================================================"
	@echo "Running AXI5 Master Monitor Tests at FUNC level (functional coverage)"
	@echo "Tests: test_axi5_master_rd_mon, test_axi5_master_rd_mon_cg, test_axi5_master_wr_mon, test_axi5_master_wr_mon_cg"
	@echo "Expected: 12 tests (~45 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi5_master_rd_mon.py test_axi5_master_rd_mon_cg.py test_axi5_master_wr_mon.py test_axi5_master_wr_mon_cg.py

.PHONY: run-axi5-mon-master-full
run-axi5-mon-master-full:
	@echo "================================================================================"
	@echo "Running AXI5 Master Monitor Tests at FULL level (comprehensive validation)"
	@echo "Tests: test_axi5_master_rd_mon, test_axi5_master_rd_mon_cg, test_axi5_master_wr_mon, test_axi5_master_wr_mon_cg"
	@echo "Expected: 36 tests (~4 hours)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi5_master_rd_mon.py test_axi5_master_rd_mon_cg.py test_axi5_master_wr_mon.py test_axi5_master_wr_mon_cg.py

.PHONY: run-axi5-mon-master-gate-parallel
run-axi5-mon-master-gate-parallel:
	@echo "================================================================================"
	@echo "Running AXI5 Master Monitor Tests at GATE level (parallel)"
	@echo "Expected: 4 tests (~2 min with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi5_master_rd_mon.py test_axi5_master_rd_mon_cg.py test_axi5_master_wr_mon.py test_axi5_master_wr_mon_cg.py

.PHONY: run-axi5-mon-master-func-parallel
run-axi5-mon-master-func-parallel:
	@echo "================================================================================"
	@echo "Running AXI5 Master Monitor Tests at FUNC level (parallel)"
	@echo "Expected: 12 tests (~18 min with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi5_master_rd_mon.py test_axi5_master_rd_mon_cg.py test_axi5_master_wr_mon.py test_axi5_master_wr_mon_cg.py

.PHONY: run-axi5-mon-master-full-parallel
run-axi5-mon-master-full-parallel:
	@echo "================================================================================"
	@echo "Running AXI5 Master Monitor Tests at FULL level (parallel)"
	@echo "Expected: 36 tests (~1.5 hours with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi5_master_rd_mon.py test_axi5_master_rd_mon_cg.py test_axi5_master_wr_mon.py test_axi5_master_wr_mon_cg.py

# AXI5 Monitor Slave Tests (Read + Write, base + CG)
.PHONY: run-axi5-mon-slave-gate
run-axi5-mon-slave-gate:
	@echo "================================================================================"
	@echo "Running AXI5 Slave Monitor Tests at GATE level (smoke test)"
	@echo "Tests: test_axi5_slave_rd_mon, test_axi5_slave_rd_mon_cg, test_axi5_slave_wr_mon, test_axi5_slave_wr_mon_cg"
	@echo "Expected: 4 tests (~5 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi5_slave_rd_mon.py test_axi5_slave_rd_mon_cg.py test_axi5_slave_wr_mon.py test_axi5_slave_wr_mon_cg.py

.PHONY: run-axi5-mon-slave-func
run-axi5-mon-slave-func:
	@echo "================================================================================"
	@echo "Running AXI5 Slave Monitor Tests at FUNC level (functional coverage)"
	@echo "Tests: test_axi5_slave_rd_mon, test_axi5_slave_rd_mon_cg, test_axi5_slave_wr_mon, test_axi5_slave_wr_mon_cg"
	@echo "Expected: 12 tests (~45 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi5_slave_rd_mon.py test_axi5_slave_rd_mon_cg.py test_axi5_slave_wr_mon.py test_axi5_slave_wr_mon_cg.py

.PHONY: run-axi5-mon-slave-full
run-axi5-mon-slave-full:
	@echo "================================================================================"
	@echo "Running AXI5 Slave Monitor Tests at FULL level (comprehensive validation)"
	@echo "Tests: test_axi5_slave_rd_mon, test_axi5_slave_rd_mon_cg, test_axi5_slave_wr_mon, test_axi5_slave_wr_mon_cg"
	@echo "Expected: 36 tests (~4 hours)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi5_slave_rd_mon.py test_axi5_slave_rd_mon_cg.py test_axi5_slave_wr_mon.py test_axi5_slave_wr_mon_cg.py

.PHONY: run-axi5-mon-slave-gate-parallel
run-axi5-mon-slave-gate-parallel:
	@echo "================================================================================"
	@echo "Running AXI5 Slave Monitor Tests at GATE level (parallel)"
	@echo "Expected: 4 tests (~2 min with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi5_slave_rd_mon.py test_axi5_slave_rd_mon_cg.py test_axi5_slave_wr_mon.py test_axi5_slave_wr_mon_cg.py

.PHONY: run-axi5-mon-slave-func-parallel
run-axi5-mon-slave-func-parallel:
	@echo "================================================================================"
	@echo "Running AXI5 Slave Monitor Tests at FUNC level (parallel)"
	@echo "Expected: 12 tests (~18 min with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi5_slave_rd_mon.py test_axi5_slave_rd_mon_cg.py test_axi5_slave_wr_mon.py test_axi5_slave_wr_mon_cg.py

.PHONY: run-axi5-mon-slave-full-parallel
run-axi5-mon-slave-full-parallel:
	@echo "================================================================================"
	@echo "Running AXI5 Slave Monitor Tests at FULL level (parallel)"
	@echo "Expected: 36 tests (~1.5 hours with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi5_slave_rd_mon.py test_axi5_slave_rd_mon_cg.py test_axi5_slave_wr_mon.py test_axi5_slave_wr_mon_cg.py

# ALL AXI5 Monitor Tests (Master + Slave, all 8 files)
.PHONY: run-axi5-mon-all-gate
run-axi5-mon-all-gate:
	@echo "================================================================================"
	@echo "Running ALL AXI5 Monitor Tests at GATE level (smoke test)"
	@echo "Tests: master (rd_mon+wr_mon+rd_mon_cg+wr_mon_cg) + slave (rd_mon+wr_mon+rd_mon_cg+wr_mon_cg)"
	@echo "Expected: 8 tests (~10 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi5_master_rd_mon.py test_axi5_master_rd_mon_cg.py test_axi5_master_wr_mon.py test_axi5_master_wr_mon_cg.py test_axi5_slave_rd_mon.py test_axi5_slave_rd_mon_cg.py test_axi5_slave_wr_mon.py test_axi5_slave_wr_mon_cg.py

.PHONY: run-axi5-mon-all-func
run-axi5-mon-all-func:
	@echo "================================================================================"
	@echo "Running ALL AXI5 Monitor Tests at FUNC level (functional coverage)"
	@echo "Tests: master (rd_mon+wr_mon+rd_mon_cg+wr_mon_cg) + slave (rd_mon+wr_mon+rd_mon_cg+wr_mon_cg)"
	@echo "Expected: 24 tests (~90 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi5_master_rd_mon.py test_axi5_master_rd_mon_cg.py test_axi5_master_wr_mon.py test_axi5_master_wr_mon_cg.py test_axi5_slave_rd_mon.py test_axi5_slave_rd_mon_cg.py test_axi5_slave_wr_mon.py test_axi5_slave_wr_mon_cg.py

.PHONY: run-axi5-mon-all-full
run-axi5-mon-all-full:
	@echo "================================================================================"
	@echo "Running ALL AXI5 Monitor Tests at FULL level (comprehensive validation)"
	@echo "Tests: master (rd_mon+wr_mon+rd_mon_cg+wr_mon_cg) + slave (rd_mon+wr_mon+rd_mon_cg+wr_mon_cg)"
	@echo "Expected: 72 tests (~8 hours)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi5_master_rd_mon.py test_axi5_master_rd_mon_cg.py test_axi5_master_wr_mon.py test_axi5_master_wr_mon_cg.py test_axi5_slave_rd_mon.py test_axi5_slave_rd_mon_cg.py test_axi5_slave_wr_mon.py test_axi5_slave_wr_mon_cg.py

.PHONY: run-axi5-mon-all-gate-parallel
run-axi5-mon-all-gate-parallel:
	@echo "================================================================================"
	@echo "Running ALL AXI5 Monitor Tests at GATE level (parallel)"
	@echo "Expected: 8 tests (~4 min with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi5_master_rd_mon.py test_axi5_master_rd_mon_cg.py test_axi5_master_wr_mon.py test_axi5_master_wr_mon_cg.py test_axi5_slave_rd_mon.py test_axi5_slave_rd_mon_cg.py test_axi5_slave_wr_mon.py test_axi5_slave_wr_mon_cg.py

.PHONY: run-axi5-mon-all-func-parallel
run-axi5-mon-all-func-parallel:
	@echo "================================================================================"
	@echo "Running ALL AXI5 Monitor Tests at FUNC level (parallel)"
	@echo "Expected: 24 tests (~35 min with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi5_master_rd_mon.py test_axi5_master_rd_mon_cg.py test_axi5_master_wr_mon.py test_axi5_master_wr_mon_cg.py test_axi5_slave_rd_mon.py test_axi5_slave_rd_mon_cg.py test_axi5_slave_wr_mon.py test_axi5_slave_wr_mon_cg.py

.PHONY: run-axi5-mon-all-full-parallel
run-axi5-mon-all-full-parallel:
	@echo "================================================================================"
	@echo "Running ALL AXI5 Monitor Tests at FULL level (parallel)"
	@echo "Expected: 72 tests (~3 hours with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi5_master_rd_mon.py test_axi5_master_rd_mon_cg.py test_axi5_master_wr_mon.py test_axi5_master_wr_mon_cg.py test_axi5_slave_rd_mon.py test_axi5_slave_rd_mon_cg.py test_axi5_slave_wr_mon.py test_axi5_slave_wr_mon_cg.py

# =============================================================================
# AXI5 Clock-Gated Tests (Master + Slave, Read + Write, no monitors)
# =============================================================================
# Test counts (4 CG test files without monitors):
#   Master (rd_cg+wr_cg): GATE=2, FUNC=6, FULL=18
#   Slave (rd_cg+wr_cg):  GATE=2, FUNC=6, FULL=18
#   ALL CG:               GATE=4, FUNC=12, FULL=36

.PHONY: run-axi5-cg-gate
run-axi5-cg-gate:
	@echo "================================================================================"
	@echo "Running AXI5 Clock-Gated Tests at GATE level (smoke test)"
	@echo "Tests: test_axi5_master_rd_cg, test_axi5_master_wr_cg, test_axi5_slave_rd_cg, test_axi5_slave_wr_cg"
	@echo "Expected: 4 tests (~5 min)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi5_master_rd_cg.py test_axi5_master_wr_cg.py test_axi5_slave_rd_cg.py test_axi5_slave_wr_cg.py

.PHONY: run-axi5-cg-func
run-axi5-cg-func:
	@echo "================================================================================"
	@echo "Running AXI5 Clock-Gated Tests at FUNC level (functional coverage)"
	@echo "Tests: test_axi5_master_rd_cg, test_axi5_master_wr_cg, test_axi5_slave_rd_cg, test_axi5_slave_wr_cg"
	@echo "Expected: 12 tests (~45 min)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi5_master_rd_cg.py test_axi5_master_wr_cg.py test_axi5_slave_rd_cg.py test_axi5_slave_wr_cg.py

.PHONY: run-axi5-cg-full
run-axi5-cg-full:
	@echo "================================================================================"
	@echo "Running AXI5 Clock-Gated Tests at FULL level (comprehensive validation)"
	@echo "Tests: test_axi5_master_rd_cg, test_axi5_master_wr_cg, test_axi5_slave_rd_cg, test_axi5_slave_wr_cg"
	@echo "Expected: 36 tests (~4 hours)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) test_axi5_master_rd_cg.py test_axi5_master_wr_cg.py test_axi5_slave_rd_cg.py test_axi5_slave_wr_cg.py

.PHONY: run-axi5-cg-gate-parallel
run-axi5-cg-gate-parallel:
	@echo "================================================================================"
	@echo "Running AXI5 Clock-Gated Tests at GATE level (parallel)"
	@echo "Expected: 4 tests (~2 min with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi5_master_rd_cg.py test_axi5_master_wr_cg.py test_axi5_slave_rd_cg.py test_axi5_slave_wr_cg.py

.PHONY: run-axi5-cg-func-parallel
run-axi5-cg-func-parallel:
	@echo "================================================================================"
	@echo "Running AXI5 Clock-Gated Tests at FUNC level (parallel)"
	@echo "Expected: 12 tests (~18 min with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=FUNC $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi5_master_rd_cg.py test_axi5_master_wr_cg.py test_axi5_slave_rd_cg.py test_axi5_slave_wr_cg.py

.PHONY: run-axi5-cg-full-parallel
run-axi5-cg-full-parallel:
	@echo "================================================================================"
	@echo "Running AXI5 Clock-Gated Tests at FULL level (parallel)"
	@echo "Expected: 36 tests (~1.5 hours with parallel execution)"
	@echo "================================================================================"
	REG_LEVEL=FULL $(PYTEST) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) test_axi5_master_rd_cg.py test_axi5_master_wr_cg.py test_axi5_slave_rd_cg.py test_axi5_slave_wr_cg.py

# ==============================================================================
# Combined Targets (clean + run)
# ==============================================================================

.PHONY: fresh-apb
fresh-apb: clean-all run-apb
	@echo "✓ Fresh APB test run complete"

.PHONY: fresh-axi4
fresh-axi4: clean-all run-axi4
	@echo "✓ Fresh AXI4 test run complete"

.PHONY: fresh-all
fresh-all: clean-all run-all
	@echo "✓ Fresh all tests run complete"

# ==============================================================================
# Quick Aliases
# ==============================================================================

# AMBA4 Protocol Aliases
.PHONY: apb
apb: run-apb

.PHONY: axi4
axi4: run-axi4

.PHONY: axil4
axil4: run-axil4

.PHONY: axis
axis: run-axis

# AMBA5 Protocol Aliases
.PHONY: apb5
apb5: run-apb5

.PHONY: axi5
axi5: run-axi5

.PHONY: axis5
axis5: run-axis5

# Combined Version Aliases
.PHONY: amba4
amba4: run-amba4

.PHONY: amba5
amba5: run-amba5

# General Aliases
.PHONY: all
all: run-all

.PHONY: clean
clean: clean-all

.PHONY: collect
collect: collect-all

.PHONY: list
list: list-all

# ==============================================================================
# End of Makefile
# ==============================================================================
