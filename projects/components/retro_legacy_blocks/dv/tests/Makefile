# ==============================================================================
# Retro Legacy Blocks (RLB) Tests Makefile
# ==============================================================================
#
# Local test runner for APB-based legacy peripheral blocks
#
# Usage:
#   cd $REPO_ROOT/projects/components/retro_legacy_blocks/dv/tests
#   make <target>
#
# Quick start:
#   make help           - Show available targets
#   make run-hpet       - Run HPET tests
#   make run-pit        - Run PIT 8254 tests
#   make run-rtc        - Run RTC tests
#   make run-pic        - Run 8259 PIC tests
#   make run-ioapic     - Run IOAPIC tests
#   make run-all        - Run all tests
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
PYTEST_XDIST = -n 8
PYTEST_TBSTYLE = --tb=short
PYTEST_RERUNS = --reruns 0 --reruns-delay 1

# Default target
.DEFAULT_GOAL := help

# ==============================================================================
# Help Target
# ==============================================================================

.PHONY: help
help:
	@echo "================================================================================"
	@echo "Retro Legacy Blocks (RLB) Tests Makefile"
	@echo "================================================================================"
	@echo ""
	@echo "QUICK RUN TARGETS (BASIC level, single-threaded):"
	@echo "  make run-hpet                   Run HPET tests"
	@echo "  make run-pit                    Run PIT 8254 tests"
	@echo "  make run-rtc                    Run RTC tests"
	@echo "  make run-pic                    Run 8259 PIC tests"
	@echo "  make run-ioapic                 Run IOAPIC tests"
	@echo "  make run-all                    Run all tests"
	@echo ""
	@echo "HPET TARGETS (test_apb_hpet.py):"
	@echo "  make run-hpet-basic             Run HPET at BASIC level"
	@echo "  make run-hpet-basic-waves       Run HPET at BASIC level with waveforms"
	@echo "  make run-hpet-basic-parallel    Run HPET at BASIC level in parallel"
	@echo "  make run-hpet-basic-parallel-waves Run HPET at BASIC level parallel + waves"
	@echo "  make run-hpet-medium            Run HPET at MEDIUM level"
	@echo "  make run-hpet-medium-waves      Run HPET at MEDIUM level with waveforms"
	@echo "  make run-hpet-medium-parallel   Run HPET at MEDIUM level in parallel"
	@echo "  make run-hpet-medium-parallel-waves Run HPET at MEDIUM level parallel + waves"
	@echo "  make run-hpet-full              Run HPET at FULL level"
	@echo "  make run-hpet-full-waves        Run HPET at FULL level with waveforms"
	@echo "  make run-hpet-full-parallel     Run HPET at FULL level in parallel"
	@echo "  make run-hpet-full-parallel-waves Run HPET at FULL level parallel + waves"
	@echo ""
	@echo "PIT 8254 TARGETS (test_apb_pit_8254.py):"
	@echo "  make run-pit-basic              Run PIT at BASIC level"
	@echo "  make run-pit-basic-waves        Run PIT at BASIC level with waveforms"
	@echo "  make run-pit-basic-parallel     Run PIT at BASIC level in parallel"
	@echo "  make run-pit-basic-parallel-waves Run PIT at BASIC level parallel + waves"
	@echo "  make run-pit-medium             Run PIT at MEDIUM level"
	@echo "  make run-pit-medium-waves       Run PIT at MEDIUM level with waveforms"
	@echo "  make run-pit-medium-parallel    Run PIT at MEDIUM level in parallel"
	@echo "  make run-pit-medium-parallel-waves Run PIT at MEDIUM level parallel + waves"
	@echo "  make run-pit-full               Run PIT at FULL level"
	@echo "  make run-pit-full-waves         Run PIT at FULL level with waveforms"
	@echo "  make run-pit-full-parallel      Run PIT at FULL level in parallel"
	@echo "  make run-pit-full-parallel-waves Run PIT at FULL level parallel + waves"
	@echo ""
	@echo "RTC TARGETS (test_apb_rtc.py):"
	@echo "  make run-rtc-basic              Run RTC at BASIC level"
	@echo "  make run-rtc-basic-waves        Run RTC at BASIC level with waveforms"
	@echo "  make run-rtc-basic-parallel     Run RTC at BASIC level in parallel"
	@echo "  make run-rtc-basic-parallel-waves Run RTC at BASIC level parallel + waves"
	@echo "  make run-rtc-medium             Run RTC at MEDIUM level"
	@echo "  make run-rtc-medium-waves       Run RTC at MEDIUM level with waveforms"
	@echo "  make run-rtc-medium-parallel    Run RTC at MEDIUM level in parallel"
	@echo "  make run-rtc-medium-parallel-waves Run RTC at MEDIUM level parallel + waves"
	@echo "  make run-rtc-full               Run RTC at FULL level"
	@echo "  make run-rtc-full-waves         Run RTC at FULL level with waveforms"
	@echo "  make run-rtc-full-parallel      Run RTC at FULL level in parallel"
	@echo "  make run-rtc-full-parallel-waves Run RTC at FULL level parallel + waves"
	@echo ""
	@echo "8259 PIC TARGETS (test_apb_pic_8259.py):"
	@echo "  make run-pic-basic              Run PIC at BASIC level"
	@echo "  make run-pic-basic-waves        Run PIC at BASIC level with waveforms"
	@echo "  make run-pic-basic-parallel     Run PIC at BASIC level in parallel"
	@echo "  make run-pic-basic-parallel-waves Run PIC at BASIC level parallel + waves"
	@echo "  make run-pic-medium             Run PIC at MEDIUM level"
	@echo "  make run-pic-medium-waves       Run PIC at MEDIUM level with waveforms"
	@echo "  make run-pic-medium-parallel    Run PIC at MEDIUM level in parallel"
	@echo "  make run-pic-medium-parallel-waves Run PIC at MEDIUM level parallel + waves"
	@echo "  make run-pic-full               Run PIC at FULL level"
	@echo "  make run-pic-full-waves         Run PIC at FULL level with waveforms"
	@echo "  make run-pic-full-parallel      Run PIC at FULL level in parallel"
	@echo "  make run-pic-full-parallel-waves Run PIC at FULL level parallel + waves"
	@echo ""
	@echo "IOAPIC TARGETS (test_apb_ioapic.py):"
	@echo "  make run-ioapic-basic           Run IOAPIC at BASIC level"
	@echo "  make run-ioapic-basic-waves     Run IOAPIC at BASIC level with waveforms"
	@echo "  make run-ioapic-basic-parallel  Run IOAPIC at BASIC level in parallel"
	@echo "  make run-ioapic-basic-parallel-waves Run IOAPIC at BASIC parallel + waves"
	@echo "  make run-ioapic-medium          Run IOAPIC at MEDIUM level"
	@echo "  make run-ioapic-medium-waves    Run IOAPIC at MEDIUM level with waveforms"
	@echo "  make run-ioapic-medium-parallel Run IOAPIC at MEDIUM level in parallel"
	@echo "  make run-ioapic-medium-parallel-waves Run IOAPIC at MEDIUM parallel + waves"
	@echo "  make run-ioapic-full            Run IOAPIC at FULL level"
	@echo "  make run-ioapic-full-waves      Run IOAPIC at FULL level with waveforms"
	@echo "  make run-ioapic-full-parallel   Run IOAPIC at FULL level in parallel"
	@echo "  make run-ioapic-full-parallel-waves Run IOAPIC at FULL parallel + waves"
	@echo ""
	@echo "COMBINED TARGETS (all blocks):"
	@echo "  make run-all-basic              Run all tests at BASIC level"
	@echo "  make run-all-basic-waves        Run all tests at BASIC level with waveforms"
	@echo "  make run-all-basic-parallel     Run all tests at BASIC level in parallel"
	@echo "  make run-all-basic-parallel-waves Run all tests at BASIC parallel + waves"
	@echo "  make run-all-medium             Run all tests at MEDIUM level"
	@echo "  make run-all-medium-waves       Run all tests at MEDIUM level with waveforms"
	@echo "  make run-all-medium-parallel    Run all tests at MEDIUM level in parallel"
	@echo "  make run-all-medium-parallel-waves Run all tests at MEDIUM parallel + waves"
	@echo "  make run-all-full               Run all tests at FULL level"
	@echo "  make run-all-full-waves         Run all tests at FULL level with waveforms"
	@echo "  make run-all-full-parallel      Run all tests at FULL level in parallel"
	@echo "  make run-all-full-parallel-waves Run all tests at FULL parallel + waves"
	@echo ""
	@echo "UTILITY TARGETS:"
	@echo "  make collect-hpet         Collect (don't run) HPET tests"
	@echo "  make collect-pit          Collect (don't run) PIT tests"
	@echo "  make collect-rtc          Collect (don't run) RTC tests"
	@echo "  make collect-pic          Collect (don't run) PIC tests"
	@echo "  make collect-ioapic       Collect (don't run) IOAPIC tests"
	@echo "  make clean                Clean local artifacts"
	@echo "  make clean-all            Clean all test artifacts"
	@echo ""
	@echo "================================================================================"

# ==============================================================================
# Quick Run Targets (Default BASIC level, single-threaded)
# ==============================================================================

.PHONY: run-hpet
run-hpet:
	@echo "Running HPET tests (BASIC level)..."
	TEST_LEVEL=basic $(PYTEST) test_apb_hpet.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-pit
run-pit:
	@echo "Running PIT 8254 tests (BASIC level)..."
	TEST_LEVEL=basic $(PYTEST) test_apb_pit_8254.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-rtc
run-rtc:
	@echo "Running RTC tests (BASIC level)..."
	TEST_LEVEL=basic $(PYTEST) test_apb_rtc.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-pic
run-pic:
	@echo "Running 8259 PIC tests (BASIC level)..."
	TEST_LEVEL=basic $(PYTEST) test_apb_pic_8259.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-ioapic
run-ioapic:
	@echo "Running IOAPIC tests (BASIC level)..."
	TEST_LEVEL=basic $(PYTEST) test_apb_ioapic.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-all
run-all:
	@echo "Running all RLB tests (BASIC level)..."
	TEST_LEVEL=basic $(PYTEST) test_apb_hpet.py test_apb_pit_8254.py test_apb_rtc.py test_apb_pic_8259.py test_apb_ioapic.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

# ==============================================================================
# HPET Targets (test_apb_hpet.py)
# ==============================================================================

# BASIC level
.PHONY: run-hpet-basic
run-hpet-basic:
	@echo "Running HPET tests at BASIC level..."
	TEST_LEVEL=basic $(PYTEST) test_apb_hpet.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-hpet-basic-waves
run-hpet-basic-waves:
	@echo "Running HPET tests at BASIC level with waveforms..."
	WAVES=1 TEST_LEVEL=basic $(PYTEST) test_apb_hpet.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-hpet-basic-parallel
run-hpet-basic-parallel:
	@echo "Running HPET tests at BASIC level in parallel..."
	TEST_LEVEL=basic $(PYTEST) test_apb_hpet.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-hpet-basic-parallel-waves
run-hpet-basic-parallel-waves:
	@echo "Running HPET tests at BASIC level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=basic $(PYTEST) test_apb_hpet.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# MEDIUM level
.PHONY: run-hpet-medium
run-hpet-medium:
	@echo "Running HPET tests at MEDIUM level..."
	TEST_LEVEL=medium $(PYTEST) test_apb_hpet.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-hpet-medium-waves
run-hpet-medium-waves:
	@echo "Running HPET tests at MEDIUM level with waveforms..."
	WAVES=1 TEST_LEVEL=medium $(PYTEST) test_apb_hpet.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-hpet-medium-parallel
run-hpet-medium-parallel:
	@echo "Running HPET tests at MEDIUM level in parallel..."
	TEST_LEVEL=medium $(PYTEST) test_apb_hpet.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-hpet-medium-parallel-waves
run-hpet-medium-parallel-waves:
	@echo "Running HPET tests at MEDIUM level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=medium $(PYTEST) test_apb_hpet.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# FULL level
.PHONY: run-hpet-full
run-hpet-full:
	@echo "Running HPET tests at FULL level..."
	TEST_LEVEL=full $(PYTEST) test_apb_hpet.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-hpet-full-waves
run-hpet-full-waves:
	@echo "Running HPET tests at FULL level with waveforms..."
	WAVES=1 TEST_LEVEL=full $(PYTEST) test_apb_hpet.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-hpet-full-parallel
run-hpet-full-parallel:
	@echo "Running HPET tests at FULL level in parallel..."
	TEST_LEVEL=full $(PYTEST) test_apb_hpet.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-hpet-full-parallel-waves
run-hpet-full-parallel-waves:
	@echo "Running HPET tests at FULL level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=full $(PYTEST) test_apb_hpet.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

# ==============================================================================
# PIT 8254 Targets (test_apb_pit_8254.py)
# ==============================================================================

# BASIC level
.PHONY: run-pit-basic
run-pit-basic:
	@echo "Running PIT 8254 tests at BASIC level..."
	TEST_LEVEL=basic $(PYTEST) test_apb_pit_8254.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-pit-basic-waves
run-pit-basic-waves:
	@echo "Running PIT 8254 tests at BASIC level with waveforms..."
	WAVES=1 TEST_LEVEL=basic $(PYTEST) test_apb_pit_8254.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-pit-basic-parallel
run-pit-basic-parallel:
	@echo "Running PIT 8254 tests at BASIC level in parallel..."
	TEST_LEVEL=basic $(PYTEST) test_apb_pit_8254.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-pit-basic-parallel-waves
run-pit-basic-parallel-waves:
	@echo "Running PIT 8254 tests at BASIC level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=basic $(PYTEST) test_apb_pit_8254.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)


# MEDIUM level
.PHONY: run-pit-medium
run-pit-medium:
	@echo "Running PIT 8254 tests at MEDIUM level..."
	TEST_LEVEL=medium $(PYTEST) test_apb_pit_8254.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-pit-medium-waves
run-pit-medium-waves:
	@echo "Running PIT 8254 tests at MEDIUM level with waveforms..."
	WAVES=1 TEST_LEVEL=medium $(PYTEST) test_apb_pit_8254.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-pit-medium-parallel
run-pit-medium-parallel:
	@echo "Running PIT 8254 tests at MEDIUM level in parallel..."
	TEST_LEVEL=medium $(PYTEST) test_apb_pit_8254.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-pit-medium-parallel-waves
run-pit-medium-parallel-waves:
	@echo "Running PIT 8254 tests at MEDIUM level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=medium $(PYTEST) test_apb_pit_8254.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)


# FULL level
.PHONY: run-pit-full
run-pit-full:
	@echo "Running PIT 8254 tests at FULL level..."
	TEST_LEVEL=full $(PYTEST) test_apb_pit_8254.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-pit-full-waves
run-pit-full-waves:
	@echo "Running PIT 8254 tests at FULL level with waveforms..."
	WAVES=1 TEST_LEVEL=full $(PYTEST) test_apb_pit_8254.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-pit-full-parallel
run-pit-full-parallel:
	@echo "Running PIT 8254 tests at FULL level in parallel..."
	TEST_LEVEL=full $(PYTEST) test_apb_pit_8254.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-pit-full-parallel-waves
run-pit-full-parallel-waves:
	@echo "Running PIT 8254 tests at FULL level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=full $(PYTEST) test_apb_pit_8254.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)


# ==============================================================================
# RTC Targets (test_apb_rtc.py)
# ==============================================================================

# BASIC level
.PHONY: run-rtc-basic
run-rtc-basic:
	@echo "Running RTC tests at BASIC level..."
	TEST_LEVEL=basic $(PYTEST) test_apb_rtc.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-rtc-basic-waves
run-rtc-basic-waves:
	@echo "Running RTC tests at BASIC level with waveforms..."
	WAVES=1 TEST_LEVEL=basic $(PYTEST) test_apb_rtc.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-rtc-basic-parallel
run-rtc-basic-parallel:
	@echo "Running RTC tests at BASIC level in parallel..."
	TEST_LEVEL=basic $(PYTEST) test_apb_rtc.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-rtc-basic-parallel-waves
run-rtc-basic-parallel-waves:
	@echo "Running RTC tests at BASIC level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=basic $(PYTEST) test_apb_rtc.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)


# MEDIUM level
.PHONY: run-rtc-medium
run-rtc-medium:
	@echo "Running RTC tests at MEDIUM level..."
	TEST_LEVEL=medium $(PYTEST) test_apb_rtc.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-rtc-medium-waves
run-rtc-medium-waves:
	@echo "Running RTC tests at MEDIUM level with waveforms..."
	WAVES=1 TEST_LEVEL=medium $(PYTEST) test_apb_rtc.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-rtc-medium-parallel
run-rtc-medium-parallel:
	@echo "Running RTC tests at MEDIUM level in parallel..."
	TEST_LEVEL=medium $(PYTEST) test_apb_rtc.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-rtc-medium-parallel-waves
run-rtc-medium-parallel-waves:
	@echo "Running RTC tests at MEDIUM level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=medium $(PYTEST) test_apb_rtc.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)


# FULL level
.PHONY: run-rtc-full
run-rtc-full:
	@echo "Running RTC tests at FULL level..."
	TEST_LEVEL=full $(PYTEST) test_apb_rtc.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-rtc-full-waves
run-rtc-full-waves:
	@echo "Running RTC tests at FULL level with waveforms..."
	WAVES=1 TEST_LEVEL=full $(PYTEST) test_apb_rtc.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-rtc-full-parallel
run-rtc-full-parallel:
	@echo "Running RTC tests at FULL level in parallel..."
	TEST_LEVEL=full $(PYTEST) test_apb_rtc.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-rtc-full-parallel-waves
run-rtc-full-parallel-waves:
	@echo "Running RTC tests at FULL level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=full $(PYTEST) test_apb_rtc.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)


# ==============================================================================
# 8259 PIC Targets (test_apb_pic_8259.py)
# ==============================================================================

# BASIC level
.PHONY: run-pic-basic
run-pic-basic:
	@echo "Running 8259 PIC tests at BASIC level..."
	TEST_LEVEL=basic $(PYTEST) test_apb_pic_8259.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-pic-basic-waves
run-pic-basic-waves:
	@echo "Running 8259 PIC tests at BASIC level with waveforms..."
	WAVES=1 TEST_LEVEL=basic $(PYTEST) test_apb_pic_8259.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-pic-basic-parallel
run-pic-basic-parallel:
	@echo "Running 8259 PIC tests at BASIC level in parallel..."
	TEST_LEVEL=basic $(PYTEST) test_apb_pic_8259.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-pic-basic-parallel-waves
run-pic-basic-parallel-waves:
	@echo "Running 8259 PIC tests at BASIC level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=basic $(PYTEST) test_apb_pic_8259.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)


# MEDIUM level
.PHONY: run-pic-medium
run-pic-medium:
	@echo "Running 8259 PIC tests at MEDIUM level..."
	TEST_LEVEL=medium $(PYTEST) test_apb_pic_8259.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-pic-medium-waves
run-pic-medium-waves:
	@echo "Running 8259 PIC tests at MEDIUM level with waveforms..."
	WAVES=1 TEST_LEVEL=medium $(PYTEST) test_apb_pic_8259.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-pic-medium-parallel
run-pic-medium-parallel:
	@echo "Running 8259 PIC tests at MEDIUM level in parallel..."
	TEST_LEVEL=medium $(PYTEST) test_apb_pic_8259.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-pic-medium-parallel-waves
run-pic-medium-parallel-waves:
	@echo "Running 8259 PIC tests at MEDIUM level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=medium $(PYTEST) test_apb_pic_8259.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)


# FULL level
.PHONY: run-pic-full
run-pic-full:
	@echo "Running 8259 PIC tests at FULL level..."
	TEST_LEVEL=full $(PYTEST) test_apb_pic_8259.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-pic-full-waves
run-pic-full-waves:
	@echo "Running 8259 PIC tests at FULL level with waveforms..."
	WAVES=1 TEST_LEVEL=full $(PYTEST) test_apb_pic_8259.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-pic-full-parallel
run-pic-full-parallel:
	@echo "Running 8259 PIC tests at FULL level in parallel..."
	TEST_LEVEL=full $(PYTEST) test_apb_pic_8259.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-pic-full-parallel-waves
run-pic-full-parallel-waves:
	@echo "Running 8259 PIC tests at FULL level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=full $(PYTEST) test_apb_pic_8259.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)


# ==============================================================================
# IOAPIC Targets (test_apb_ioapic.py)
# ==============================================================================

# BASIC level
.PHONY: run-ioapic-basic
run-ioapic-basic:
	@echo "Running IOAPIC tests at BASIC level..."
	TEST_LEVEL=basic $(PYTEST) test_apb_ioapic.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-ioapic-basic-waves
run-ioapic-basic-waves:
	@echo "Running IOAPIC tests at BASIC level with waveforms..."
	WAVES=1 TEST_LEVEL=basic $(PYTEST) test_apb_ioapic.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-ioapic-basic-parallel
run-ioapic-basic-parallel:
	@echo "Running IOAPIC tests at BASIC level in parallel..."
	TEST_LEVEL=basic $(PYTEST) test_apb_ioapic.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-ioapic-basic-parallel-waves
run-ioapic-basic-parallel-waves:
	@echo "Running IOAPIC tests at BASIC level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=basic $(PYTEST) test_apb_ioapic.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)


# MEDIUM level
.PHONY: run-ioapic-medium
run-ioapic-medium:
	@echo "Running IOAPIC tests at MEDIUM level..."
	TEST_LEVEL=medium $(PYTEST) test_apb_ioapic.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-ioapic-medium-waves
run-ioapic-medium-waves:
	@echo "Running IOAPIC tests at MEDIUM level with waveforms..."
	WAVES=1 TEST_LEVEL=medium $(PYTEST) test_apb_ioapic.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-ioapic-medium-parallel
run-ioapic-medium-parallel:
	@echo "Running IOAPIC tests at MEDIUM level in parallel..."
	TEST_LEVEL=medium $(PYTEST) test_apb_ioapic.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-ioapic-medium-parallel-waves
run-ioapic-medium-parallel-waves:
	@echo "Running IOAPIC tests at MEDIUM level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=medium $(PYTEST) test_apb_ioapic.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)


# FULL level
.PHONY: run-ioapic-full
run-ioapic-full:
	@echo "Running IOAPIC tests at FULL level..."
	TEST_LEVEL=full $(PYTEST) test_apb_ioapic.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-ioapic-full-waves
run-ioapic-full-waves:
	@echo "Running IOAPIC tests at FULL level with waveforms..."
	WAVES=1 TEST_LEVEL=full $(PYTEST) test_apb_ioapic.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-ioapic-full-parallel
run-ioapic-full-parallel:
	@echo "Running IOAPIC tests at FULL level in parallel..."
	TEST_LEVEL=full $(PYTEST) test_apb_ioapic.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-ioapic-full-parallel-waves
run-ioapic-full-parallel-waves:
	@echo "Running IOAPIC tests at FULL level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=full $(PYTEST) test_apb_ioapic.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)


# ==============================================================================
# Combined Targets (All Blocks)
# ==============================================================================

# BASIC level
.PHONY: run-all-basic
run-all-basic:
	@echo "Running all RLB tests at BASIC level..."
	TEST_LEVEL=basic $(PYTEST) test_apb_hpet.py test_apb_pit_8254.py test_apb_rtc.py test_apb_pic_8259.py test_apb_ioapic.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-all-basic-waves
run-all-basic-waves:
	@echo "Running all RLB tests at BASIC level with waveforms..."
	WAVES=1 TEST_LEVEL=basic $(PYTEST) test_apb_hpet.py test_apb_pit_8254.py test_apb_rtc.py test_apb_pic_8259.py test_apb_ioapic.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-all-basic-parallel
run-all-basic-parallel:
	@echo "Running all RLB tests at BASIC level in parallel..."
	TEST_LEVEL=basic $(PYTEST) test_apb_hpet.py test_apb_pit_8254.py test_apb_rtc.py test_apb_pic_8259.py test_apb_ioapic.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-all-basic-parallel-waves
run-all-basic-parallel-waves:
	@echo "Running all RLB tests at BASIC level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=basic $(PYTEST) test_apb_hpet.py test_apb_pit_8254.py test_apb_rtc.py test_apb_pic_8259.py test_apb_ioapic.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)


# MEDIUM level
.PHONY: run-all-medium
run-all-medium:
	@echo "Running all RLB tests at MEDIUM level..."
	TEST_LEVEL=medium $(PYTEST) test_apb_hpet.py test_apb_pit_8254.py test_apb_rtc.py test_apb_pic_8259.py test_apb_ioapic.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-all-medium-waves
run-all-medium-waves:
	@echo "Running all RLB tests at MEDIUM level with waveforms..."
	WAVES=1 TEST_LEVEL=medium $(PYTEST) test_apb_hpet.py test_apb_pit_8254.py test_apb_rtc.py test_apb_pic_8259.py test_apb_ioapic.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-all-medium-parallel
run-all-medium-parallel:
	@echo "Running all RLB tests at MEDIUM level in parallel..."
	TEST_LEVEL=medium $(PYTEST) test_apb_hpet.py test_apb_pit_8254.py test_apb_rtc.py test_apb_pic_8259.py test_apb_ioapic.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-all-medium-parallel-waves
run-all-medium-parallel-waves:
	@echo "Running all RLB tests at MEDIUM level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=medium $(PYTEST) test_apb_hpet.py test_apb_pit_8254.py test_apb_rtc.py test_apb_pic_8259.py test_apb_ioapic.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)


# FULL level
.PHONY: run-all-full
run-all-full:
	@echo "Running all RLB tests at FULL level..."
	TEST_LEVEL=full $(PYTEST) test_apb_hpet.py test_apb_pit_8254.py test_apb_rtc.py test_apb_pic_8259.py test_apb_ioapic.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-all-full-waves
run-all-full-waves:
	@echo "Running all RLB tests at FULL level with waveforms..."
	WAVES=1 TEST_LEVEL=full $(PYTEST) test_apb_hpet.py test_apb_pit_8254.py test_apb_rtc.py test_apb_pic_8259.py test_apb_ioapic.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: run-all-full-parallel
run-all-full-parallel:
	@echo "Running all RLB tests at FULL level in parallel..."
	TEST_LEVEL=full $(PYTEST) test_apb_hpet.py test_apb_pit_8254.py test_apb_rtc.py test_apb_pic_8259.py test_apb_ioapic.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-all-full-parallel-waves
run-all-full-parallel-waves:
	@echo "Running all RLB tests at FULL level in parallel with waveforms..."
	WAVES=1 TEST_LEVEL=full $(PYTEST) test_apb_hpet.py test_apb_pit_8254.py test_apb_rtc.py test_apb_pic_8259.py test_apb_ioapic.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)


# ==============================================================================
# Utility Targets
# ==============================================================================

.PHONY: collect-hpet
collect-hpet:
	@echo "Collecting HPET tests..."
	$(PYTEST) test_apb_hpet.py --collect-only

.PHONY: collect-pit
collect-pit:
	@echo "Collecting PIT 8254 tests..."
	$(PYTEST) test_apb_pit_8254.py --collect-only

.PHONY: collect-rtc
collect-rtc:
	@echo "Collecting RTC tests..."
	$(PYTEST) test_apb_rtc.py --collect-only

.PHONY: collect-pic
collect-pic:
	@echo "Collecting 8259 PIC tests..."
	$(PYTEST) test_apb_pic_8259.py --collect-only

.PHONY: collect-ioapic
collect-ioapic:
	@echo "Collecting IOAPIC tests..."
	$(PYTEST) test_apb_ioapic.py --collect-only

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
