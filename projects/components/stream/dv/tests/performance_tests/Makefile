# Makefile for STREAM Performance Tests
#
# Purpose: Automate V1/V2/V3 baseline performance testing and report generation
#
# Targets:
#   v1-baseline       - Run V1 baseline tests (read + write) and update reports
#   v1-read-baseline  - Run V1 read baseline only
#   v1-write-baseline - Run V1 write baseline only
#   v2-performance    - Run V2 performance tests (after V2 implementation)
#   v3-performance    - Run V3 performance tests (after V3 implementation)
#   all-baselines     - Run all available baselines
#   clean             - Remove generated files
#
# Usage:
#   make v1-baseline           # Run V1 tests and auto-update reports
#   make v1-read-baseline      # Run V1 read tests only
#   pytest test_v1_baseline_read.py -v -s   # Run manually with verbose output

.PHONY: all v1-baseline v1-read-baseline v1-write-baseline v2-performance v3-performance clean help

# Directories
STREAM_ROOT := $(shell cd ../../../.. && pwd)
JSON_DIR := $(STREAM_ROOT)/dv/tests/performance_results
REPORTS_DIR := $(STREAM_ROOT)/reports
UPDATE_SCRIPT := $(STREAM_ROOT)/bin/update_performance_reports.py

# Python and pytest
PYTHON := python3
PYTEST := $(PYTHON) -m pytest

# Default pytest options
PYTEST_OPTS := -v -s
PYTEST_WORKERS := 8  # Parallel workers for test execution

# Help target
help:
	@echo "STREAM Performance Test Makefile"
	@echo ""
	@echo "Available targets:"
	@echo "  v1-baseline       - Run V1 baseline (read + write), update reports"
	@echo "  v1-read-baseline  - Run V1 read baseline only"
	@echo "  v1-write-baseline - Run V1 write baseline only (when created)"
	@echo "  v2-performance    - Run V2 tests (pending V2 implementation)"
	@echo "  v3-performance    - Run V3 tests (pending V3 implementation)"
	@echo "  all-baselines     - Run all implemented baselines"
	@echo "  clean             - Remove generated files"
	@echo "  help              - Show this help message"
	@echo ""
	@echo "Example usage:"
	@echo "  make v1-baseline           # Full V1 baseline + auto-update reports"
	@echo "  make v1-read-baseline      # V1 read only"

# V1 Read Baseline
v1-read-baseline:
	@echo "=========================================="
	@echo "Running V1 Read Engine Baseline Tests"
	@echo "=========================================="
	@mkdir -p $(JSON_DIR)
	@mkdir -p logs
	$(PYTEST) test_v1_baseline_read.py $(PYTEST_OPTS) -n $(PYTEST_WORKERS)
	@echo ""
	@echo "=========================================="
	@echo "Updating Performance Reports"
	@echo "=========================================="
	$(UPDATE_SCRIPT) --json-dir $(JSON_DIR) --reports-dir $(REPORTS_DIR) --version v1 --engine read
	@echo ""
	@echo "✓ V1 Read Baseline Complete"
	@echo "  Results: $(JSON_DIR)/v1_read_*.json"
	@echo "  Report:  $(REPORTS_DIR)/v1_read_performance.md"

# V1 Write Baseline
v1-write-baseline:
	@echo "=========================================="
	@echo "Running V1 Write Engine Baseline Tests"
	@echo "=========================================="
	@mkdir -p $(JSON_DIR)
	@mkdir -p logs
	$(PYTEST) test_v1_baseline_write.py $(PYTEST_OPTS) -n $(PYTEST_WORKERS)
	@echo ""
	@echo "=========================================="
	@echo "Updating Performance Reports"
	@echo "=========================================="
	$(UPDATE_SCRIPT) --json-dir $(JSON_DIR) --reports-dir $(REPORTS_DIR) --version v1 --engine write
	@echo ""
	@echo "✓ V1 Write Baseline Complete"
	@echo "  Results: $(JSON_DIR)/v1_write_*.json"
	@echo "  Report:  $(REPORTS_DIR)/v1_write_performance.md"

# V1 Complete Baseline (Read + Write)
v1-baseline: v1-read-baseline v1-write-baseline
	@echo ""
	@echo "=========================================="
	@echo "V1 Baseline Summary"
	@echo "=========================================="
	@echo "✓ Read baseline: Complete"
	@echo "✓ Write baseline: Complete"
	@echo ""
	@echo "View results:"
	@echo "  cat $(REPORTS_DIR)/v1_read_performance.md"
	@echo "  cat $(REPORTS_DIR)/v1_write_performance.md"

# V2 Performance Tests (pending implementation)
v2-performance:
	@echo "⚠️  V2 performance tests pending V2 RTL implementation"
	@echo "  Requires: V2 read/write engines with command pipelining"
	@false

# V3 Performance Tests (pending implementation)
v3-performance:
	@echo "⚠️  V3 performance tests pending V3 RTL implementation"
	@echo "  Requires: V3 OOO logic implementation"
	@false

# Run all available baselines
all-baselines: v1-baseline
	@echo ""
	@echo "=========================================="
	@echo "All Baselines Complete"
	@echo "=========================================="

# Clean generated files
clean:
	@echo "Cleaning generated files..."
	rm -rf logs/
	rm -rf local_sim_build/
	rm -rf $(JSON_DIR)/*.json
	rm -rf __pycache__/
	rm -rf .pytest_cache/
	@echo "✓ Clean complete"

# Default target
all: v1-baseline
