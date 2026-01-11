# Coverage Collection Guide for Project Components

This document explains how to add code coverage and protocol coverage tracking to project components. The STREAM component serves as the reference implementation.

## Table of Contents

1. [Overview](#overview)
2. [Architecture: Test Hierarchy Levels](#architecture-test-hierarchy-levels)
3. [Quick Start](#quick-start)
4. [Global vs Local Scripts](#global-vs-local-scripts)
5. [Adding Coverage to a New Component](#adding-coverage-to-a-new-component)
6. [Coverage APIs](#coverage-apis)
7. [Legal Coverage Mode](#legal-coverage-mode)
8. [Coverage Data Structure](#coverage-data-structure)
9. [Aggregating Coverage Across Test Levels](#aggregating-coverage-across-test-levels)
10. [Report Generation](#report-generation)
11. [Protocol Coverage Bins](#protocol-coverage-bins)
12. [Best Practices](#best-practices)
13. [Troubleshooting](#troubleshooting)

---

## Overview

The coverage infrastructure provides:

1. **Code Coverage** - Line, toggle, and branch coverage via Verilator's `--coverage` flags
2. **Protocol Coverage** - Transaction-level coverage for AXI/APB protocols
3. **Functional Coverage** - Scenario-based coverage for test completeness
4. **Legal Coverage** - Coverage measured against only the variations the component actually supports
5. **Aggregated Reports** - Combined coverage from all test levels in Markdown format

## Architecture: Test Hierarchy Levels

Coverage is collected at three hierarchical test levels:

```
┌─────────────────────────────────────────────────────────────────────────┐
│                           TOP LEVEL                                      │
│  Full system integration tests (stream_top)                              │
│  - All modules instantiated together                                     │
│  - End-to-end data flow verification                                     │
│  - APB configuration + AXI data path                                     │
│  Coverage: coverage_data/top/                                            │
├─────────────────────────────────────────────────────────────────────────┤
│                          MACRO LEVEL                                     │
│  Multi-module integration tests (stream_core, scheduler_group)           │
│  - Groups of related FUBs tested together                                │
│  - Internal interfaces verified                                          │
│  - Cross-module behavior                                                 │
│  Coverage: coverage_data/macro/                                          │
├─────────────────────────────────────────────────────────────────────────┤
│                           FUB LEVEL                                      │
│  Functional Unit Block tests (scheduler, descriptor_engine, etc.)        │
│  - Individual module verification                                        │
│  - Unit-level edge cases and corner cases                                │
│  - Highest coverage granularity                                          │
│  Coverage: coverage_data/fub/                                            │
└─────────────────────────────────────────────────────────────────────────┘
```

### Test Intensity Levels

Within each hierarchy level, tests can run at different intensity levels:

| Level | Purpose | Duration | Operations |
|-------|---------|----------|------------|
| `gate` | Quick smoke test | ~30s | 10-20 ops per phase |
| `func` | Functional coverage | ~90s | 30-50 ops per phase |
| `full` | Comprehensive validation | ~180s+ | 100+ ops, stress testing |

Set via environment variable: `TEST_LEVEL=gate|func|full`

---

## Quick Start

### Running Tests with Coverage

```bash
# Navigate to tests directory
cd projects/components/{component}/dv/tests

# Run all tests with coverage at functional level
make coverage-all

# Run specific level with coverage
make coverage-fub          # FUB level only
make coverage-macro        # Macro level only
make coverage-top          # Top level only

# Run with specific test intensity
make coverage-all-full     # All levels, full intensity
make coverage-fub-gate     # FUB level, gate (quick) intensity

# Generate combined report from all levels
make coverage-report

# Full workflow: clean + run all + report
make coverage-full-report
```

### Environment Variables

| Variable | Values | Description |
|----------|--------|-------------|
| `COVERAGE` | `1` | Enable coverage collection |
| `COVERAGE_LEGAL` | `1` | Enable legal coverage mode (component-specific) |
| `TEST_LEVEL` | `gate`, `func`, `full` | Test intensity level |
| `COVERAGE_OUTPUT_DIR` | path | Override coverage output directory |
| `COVERAGE_TEST_NAME` | string | Override test name for coverage files |

Example:
```bash
COVERAGE=1 COVERAGE_LEGAL=1 TEST_LEVEL=full pytest test_scheduler.py -v
```

---

## Global vs Local Scripts

Understanding what is global (framework/shared) vs local (component-specific) is critical for proper coverage implementation.

### Global Scripts (Shared Framework)

Location: `bin/CocoTBFramework/` and `bin/`

These are **SHARED** across all components and should **NOT** be modified for component-specific needs:

| Script/Module | Location | Purpose |
|---------------|----------|---------|
| `TBBase` | `bin/CocoTBFramework/tbclasses/shared/tbbase.py` | Base testbench class |
| `FlexConfigBase` | `bin/CocoTBFramework/tbclasses/flex_config_base.py` | Configuration utilities |
| GAXI BFMs | `bin/CocoTBFramework/components/gaxi/` | Generic AXI bus functional models |
| AXI4 Factories | `bin/CocoTBFramework/tbclasses/axi4_factories.py` | AXI4 interface creation |
| `get_paths()` | `bin/CocoTBFramework/tbclasses/common/pytest_cocotb_utils.py` | Path utilities |
| `get_sources_from_filelist()` | `bin/CocoTBFramework/tbclasses/common/pytest_cocotb_utils.py` | Filelist parsing |

### Local Scripts (Component-Specific)

Location: `projects/components/{component}/`

These are **COMPONENT-SPECIFIC** and must be created for each component:

```
projects/components/{component}/
├── dv/
│   ├── {component}_coverage/          # Coverage package (LOCAL)
│   │   ├── __init__.py
│   │   ├── coverage_config.py         # Configuration
│   │   ├── protocol_coverage.py       # Protocol coverage
│   │   ├── coverage_collector.py      # Main collector
│   │   ├── coverage_helper.py         # Easy integration helper
│   │   └── legal_coverage_config.py   # Legal coverage definition
│   │
│   ├── tbclasses/                     # Component testbench classes (LOCAL)
│   │   ├── scheduler_tb.py
│   │   ├── stream_core_tb.py
│   │   └── stream_top_tb.py
│   │
│   └── tests/
│       ├── Makefile                   # Test orchestration (LOCAL)
│       ├── conftest.py                # Shared pytest config (LOCAL)
│       ├── fub/                       # FUB level tests
│       │   ├── conftest.py            # FUB-specific coverage aggregation
│       │   └── test_*.py
│       ├── macro/                     # Macro level tests
│       │   ├── conftest.py            # Macro-specific coverage aggregation
│       │   └── test_*.py
│       └── top/                       # Top level tests
│           ├── conftest.py            # Top-specific coverage aggregation
│           └── test_*.py
│
├── bin/
│   └── generate_coverage_report.py    # Report generator (LOCAL)
│
└── docs/
    └── coverage/
        └── COVERAGE_METHODOLOGY.md    # Documentation (LOCAL)
```

### Why This Separation Matters

1. **Framework Stability** - Global scripts are tested across many components; changes affect everything
2. **Component Flexibility** - Local scripts can be customized for specific coverage needs
3. **Legal Coverage** - Only the component knows what variations it legally supports
4. **Aggregation** - Each test level needs its own conftest.py for proper aggregation

---

## Adding Coverage to a New Component

### Step 1: Create Coverage Package Structure

Create the following directory structure:

```
projects/components/{component}/dv/
    {component}_coverage/    # Named to avoid collision with Python coverage pkg
        __init__.py           # Package exports
        coverage_config.py    # Configuration classes
        protocol_coverage.py  # Protocol coverage tracking
        coverage_collector.py # Main collector class
        coverage_helper.py    # Easy integration helpers
        legal_coverage_config.py  # Component-specific legal variations
```

**IMPORTANT:** Name the directory `{component}_coverage` (e.g., `stream_coverage`, `rapids_coverage`)
to avoid naming collision with Python's standard `coverage` package used by cocotb.

### Step 2: Copy and Adapt from STREAM

The easiest approach is to copy from STREAM and adapt:

```bash
# Copy coverage package (note: renamed to stream_coverage)
cp -r projects/components/stream/dv/stream_coverage \
      projects/components/{component}/dv/{component}_coverage

# Copy report generator
cp projects/components/stream/bin/generate_coverage_report.py \
   projects/components/{component}/bin/

# Copy documentation template
cp projects/components/stream/dv/COVERAGE_METHODOLOGY.md \
   projects/components/{component}/dv/
```

Update imports in the copied files to reference your component.

### Step 3: Create conftest.py for Each Test Level

Each test level (fub, macro, top) needs its own conftest.py with coverage aggregation.

**Template for conftest.py:**

```python
# In dv/tests/{level}/conftest.py

import os
import json
import pytest
import logging
import glob
from datetime import datetime
from pathlib import Path

# Coverage aggregation for {level} tests
def _aggregate_coverage(coverage_dir: str, log: logging.Logger) -> dict:
    """Aggregate all per-test coverage files into a combined summary."""
    per_test_dir = os.path.join(coverage_dir, "per_test")

    if not os.path.exists(per_test_dir):
        log.warning(f"Per-test coverage directory not found: {per_test_dir}")
        return {}

    combined = {
        'test_results': [],
        'protocol_totals': {
            'axi_read': {'covered': 0, 'total': 0},
            'axi_write': {'covered': 0, 'total': 0},
            'apb': {'covered': 0, 'total': 0},
            'scenarios': {'covered': 0, 'total': 0}
        },
        'code_coverage': {
            'line': {'covered': 0, 'total': 0},
            'toggle': {'covered': 0, 'total': 0}
        }
    }

    # Find all summary files
    summary_files = glob.glob(os.path.join(per_test_dir, "*_summary.json"))

    for summary_file in summary_files:
        try:
            with open(summary_file, 'r') as f:
                data = json.load(f)
                combined['test_results'].append({
                    'test_name': data.get('test_name', os.path.basename(summary_file)),
                    'protocol_pct': data.get('overall', {}).get('protocol_pct', 0),
                    'line_pct': data.get('overall', {}).get('line_pct', 0)
                })

                # Aggregate protocol coverage
                proto = data.get('protocol_coverage', {})
                for category in ['axi_read', 'axi_write', 'apb', 'scenarios']:
                    if category in proto:
                        combined['protocol_totals'][category]['covered'] += proto[category].get('covered', 0)
                        combined['protocol_totals'][category]['total'] += proto[category].get('total', 0)

                # Aggregate code coverage
                code = data.get('code_coverage', {})
                for cov_type in ['line', 'toggle']:
                    if cov_type in code:
                        combined['code_coverage'][cov_type]['covered'] += code[cov_type].get('covered', 0)
                        combined['code_coverage'][cov_type]['total'] += code[cov_type].get('total', 0)
        except Exception as e:
            log.warning(f"Failed to parse {summary_file}: {e}")

    return combined


def _generate_coverage_report(combined: dict, output_path: str, level: str, log: logging.Logger):
    """Generate markdown coverage report for this level."""
    lines = []
    lines.append(f"# {level.upper()} Level Coverage Report")
    lines.append(f"\nGenerated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")

    # Summary table
    lines.append("## Summary\n")
    lines.append("| Metric | Covered | Total | Percentage |")
    lines.append("|--------|---------|-------|------------|")

    for category, data in combined.get('protocol_totals', {}).items():
        covered = data.get('covered', 0)
        total = data.get('total', 0)
        pct = (covered / total * 100) if total > 0 else 0
        lines.append(f"| {category} | {covered} | {total} | {pct:.1f}% |")

    for cov_type, data in combined.get('code_coverage', {}).items():
        covered = data.get('covered', 0)
        total = data.get('total', 0)
        pct = (covered / total * 100) if total > 0 else 0
        lines.append(f"| {cov_type}_coverage | {covered} | {total} | {pct:.1f}% |")

    # Per-test results
    lines.append("\n## Per-Test Results\n")
    lines.append("| Test | Protocol % | Line % |")
    lines.append("|------|------------|--------|")

    for result in combined.get('test_results', []):
        lines.append(f"| {result['test_name']} | {result['protocol_pct']:.1f}% | {result['line_pct']:.1f}% |")

    report_text = "\n".join(lines)

    with open(output_path, 'w') as f:
        f.write(report_text)

    log.info(f"Coverage report written to: {output_path}")


def pytest_configure(config):
    """Configure pytest for coverage collection."""
    log = logging.getLogger("{level}_conftest")

    if os.environ.get('COVERAGE', '0') == '1':
        tests_dir = os.path.dirname(os.path.abspath(__file__))
        coverage_dir = os.path.join(tests_dir, "coverage_data")

        os.makedirs(os.path.join(coverage_dir, "per_test"), exist_ok=True)
        os.makedirs(os.path.join(coverage_dir, "reports"), exist_ok=True)

        # Set environment for coverage collector
        os.environ['COVERAGE_OUTPUT_DIR'] = os.path.join(coverage_dir, "per_test")

        log.info(f"Coverage enabled for {level} tests. Data: {coverage_dir}")


def pytest_sessionfinish(session, exitstatus):
    """Generate coverage report after all tests complete."""
    log = logging.getLogger("{level}_conftest")

    if os.environ.get('COVERAGE', '0') != '1':
        return

    tests_dir = os.path.dirname(os.path.abspath(__file__))
    coverage_dir = os.path.join(tests_dir, "coverage_data")

    if not os.path.exists(coverage_dir):
        return

    log.info("Aggregating {level} coverage data...")
    combined = _aggregate_coverage(coverage_dir, log)

    if combined:
        report_path = os.path.join(coverage_dir, "reports", "{level}_coverage_report.md")
        _generate_coverage_report(combined, report_path, "{level}", log)

        # Save combined JSON
        combined_path = os.path.join(coverage_dir, "combined_{level}_coverage.json")
        with open(combined_path, 'w') as f:
            json.dump(combined, f, indent=2)


@pytest.fixture(scope="function")
def coverage_enabled():
    """Check if coverage collection is enabled."""
    return os.environ.get('COVERAGE', '0') == '1'
```

### Step 4: Update Test Files

Modify test files to use coverage helpers:

```python
# In your test file (e.g., test_scheduler.py)

import os
import cocotb
import pytest
from cocotb_test.simulator import run

# Import coverage helper
try:
    from projects.components.{component}.dv.{component}_coverage import CoverageHelper
    COVERAGE_AVAILABLE = True
except ImportError:
    COVERAGE_AVAILABLE = False


def get_coverage_helper(test_name: str, log=None):
    """Get coverage helper if coverage is enabled."""
    if not COVERAGE_AVAILABLE:
        return None
    if os.environ.get('COVERAGE', '0') != '1':
        return None
    return CoverageHelper.get_instance(test_name, log=log)


# ============================================================================
# COCOTB TEST FUNCTION
# ============================================================================

@cocotb.test(timeout_time=100, timeout_unit="ms")
async def cocotb_test_my_module(dut):
    """CocoTB test function with coverage sampling."""
    test_level = os.environ.get('TEST_LEVEL', 'basic')
    test_name = os.environ.get('COVERAGE_TEST_NAME', f'my_module_{test_level}')

    # Get coverage helper (returns None if coverage disabled)
    coverage = get_coverage_helper(test_name, log=dut._log)

    # Initialize testbench
    tb = MyModuleTB(dut)
    await tb.setup_clocks_and_reset()

    # Run test phases
    # ... test logic ...

    # Sample coverage during test
    if coverage:
        coverage.sample_scenario(f"basic_operation_{test_level}")

        # Sample AXI transactions as they complete
        coverage.sample_axi_read(burst_type=1, burst_size=6, burst_len=7)
        coverage.sample_axi_write(burst_type=1, burst_size=6, burst_len=7, response=0)

        # Sample APB transactions
        coverage.sample_apb_read()
        coverage.sample_apb_write()

        # Save coverage at end of test
        coverage.save()


# ============================================================================
# PYTEST WRAPPER FUNCTION
# ============================================================================

@pytest.mark.parametrize("params", test_params)
def test_my_module(request, params):
    """Pytest wrapper with coverage support."""
    # ... setup paths, filelist, etc. ...

    # Build test name for coverage
    test_name = f"my_module_{params['width']}_{params['depth']}"

    # Base environment variables
    extra_env = {
        'TEST_LEVEL': os.environ.get('TEST_LEVEL', 'func'),
        'COVERAGE_TEST_NAME': test_name,
    }

    # Add coverage output directory if coverage is enabled
    if os.environ.get('COVERAGE', '0') == '1':
        coverage_output = os.path.join(os.path.dirname(__file__), "coverage_data", "per_test")
        extra_env['COVERAGE_OUTPUT_DIR'] = coverage_output

    # Build compile args - include coverage if enabled
    compile_args = [
        "--trace",
        "--trace-structs",
        "-Wno-TIMESCALEMOD",
    ]

    # Add coverage compile args if COVERAGE=1
    if os.environ.get('COVERAGE', '0') == '1':
        compile_args.extend([
            "--coverage",
            "--coverage-line",
            "--coverage-toggle",
            "--coverage-underscore",
        ])

    run(
        # ... standard run() arguments ...
        extra_env=extra_env,
        compile_args=compile_args,
    )
```

### Step 5: Create the Makefile

Create a comprehensive Makefile that orchestrates all test levels and coverage:

```makefile
# projects/components/{component}/dv/tests/Makefile

# ==============================================================================
# Configuration
# ==============================================================================

SHELL := /bin/bash
REPO_ROOT ?= $(shell git rev-parse --show-toplevel)
PYTEST ?= $(REPO_ROOT)/venv/bin/python -m pytest
PYTHON ?= $(REPO_ROOT)/venv/bin/python

# Test level: gate (quick), func (functional), full (comprehensive)
TEST_LEVEL ?= func

# Pytest options
PYTEST_VERBOSE ?= -v
PYTEST_TBSTYLE ?= --tb=short

# ==============================================================================
# Directory Structure
# ==============================================================================

TESTS_DIR := $(shell pwd)
FUB_DIR := $(TESTS_DIR)/fub
MACRO_DIR := $(TESTS_DIR)/macro
TOP_DIR := $(TESTS_DIR)/top

# ==============================================================================
# Help
# ==============================================================================

.PHONY: help
help:
	@echo "Coverage Collection Targets"
	@echo "==========================="
	@echo ""
	@echo "Individual Level Coverage:"
	@echo "  coverage-fub          Run FUB tests with coverage (TEST_LEVEL=$(TEST_LEVEL))"
	@echo "  coverage-macro        Run macro tests with coverage"
	@echo "  coverage-top          Run top tests with coverage"
	@echo ""
	@echo "Combined Coverage:"
	@echo "  coverage-all          Run all levels with coverage"
	@echo "  coverage-all-gate     Run all levels (gate intensity)"
	@echo "  coverage-all-func     Run all levels (func intensity)"
	@echo "  coverage-all-full     Run all levels (full intensity)"
	@echo ""
	@echo "Reports:"
	@echo "  coverage-report       Generate combined coverage report"
	@echo "  coverage-full-report  Clean + run all + generate report"
	@echo ""
	@echo "Utilities:"
	@echo "  clean-coverage        Remove all coverage data"
	@echo "  coverage-status       Show coverage data status"

# ==============================================================================
# Individual Level Coverage
# ==============================================================================

.PHONY: coverage-fub
coverage-fub:
	@echo "Running FUB tests with coverage (TEST_LEVEL=$(TEST_LEVEL))..."
	cd $(FUB_DIR) && \
	PYTHONPATH=$(REPO_ROOT)/bin:$$PYTHONPATH \
	SIM=verilator \
	WAVES=0 \
	COVERAGE=1 \
	COVERAGE_LEGAL=1 \
	TEST_LEVEL=$(TEST_LEVEL) \
	timeout 900 $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: coverage-macro
coverage-macro:
	@echo "Running macro tests with coverage (TEST_LEVEL=$(TEST_LEVEL))..."
	cd $(MACRO_DIR) && \
	PYTHONPATH=$(REPO_ROOT)/bin:$$PYTHONPATH \
	SIM=verilator \
	WAVES=0 \
	COVERAGE=1 \
	COVERAGE_LEGAL=1 \
	TEST_LEVEL=$(TEST_LEVEL) \
	timeout 900 $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

.PHONY: coverage-top
coverage-top:
	@echo "Running top tests with coverage (TEST_LEVEL=$(TEST_LEVEL))..."
	cd $(TOP_DIR) && \
	PYTHONPATH=$(REPO_ROOT)/bin:$$PYTHONPATH \
	SIM=verilator \
	WAVES=0 \
	COVERAGE=1 \
	COVERAGE_LEGAL=1 \
	TEST_LEVEL=$(TEST_LEVEL) \
	timeout 900 $(PYTEST) test_*.py $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE)

# ==============================================================================
# Combined Coverage
# ==============================================================================

.PHONY: coverage-all
coverage-all: coverage-fub coverage-macro coverage-top
	@echo "All coverage runs complete."

.PHONY: coverage-all-gate
coverage-all-gate:
	$(MAKE) coverage-all TEST_LEVEL=gate

.PHONY: coverage-all-func
coverage-all-func:
	$(MAKE) coverage-all TEST_LEVEL=func

.PHONY: coverage-all-full
coverage-all-full:
	$(MAKE) coverage-all TEST_LEVEL=full

# ==============================================================================
# Report Generation
# ==============================================================================

.PHONY: coverage-report
coverage-report:
	@echo "Generating combined coverage report..."
	@$(PYTHON) -c " \
import os, json, glob; \
from datetime import datetime; \
\
levels = ['fub', 'macro', 'top']; \
combined = {'levels': {}, 'totals': {'protocol': 0, 'line': 0, 'count': 0}}; \
\
for level in levels: \
    json_path = f'{level}/coverage_data/combined_{level}_coverage.json'; \
    if os.path.exists(json_path): \
        with open(json_path) as f: \
            data = json.load(f); \
            combined['levels'][level] = data; \
            for r in data.get('test_results', []): \
                combined['totals']['protocol'] += r.get('protocol_pct', 0); \
                combined['totals']['line'] += r.get('line_pct', 0); \
                combined['totals']['count'] += 1; \
\
if combined['totals']['count'] > 0: \
    avg_protocol = combined['totals']['protocol'] / combined['totals']['count']; \
    avg_line = combined['totals']['line'] / combined['totals']['count']; \
else: \
    avg_protocol = avg_line = 0; \
\
lines = ['# Combined Coverage Report', '', f'Generated: {datetime.now()}', '']; \
lines.append('## Overall Summary'); \
lines.append(f'- **Average Protocol Coverage:** {avg_protocol:.1f}%'); \
lines.append(f'- **Average Line Coverage:** {avg_line:.1f}%'); \
lines.append(f'- **Total Tests:** {combined[\"totals\"][\"count\"]}'); \
lines.append(''); \
\
for level in levels: \
    if level in combined['levels']: \
        data = combined['levels'][level]; \
        test_count = len(data.get('test_results', [])); \
        lines.append(f'## {level.upper()} Level ({test_count} tests)'); \
        lines.append('| Test | Protocol % | Line % |'); \
        lines.append('|------|------------|--------|'); \
        for r in data.get('test_results', []): \
            lines.append(f'| {r[\"test_name\"]} | {r[\"protocol_pct\"]:.1f}% | {r[\"line_pct\"]:.1f}% |'); \
        lines.append(''); \
\
os.makedirs('coverage_data/reports', exist_ok=True); \
with open('coverage_data/reports/combined_coverage_report.md', 'w') as f: \
    f.write('\n'.join(lines)); \
print('Report written to: coverage_data/reports/combined_coverage_report.md'); \
"

.PHONY: coverage-full-report
coverage-full-report: clean-coverage coverage-all-full coverage-report
	@echo "Full coverage report complete."

# ==============================================================================
# Utilities
# ==============================================================================

.PHONY: clean-coverage
clean-coverage:
	@echo "Cleaning coverage data..."
	rm -rf $(FUB_DIR)/coverage_data
	rm -rf $(MACRO_DIR)/coverage_data
	rm -rf $(TOP_DIR)/coverage_data
	rm -rf $(TESTS_DIR)/coverage_data
	rm -rf */sim_build
	@echo "Coverage data cleaned."

.PHONY: coverage-status
coverage-status:
	@echo "Coverage Data Status"
	@echo "===================="
	@for level in fub macro top; do \
		echo ""; \
		echo "$$level level:"; \
		if [ -d "$$level/coverage_data/per_test" ]; then \
			count=$$(ls -1 $$level/coverage_data/per_test/*_summary.json 2>/dev/null | wc -l); \
			echo "  - $$count test coverage files"; \
		else \
			echo "  - No coverage data"; \
		fi; \
	done
```

---

## Coverage APIs

### CoverageHelper Class (Recommended)

The simplest way to add coverage to tests:

```python
from projects.components.stream.dv.stream_coverage import CoverageHelper

# Get or create helper instance
coverage = CoverageHelper.get_instance("test_name", log=dut._log)

# Sample scenarios
coverage.sample_scenario("basic_flow")
coverage.sample_scenario("error_handling")

# Sample AXI read transactions
coverage.sample_axi_read(
    burst_type=1,    # 0=FIXED, 1=INCR, 2=WRAP
    burst_size=6,    # 2^size bytes per beat (6=64 bytes)
    burst_len=7      # Number of beats - 1
)

# Sample AXI write transactions
coverage.sample_axi_write(
    burst_type=1,
    burst_size=6,
    burst_len=7,
    response=0       # 0=OKAY, 1=EXOKAY, 2=SLVERR, 3=DECERR
)

# Sample APB transactions
coverage.sample_apb_read()
coverage.sample_apb_write(response=0)

# Sample handshakes (for flow control verification)
coverage.sample_handshake("descriptor_valid_ready")

# Save at end of test
coverage.save()
```

### Automatic BFM Coverage

Hook into GAXI BFMs for automatic transaction coverage:

```python
from projects.components.stream.dv.stream_coverage import (
    CoverageHelper,
    register_bfm_coverage
)

# Initialize coverage
coverage = CoverageHelper.get_instance("test_name")

# After creating testbench and initializing BFMs...
tb = MyModuleTB(dut)
await tb.setup_clocks_and_reset()

# Register all BFMs for automatic coverage sampling
register_bfm_coverage([
    tb.axi_master,
    tb.axi_slave,
    tb.descriptor_master,
    tb.network_slave,
], coverage)

# Run test - coverage is sampled automatically on every transaction!
await tb.run_test()

# Save coverage
coverage.save()
```

**What gets sampled automatically:**
- AXI burst type (FIXED, INCR, WRAP)
- AXI burst size (1B, 2B, 4B, 8B, 16B, 32B, 64B, 128B)
- AXI burst length (1, 2-4, 5-8, 9-16, 17-256)
- AXI response (OKAY, EXOKAY, SLVERR, DECERR)
- Address alignment
- Handshake events

---

## Legal Coverage Mode

### What is Legal Coverage?

Standard AXI4 protocol defines many variations (all burst types, all sizes, etc.). However, most components only support a subset. **Legal coverage** measures coverage against only what the component actually supports.

Example - STREAM component legal variations:
- **Burst Type:** INCR only (no FIXED, no WRAP)
- **Burst Size:** 64 bytes only (matches data width)
- **Burst Length:** 1, 2, 4, 8, 16, 32, 64, 128, 256
- **Response:** OKAY only (errors handled separately)

### Enabling Legal Coverage

```bash
# Enable both coverage and legal coverage mode
COVERAGE=1 COVERAGE_LEGAL=1 pytest test_scheduler.py -v
```

### Defining Legal Variations

Create `legal_coverage_config.py` in your coverage package:

```python
# projects/components/{component}/dv/{component}_coverage/legal_coverage_config.py

from dataclasses import dataclass
from typing import List, Set

@dataclass
class LegalCoverageConfig:
    """Defines what variations this component legally supports."""

    # AXI Burst Types (0=FIXED, 1=INCR, 2=WRAP)
    legal_burst_types: Set[int] = frozenset({1})  # INCR only

    # AXI Burst Sizes (2^n bytes)
    legal_burst_sizes: Set[int] = frozenset({6})  # 64 bytes only

    # AXI Burst Lengths (actual beats, not encoded)
    legal_burst_lengths: Set[int] = frozenset({1, 2, 4, 8, 16, 32, 64, 128, 256})

    # AXI Response codes
    legal_responses: Set[int] = frozenset({0})  # OKAY only

    # APB variations
    legal_apb_responses: Set[int] = frozenset({0})  # OKAY only

    # Required test scenarios
    required_scenarios: List[str] = None

    def __post_init__(self):
        if self.required_scenarios is None:
            self.required_scenarios = [
                'single_channel_transfer',
                'multi_channel_concurrent',
                'descriptor_chaining',
                'backpressure_handling',
                'configuration_update',
            ]

    def get_legal_coverage_points(self) -> dict:
        """Calculate total legal coverage points."""
        return {
            'axi_read': {
                'burst_types': len(self.legal_burst_types),
                'burst_sizes': len(self.legal_burst_sizes),
                'burst_lengths': len(self.legal_burst_lengths),
                'total': (len(self.legal_burst_types) *
                         len(self.legal_burst_sizes) *
                         len(self.legal_burst_lengths))
            },
            'axi_write': {
                'total': (len(self.legal_burst_types) *
                         len(self.legal_burst_sizes) *
                         len(self.legal_burst_lengths) *
                         len(self.legal_responses))
            },
            'scenarios': {
                'total': len(self.required_scenarios)
            }
        }
```

---

## Coverage Data Structure

Coverage data is organized hierarchically:

```
projects/components/{component}/dv/tests/
├── fub/
│   └── coverage_data/
│       ├── per_test/
│       │   ├── scheduler_basic_cid00_nc08_protocol.json
│       │   ├── scheduler_basic_cid00_nc08_summary.json
│       │   └── ...
│       ├── reports/
│       │   └── fub_coverage_report.md
│       └── combined_fub_coverage.json
│
├── macro/
│   └── coverage_data/
│       ├── per_test/
│       │   └── ...
│       ├── reports/
│       │   └── macro_coverage_report.md
│       └── combined_macro_coverage.json
│
├── top/
│   └── coverage_data/
│       ├── per_test/
│       │   └── ...
│       ├── reports/
│       │   └── top_coverage_report.md
│       └── combined_top_coverage.json
│
└── coverage_data/
    └── reports/
        └── combined_coverage_report.md    # All levels combined
```

### Per-Test Files

Each test generates two files:

1. **`{test_name}_protocol.json`** - Detailed protocol coverage bins
2. **`{test_name}_summary.json`** - Summary statistics

Example `_summary.json`:
```json
{
  "test_name": "scheduler_basic_cid00_nc08_aw064_dw0512",
  "protocol_coverage": {
    "axi_read": {"covered": 9, "total": 9, "pct": 100.0},
    "axi_write": {"covered": 9, "total": 9, "pct": 100.0},
    "apb": {"covered": 2, "total": 2, "pct": 100.0},
    "scenarios": {"covered": 5, "total": 5, "pct": 100.0}
  },
  "code_coverage": {
    "line": {"covered": 1250, "total": 1543, "pct": 81.0},
    "toggle": {"covered": 2341, "total": 4521, "pct": 51.8}
  },
  "overall": {
    "protocol_pct": 100.0,
    "line_pct": 81.0,
    "toggle_pct": 51.8
  }
}
```

---

## Aggregating Coverage Across Test Levels

### Automatic Aggregation (via conftest.py)

Each level's `conftest.py` automatically aggregates coverage when tests complete:

1. **pytest_sessionfinish hook** triggers after all tests
2. Reads all `*_summary.json` files in `per_test/`
3. Aggregates totals across all tests
4. Generates level-specific report (e.g., `fub_coverage_report.md`)
5. Saves combined JSON (e.g., `combined_fub_coverage.json`)

### Cross-Level Aggregation (via Makefile)

The `make coverage-report` target combines all level reports:

1. Reads `combined_fub_coverage.json`, `combined_macro_coverage.json`, `combined_top_coverage.json`
2. Calculates overall averages
3. Generates `combined_coverage_report.md` with all levels

### Manual Aggregation

You can also manually aggregate using the report generator:

```bash
# Generate report for specific level
python3 bin/generate_coverage_report.py --coverage-dir fub/coverage_data

# Generate combined report
python3 bin/generate_coverage_report.py \
    --fub-dir fub/coverage_data \
    --macro-dir macro/coverage_data \
    --top-dir top/coverage_data \
    --output coverage_data/reports/combined_report.md
```

---

## Report Generation

### Markdown Report Contents

The generated reports include:

1. **Summary Statistics** - Overall coverage percentages
2. **Per-Level Breakdown** - Coverage by FUB/Macro/Top
3. **Per-Test Results** - Individual test coverage
4. **Protocol Coverage** - AXI/APB transaction coverage bins
5. **Scenario Coverage** - Functional scenario coverage
6. **Coverage Gaps** - Identifies uncovered bins/scenarios

### Example Report Output

```markdown
# Combined Coverage Report

Generated: 2025-01-10 14:30:00

## Overall Summary
- **Average Protocol Coverage:** 95.2%
- **Average Line Coverage:** 78.5%
- **Total Tests:** 15

## FUB Level (8 tests)
| Test | Protocol % | Line % |
|------|------------|--------|
| scheduler_basic_cid00_nc08 | 100.0% | 81.0% |
| scheduler_stress_cid01_nc16 | 100.0% | 85.2% |
| descriptor_engine_basic | 95.0% | 72.1% |
...

## MACRO Level (4 tests)
| Test | Protocol % | Line % |
|------|------------|--------|
| stream_core_single_channel | 100.0% | 79.5% |
| stream_core_multi_channel | 100.0% | 82.3% |
...

## TOP Level (3 tests)
| Test | Protocol % | Line % |
|------|------------|--------|
| stream_top_basic | 85.0% | 75.0% |
| stream_top_full | 95.0% | 80.0% |
...
```

---

## Protocol Coverage Bins

### AXI Coverage Points

| Category | Bins | Notes |
|----------|------|-------|
| Burst Type | FIXED (0), INCR (1), WRAP (2) | Legal coverage may limit |
| Burst Size | 1B, 2B, 4B, 8B, 16B, 32B, 64B, 128B | 2^AWSIZE |
| Burst Length | 1, 2, 4, 8, 16, 32, 64, 128, 256 | AWLEN+1 |
| Response | OKAY, EXOKAY, SLVERR, DECERR | Write response |

### APB Coverage Points

| Category | Bins |
|----------|------|
| Direction | Read, Write |
| Response | OKAY, SLVERR |

### Functional Scenarios

Define component-specific scenarios:

```python
SCENARIOS = [
    'single_channel_transfer',
    'multi_channel_concurrent',
    'descriptor_chaining',
    'backpressure_handling',
    'error_injection',
    'configuration_update',
    'timeout_recovery',
]
```

---

## Best Practices

### 1. Sample at Key Points

Sample coverage at transaction boundaries and state transitions:

```python
# Good: Sample after each transaction completes
async def handle_transaction(self, txn):
    result = await self.execute(txn)
    if coverage:
        coverage.sample_axi_write(
            burst_type=txn.burst_type,
            burst_size=txn.burst_size,
            burst_len=txn.burst_len,
            response=result.response
        )
```

### 2. Use Descriptive Scenario Names

Scenario names appear in reports - make them meaningful:

```python
# Good
coverage.sample_scenario("multi_channel_concurrent_stress")

# Bad
coverage.sample_scenario("test1")
```

### 3. Run Coverage Regularly

Don't wait until the end of development:

```bash
# Quick gate check during development
make coverage-fub-gate

# Functional check before PR
make coverage-all-func
```

### 4. Review Coverage Gaps

The report highlights uncovered bins - review and add targeted tests:

```markdown
## Coverage Gaps

### Uncovered Burst Lengths
- burst_len=128 (not tested)
- burst_len=256 (not tested)

### Uncovered Scenarios
- error_injection (0 hits)
```

### 5. Use Legal Coverage for Accurate Metrics

Standard AXI has 3 burst types * 8 sizes * 256 lengths = 6144 combinations.
If your component only supports 1 * 1 * 9 = 9 combinations, standard coverage
will never exceed ~0.15%. Use legal coverage to measure what matters.

### 6. Clean Before CI Runs

```bash
# In CI pipeline
make coverage-full-report  # Includes clean step
```

---

## Troubleshooting

### Coverage Files Not Created

Check:
1. `COVERAGE=1` environment variable is set
2. Coverage directory has write permissions
3. `coverage.save()` is called in cocotb test
4. Test completed successfully (no crash before save)

### Verilator Coverage Not Working

Check:
1. Verilator version supports coverage (`verilator --version`)
2. Compile args include `--coverage --coverage-line --coverage-toggle`
3. Simulation ran to completion
4. Coverage .dat files exist in sim_build directory

### Report Shows 0% Coverage

Check:
1. Tests ran successfully with `COVERAGE=1`
2. `per_test/` directory contains `.json` files
3. JSON files contain valid data (not empty)
4. conftest.py pytest_sessionfinish hook executed

### Legal Coverage Lower Than Expected

Check:
1. `COVERAGE_LEGAL=1` is set
2. Legal config matches component's actual capabilities
3. Tests exercise all legal variations
4. No illegal variations being sampled

### Aggregation Missing Tests

Check:
1. All test levels ran with same COVERAGE settings
2. Each level's conftest.py has aggregation hooks
3. No test crashes before coverage.save()
4. JSON file naming matches expected patterns

---

## Reference Implementation

See STREAM component for complete reference:

- **Coverage package:** `projects/components/stream/dv/stream_coverage/`
- **Legal config:** `projects/components/stream/dv/stream_coverage/legal_coverage_config.py`
- **FUB tests:** `projects/components/stream/dv/tests/fub/test_scheduler.py`
- **Macro tests:** `projects/components/stream/dv/tests/macro/test_stream_core.py`
- **Top tests:** `projects/components/stream/dv/tests/top/test_stream_top.py`
- **FUB conftest:** `projects/components/stream/dv/tests/fub/conftest.py`
- **Makefile:** `projects/components/stream/dv/tests/Makefile`
- **Methodology doc:** `projects/components/stream/dv/COVERAGE_METHODOLOGY.md`
