<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Component-Level Makefile Guide

**Version:** 1.0
**Last Updated:** 2025-10-24
**Purpose:** Guide for using and maintaining component-level Makefiles

---

## Overview

Every component in `projects/components/` has **two Makefiles** that mirror the root Makefile structure:

```
projects/components/{component}/
├── rtl/Makefile              # RTL Lint targets
└── dv/tests/Makefile         # DV Test targets with REG_LEVEL support
```

**Current Status:** All components have complete Makefile infrastructure ✅

| Component | DV Makefile | RTL Makefile | Status |
|-----------|-------------|--------------|--------|
| **stream** | ✅ REG_LEVEL + Parallel | ✅ Lint | Complete |
| **rapids** | ✅ REG_LEVEL + Parallel | ✅ Lint | Complete |
| **apb_hpet** | ✅ REG_LEVEL + Parallel | ✅ Lint | Complete |
| **apb_xbar** | ✅ REG_LEVEL + Parallel | ✅ Lint | Complete |
| **bridge** | ✅ REG_LEVEL + Parallel | ✅ Lint | Complete |

---

## DV Test Makefile (dv/tests/Makefile)

### Standard Targets

All component DV Makefiles provide these targets:

#### Basic Test Execution
```bash
make run-fub              # Run FUB (Functional Unit Block) tests
make run-macro            # Run macro/integration tests
make run-all              # Run all tests
```

#### Parallel Execution (48 workers)
```bash
make run-fub-parallel     # FUB tests in parallel
make run-macro-parallel   # Macro tests in parallel
make run-all-parallel     # All tests in parallel
```

#### REG_LEVEL Control (Configurable Test Depth)

**Test Levels:**
- **GATE** - Quick smoke tests (~5 min per subsystem)
- **FUNC** - Functional coverage tests (~30 min per subsystem) - DEFAULT
- **FULL** - Comprehensive validation (~4 hours per subsystem)

**Serial Execution:**
```bash
make run-fub-gate         # Quick FUB smoke test
make run-fub-func         # FUB functional test (default)
make run-fub-full         # FUB comprehensive test

make run-macro-gate       # Quick macro smoke test
make run-macro-func       # Macro functional test (default)
make run-macro-full       # Macro comprehensive test

make run-all-gate         # All tests - quick
make run-all-func         # All tests - functional (default)
make run-all-full         # All tests - comprehensive
```

**Parallel Execution:**
```bash
make run-fub-gate-parallel    # Quick FUB - 48 workers
make run-fub-func-parallel    # FUB functional - 48 workers
make run-fub-full-parallel    # FUB comprehensive - 48 workers

make run-macro-gate-parallel  # Quick macro - 48 workers
make run-macro-func-parallel  # Macro functional - 48 workers
make run-macro-full-parallel  # Macro comprehensive - 48 workers

make run-all-gate-parallel    # All quick - 48 workers
make run-all-func-parallel    # All functional - 48 workers (default)
make run-all-full-parallel    # All comprehensive - 48 workers
```

#### Test Collection (Verification Without Running)
```bash
make collect-fub          # Verify FUB test imports
make collect-macro        # Verify macro test imports
make collect-all          # Verify all test imports
```

#### Clean Targets
```bash
make clean-fub            # Remove FUB test artifacts
make clean-macro          # Remove macro test artifacts
make clean-all            # Remove all test artifacts
make clean-logs           # Remove log files
make clean-pycache        # Remove Python cache
make clean-build          # Remove sim build directories
make clean-vcd            # Remove waveform files
```

#### Utility Targets
```bash
make list-fub             # List FUB test modules
make list-macro           # List macro test modules
make status               # Show test status and coverage
make help                 # Show all available targets
```

---

## RTL Lint Makefile (rtl/Makefile)

### Standard Targets

All component RTL Makefiles provide these targets:

#### Lint Execution
```bash
make lint-all             # Run all lint tools (verilator + verible)
make verilator            # Run Verilator lint only
make verible              # Run Verible lint only (if installed)
make yosys                # Run Yosys synthesis check (if installed)
```

#### Reports
```bash
make report               # Generate lint summary report
make status               # Show RTL status and file counts
```

#### Clean
```bash
make clean-all            # Remove all lint artifacts
```

**Lint Output Location:**
```
rtl/lint_reports/
├── verilator/            # Verilator reports
│   ├── summary.txt
│   └── {module}.log
├── verible/              # Verible reports (if run)
│   ├── summary.txt
│   └── {module}.log
└── yosys/                # Yosys reports (if run)
    ├── summary.txt
    └── {module}.log
```

---

## Usage Examples

### Example 1: Quick Smoke Test of Component

```bash
# Navigate to component
cd $REPO_ROOT/projects/components/stream/dv/tests

# Run quick gate-level test
make run-all-gate

# Expected runtime: ~5 minutes
```

### Example 2: Full Validation with Parallel Execution

```bash
# Navigate to component
cd $REPO_ROOT/projects/components/rapids/dv/tests

# Run comprehensive tests in parallel
make run-all-full-parallel

# Expected runtime: ~4 hours with 48 workers
```

### Example 3: Lint Component RTL

```bash
# Navigate to RTL directory
cd $REPO_ROOT/projects/components/stream/rtl

# Run all lint tools
make lint-all

# View summary
make report
```

### Example 4: Development Workflow

```bash
# 1. Modify RTL
vim projects/components/stream/rtl/stream_fub/scheduler.sv

# 2. Lint the RTL
cd projects/components/stream/rtl
make verilator

# 3. Run quick smoke test
cd ../dv/tests
make run-fub-gate

# 4. If passing, run functional tests
make run-fub-func

# 5. Clean up
make clean-all
```

### Example 5: CI/CD Pipeline

```bash
#!/bin/bash
# CI script for component validation

COMPONENT=$1  # stream, rapids, etc.

cd $REPO_ROOT/projects/components/$COMPONENT

# Step 1: Lint RTL
echo "Linting $COMPONENT RTL..."
cd rtl
make lint-all || exit 1

# Step 2: Run gate-level tests (quick)
echo "Running $COMPONENT gate tests..."
cd ../dv/tests
make run-all-gate-parallel || exit 1

# Step 3: Run functional tests
echo "Running $COMPONENT functional tests..."
make run-all-func-parallel || exit 1

echo "✓ $COMPONENT validation complete"
```

---

## Integration with Root Makefile

The root Makefile delegates to component Makefiles:

```bash
# From repository root
make test-stream          # Calls projects/components/stream/dv/tests/Makefile
make lint-stream          # Calls projects/components/stream/rtl/Makefile
```

**Root Makefile targets:**
```bash
make test-all             # Run all component tests
make test-projects        # Run all project tests
make test-stream          # Run STREAM tests
make test-rapids          # Run RAPIDS tests
make test-bridge          # Run Bridge tests
make test-apb_hpet        # Run APB HPET tests
make test-apb_xbar        # Run APB Crossbar tests

make lint-all             # Lint all RTL (root + projects)
make lint-projects        # Lint all project RTL
make lint-stream          # Lint STREAM RTL
make lint-rapids          # Lint RAPIDS RTL
# ... etc
```

---

## Makefile Template for New Components

When creating a new component, copy the Makefile structure from an existing component:

```bash
# Copy DV test Makefile from STREAM
cp projects/components/stream/dv/tests/Makefile \
   projects/components/new_component/dv/tests/Makefile

# Copy RTL lint Makefile from STREAM
cp projects/components/stream/rtl/Makefile \
   projects/components/new_component/rtl/Makefile

# Update component name in both Makefiles (search for "STREAM", replace with "NEW_COMPONENT")
```

**Key sections to update:**
1. Header comment block (component name, description)
2. Help text (component-specific descriptions)
3. Test directory names (if different from FUB/macro pattern)

---

## Prerequisites

### Environment Setup

All Makefiles require sourced environment:
```bash
source $REPO_ROOT/env_python
```

This sets:
- `$REPO_ROOT` - Repository root path
- Python virtual environment with CocoTB and dependencies

### Required Tools

**For DV Tests:**
- Python 3.6+
- pytest
- pytest-xdist (for parallel execution)
- CocoTB framework
- Icarus Verilog or Verilator (simulator)

**For RTL Lint:**
- Verilator (required)
- Verible (optional but recommended)
- Yosys (optional for synthesis checks)

---

## REG_LEVEL Environment Variable

The `REG_LEVEL` environment variable controls test parametrization:

**How It Works:**
```python
# In test files (e.g., test_scheduler.py)
def generate_test_params():
    """Generate test parameters based on REG_LEVEL"""
    reg_level = os.environ.get('REG_LEVEL', 'FUNC').upper()

    if reg_level == 'GATE':
        # Minimal parameters for quick smoke test
        return [(8, 512)]  # 1 configuration
    elif reg_level == 'FUNC':
        # Default functional coverage
        return [(8, 512), (16, 256), (32, 512)]  # 3 configurations
    elif reg_level == 'FULL':
        # Comprehensive validation
        return [(8, 512), (16, 256), (32, 512), (64, 128), (128, 512)]  # 5 configurations
```

**Makefile Usage:**
```makefile
.PHONY: run-fub-gate
run-fub-gate:
	REG_LEVEL=GATE $(PYTEST) $(PYTEST_VERBOSE) $(FUB_TESTS_DIR)/test_*.py
```

**Manual Override:**
```bash
# Set environment variable directly
export REG_LEVEL=FULL
make run-fub

# Or inline
REG_LEVEL=GATE make run-fub
```

---

## Parallel Execution

All component Makefiles support parallel test execution using pytest-xdist:

**Configuration:**
- Default worker count: **48 workers**
- Retry failed tests: **3 retries with 1 second delay**

**Example:**
```bash
make run-all-func-parallel
# Equivalent to:
# pytest -v --tb=short -n 48 --reruns 3 --reruns-delay 1 fub_tests/test_*.py macro_tests/test_*.py
```

**Benefits:**
- STREAM functional tests: 30 min → ~5 min with parallelization
- RAPIDS functional tests: 45 min → ~8 min with parallelization

**Worker ID Handling:**
Tests automatically detect parallel execution via `PYTEST_XDIST_WORKER` environment variable and adjust:
- Test names (append worker ID for uniqueness)
- Log file paths (separate per worker)
- Simulation build directories (isolated per worker)

---

## Best Practices

### During Development

1. **Start with gate-level tests** - Quick feedback loop
   ```bash
   make run-fub-gate
   ```

2. **Lint before committing** - Catch issues early
   ```bash
   cd rtl && make lint-all
   ```

3. **Run functional tests before PR** - Ensure quality
   ```bash
   make run-all-func-parallel
   ```

### During CI/CD

1. **Use parallel execution** - Maximize throughput
2. **Run gate + func levels** - Balance speed vs coverage
3. **Collect first** - Verify imports before running
   ```bash
   make collect-all && make run-all-gate-parallel
   ```

### During Release

1. **Run full validation** - Leave overnight
   ```bash
   make run-all-full-parallel
   ```

2. **Generate reports** - Document lint status
   ```bash
   cd rtl && make report
   ```

---

## Troubleshooting

### Issue: "REPO_ROOT is not set"

**Solution:**
```bash
source $REPO_ROOT/env_python
# Or from repo root:
source env_python
```

### Issue: Tests fail due to import errors

**Solution:**
```bash
# Verify test collection first
make collect-all

# If errors, check Python path and module structure
```

### Issue: Parallel tests timeout

**Solution:**
```bash
# Reduce worker count
PYTEST_XDIST="-n 24" make run-all-parallel

# Or run serially
make run-all
```

### Issue: Lint reports not generated

**Solution:**
```bash
# Check tool availability
which verilator
which verible

# Install missing tools or skip
make verilator  # Run only verilator
```

---

## Quick Reference Card

```
COMPONENT TEST TARGETS                    COMPONENT LINT TARGETS
==========================                =======================
make run-fub                              make lint-all
make run-fub-gate                         make verilator
make run-fub-func                         make verible
make run-fub-full                         make report
make run-fub-parallel                     make status
make run-fub-gate-parallel                make clean-all
make run-fub-func-parallel
make run-fub-full-parallel                ROOT MAKEFILE DELEGATION
make run-all                              =======================
make run-all-gate-parallel                make test-stream
make run-all-func-parallel                make test-rapids
make run-all-full-parallel                make lint-stream
make clean-all                            make lint-rapids
make status                               make test-all
make help                                 make lint-all
```

---

## See Also

- Root `/Makefile` - Master Makefile with project-level targets
- Root `/PRD.md` - Overall testing and validation strategy
- `projects/components/CLAUDE.md` - AI assistant guidance for components
- `projects/components/PRD.md` - Component design standards

---

**Version:** 1.0
**Last Updated:** 2025-10-24
**Maintained By:** RTL Design Sherpa Project
