# Makefile Hierarchy Guide

**Version:** 1.0
**Last Updated:** 2025-10-24
**Purpose:** Complete guide to the three-tier Makefile hierarchy

---

## Three-Tier Makefile Hierarchy

The repository uses a three-tier Makefile structure for organized testing and linting:

```
$REPO_ROOT/Makefile                          # Tier 1: Repository-level master
├─> projects/components/Makefile              # Tier 2: Components-level master (NEW!)
    ├─> stream/rtl/Makefile                   # Tier 3: Component-specific lint
    ├─> stream/dv/tests/Makefile              # Tier 3: Component-specific tests
    ├─> rapids/rtl/Makefile                   # Tier 3: Component-specific lint
    ├─> rapids/dv/tests/Makefile              # Tier 3: Component-specific tests
    └─> {component}/...                       # Tier 3: Other components
```

---

## Tier 1: Repository-Level Master ($REPO_ROOT/Makefile)

**Purpose:** Coordinate validation + projects testing and linting

**Location:** `/mnt/data/github/rtldesignsherpa/Makefile`

**Key Targets:**
```bash
# Test ALL (validation + projects)
make test-all

# Test validation subsystems (val/amba, val/common)
make test-val

# Test all projects
make test-projects

# REG_LEVEL targets for validation
make run-common-{gate|func|full}-parallel
make run-amba-{gate|func|full}-parallel
make run-rtl-all-{gate|func|full}-parallel

# Lint
make lint-all
make lint-rtl
make lint-projects

# Status
make status
make status-tests
make status-lint
```

**Delegation:**
- `make test-projects` → calls `projects/components/Makefile test-all`
- `make lint-projects` → calls `projects/components/Makefile lint-all`
- `make test-stream` → calls `projects/components/Makefile test-stream`
- `make lint-stream` → calls `projects/components/Makefile lint-stream`

---

## Tier 2: Components-Level Master (projects/components/Makefile)

**Purpose:** Coordinate all component testing and linting

**Location:** `/mnt/data/github/rtldesignsherpa/projects/components/Makefile` ← **NEW!**

**Key Targets:**
```bash
# Test all components
make test-all                      # Serial, FUNC level
make test-all-parallel             # Parallel, FUNC level
make test-all-gate-parallel        # Parallel, GATE level
make test-all-func-parallel        # Parallel, FUNC level
make test-all-full-parallel        # Parallel, FULL level

# Test specific component
make test-stream                   # STREAM FUNC level
make test-stream-gate              # STREAM GATE level
make test-stream-func              # STREAM FUNC level
make test-stream-full              # STREAM FULL level
make test-stream-parallel          # STREAM FUNC parallel
make test-stream-gate-parallel     # STREAM GATE parallel
make test-stream-func-parallel     # STREAM FUNC parallel
make test-stream-full-parallel     # STREAM FULL parallel

# Same pattern for: rapids, bridge, delta, apb_hpet, apb_xbar

# Lint all components
make lint-all

# Lint specific component
make lint-stream
make lint-rapids
# ... etc

# Status
make status
make status-tests
make status-lint

# Clean
make clean-all
make clean-tests
make clean-lint
make clean-stream
make clean-rapids
# ... etc
```

**Delegation:**
- `make test-stream` → calls `stream/dv/tests/Makefile run-all`
- `make lint-stream` → calls `stream/rtl/Makefile lint-all`
- Similar for all components

---

## Tier 3: Component-Specific Makefiles

**Purpose:** Execute tests or lint for a single component

### Component DV Test Makefile (component/dv/tests/Makefile)

**Locations:**
- `projects/components/stream/dv/tests/Makefile`
- `projects/components/rapids/dv/tests/Makefile`
- ... etc

**Key Targets:**
```bash
# Basic test execution
make run-fub                       # FUB tests, FUNC level
make run-macro                     # Macro tests, FUNC level
make run-all                       # All tests, FUNC level

# Parallel execution
make run-fub-parallel              # FUB, 48 workers
make run-macro-parallel            # Macro, 48 workers
make run-all-parallel              # All, 48 workers

# REG_LEVEL control (serial)
make run-fub-gate                  # FUB, GATE level
make run-fub-func                  # FUB, FUNC level (default)
make run-fub-full                  # FUB, FULL level
make run-macro-gate                # Macro, GATE level
make run-macro-func                # Macro, FUNC level
make run-macro-full                # Macro, FULL level
make run-all-gate                  # All, GATE level
make run-all-func                  # All, FUNC level
make run-all-full                  # All, FULL level

# REG_LEVEL control (parallel - 48 workers)
make run-fub-gate-parallel         # FUB, GATE, 48 workers
make run-fub-func-parallel         # FUB, FUNC, 48 workers
make run-fub-full-parallel         # FUB, FULL, 48 workers
make run-macro-gate-parallel       # Macro, GATE, 48 workers
make run-macro-func-parallel       # Macro, FUNC, 48 workers
make run-macro-full-parallel       # Macro, FULL, 48 workers
make run-all-gate-parallel         # All, GATE, 48 workers
make run-all-func-parallel         # All, FUNC, 48 workers
make run-all-full-parallel         # All, FULL, 48 workers

# Collection (verify without running)
make collect-fub
make collect-macro
make collect-all

# Clean
make clean-fub
make clean-macro
make clean-all
make clean-logs
make clean-pycache
make clean-build
make clean-vcd

# Utility
make list-fub
make list-macro
make status
make help
```

### Component RTL Lint Makefile (component/rtl/Makefile)

**Locations:**
- `projects/components/stream/rtl/Makefile`
- `projects/components/rapids/rtl/Makefile`
- ... etc

**Key Targets:**
```bash
# Lint execution
make lint-all                      # Run all lint tools
make verilator                     # Verilator lint only
make verible                       # Verible lint (if installed)
make yosys                         # Yosys synthesis check (if installed)

# Reports
make report                        # Generate lint summary
make status                        # Show RTL status

# Clean
make clean-all                     # Remove all lint artifacts
```

---

## Usage Examples by Tier

### Tier 1: Repository-Level Examples

```bash
# From repo root - test everything
cd $REPO_ROOT
make test-all                      # Val + all components
make lint-all                      # Val + all components

# Test validation subsystems with REG_LEVEL
make run-common-gate-parallel      # Quick COMMON smoke test
make run-amba-func-parallel        # AMBA functional tests
make run-rtl-all-full-parallel     # Comprehensive validation

# Test specific component from root
make test-stream                   # Delegates to components/Makefile
make lint-rapids                   # Delegates to components/Makefile
```

### Tier 2: Components-Level Examples

```bash
# From components directory - coordinate all components
cd $REPO_ROOT/projects/components

# Test all components
make test-all                      # Serial, takes ~3 hours
make test-all-func-parallel        # Parallel, takes ~30 min

# Quick smoke test all components
make test-all-gate-parallel        # Parallel gate tests, ~10 min

# Test specific component
make test-stream-func-parallel     # STREAM functional, parallel
make test-rapids-gate              # RAPIDS quick smoke test

# Lint all components
make lint-all                      # Takes ~5 min

# Status of all components
make status
make status-tests
make status-lint
```

### Tier 3: Component-Level Examples

```bash
# From specific component - focused work
cd $REPO_ROOT/projects/components/stream/dv/tests

# Quick iterative development
make run-fub-gate                  # Quick smoke test
make run-fub-func                  # Functional test
make run-fub-full                  # Comprehensive test

# Parallel execution
make run-all-func-parallel         # All tests, 48 workers

# Lint the RTL
cd ../../rtl
make lint-all
make report
```

---

## Command Flow Examples

### Example 1: "Test Everything"

```bash
# From repo root
cd $REPO_ROOT
make test-all

# Flow:
# 1. Root Makefile: make test-all
#    ├─> Calls: make test-val (validation tests)
#    └─> Calls: cd projects/components && make test-all
#
# 2. Components Makefile: make test-all
#    ├─> Calls: cd stream/dv/tests && make run-all
#    ├─> Calls: cd rapids/dv/tests && make run-all
#    └─> ... (all components)
#
# 3. Component Makefile: make run-all
#    └─> Runs: pytest -v fub_tests/test_*.py macro_tests/test_*.py
```

### Example 2: "Lint All Components"

```bash
# From repo root
cd $REPO_ROOT
make lint-projects

# Flow:
# 1. Root Makefile: make lint-projects
#    └─> Calls: cd projects/components && make lint-all
#
# 2. Components Makefile: make lint-all
#    ├─> Calls: cd stream/rtl && make lint-all
#    ├─> Calls: cd rapids/rtl && make lint-all
#    └─> ... (all components)
#
# 3. Component RTL Makefile: make lint-all
#    ├─> Runs: verilator --lint-only *.sv
#    └─> Runs: verible-verilog-lint *.sv (if installed)
```

### Example 3: "Quick Smoke Test of STREAM"

```bash
# Option 1: From repo root
cd $REPO_ROOT
make test-stream-gate-parallel

# Option 2: From components directory
cd $REPO_ROOT/projects/components
make test-stream-gate-parallel

# Option 3: From component directory (most direct)
cd $REPO_ROOT/projects/components/stream/dv/tests
make run-all-gate-parallel

# Flow (all options):
# 1. Root or Components Makefile: make test-stream-gate-parallel
#    └─> Calls: cd stream/dv/tests && make run-all-gate-parallel
#
# 2. Component DV Makefile: make run-all-gate-parallel
#    └─> Runs: REG_LEVEL=GATE pytest -v -n 48 fub_tests/test_*.py macro_tests/test_*.py
```

---

## When to Use Each Tier

### Use Tier 1 (Root Makefile) When:
- ✅ Running complete repository validation (val + projects)
- ✅ CI/CD pipeline for entire repository
- ✅ Comprehensive regression before release
- ✅ Testing validation subsystems (COMMON, AMBA)

### Use Tier 2 (Components Makefile) When:
- ✅ Testing/linting all components together
- ✅ Component-level CI/CD
- ✅ Comparing status across components
- ✅ Quick way to run tests on multiple components

### Use Tier 3 (Component Makefile) When:
- ✅ Focused development on single component
- ✅ Iterative test-debug cycle
- ✅ Detailed component-specific testing (FUB vs macro)
- ✅ Quick feedback during development

---

## Best Practices

### Development Workflow

```bash
# 1. Start at Tier 3 - focused component work
cd $REPO_ROOT/projects/components/stream/dv/tests
make run-fub-gate                  # Quick smoke test

# 2. Iterate with Tier 3
# Edit RTL → make run-fub-gate → Debug → Repeat
cd ../../rtl
make verilator                     # Check lint
cd ../dv/tests
make run-fub-func                  # More comprehensive test

# 3. Expand to Tier 2 - verify impact on other components
cd $REPO_ROOT/projects/components
make test-all-gate-parallel        # Quick test all components

# 4. Finalize with Tier 1 - complete validation
cd $REPO_ROOT
make test-all                      # Full validation + projects
```

### CI/CD Pipeline

```bash
# Stage 1: Quick smoke test (5-10 min)
cd $REPO_ROOT
make run-rtl-all-gate-parallel     # Validation gate tests
cd projects/components
make test-all-gate-parallel        # Component gate tests

# Stage 2: Functional tests (30-60 min)
cd $REPO_ROOT
make run-rtl-all-func-parallel     # Validation functional
cd projects/components
make test-all-func-parallel        # Component functional

# Stage 3: Lint (5-10 min)
cd $REPO_ROOT
make lint-all                      # All RTL lint

# Stage 4: Comprehensive (overnight)
cd $REPO_ROOT
make run-rtl-all-full-parallel     # Validation comprehensive
cd projects/components
make test-all-full-parallel        # Component comprehensive
```

---

## Quick Reference

### Complete Target Matrix

| What | Tier 1 (Root) | Tier 2 (Components) | Tier 3 (Component) |
|------|--------------|---------------------|-------------------|
| **Test all** | `make test-all` | `make test-all` | `make run-all` |
| **Test STREAM** | `make test-stream` | `make test-stream` | (navigate to stream) |
| **Test GATE** | N/A (val only) | `make test-all-gate-parallel` | `make run-all-gate-parallel` |
| **Test FUNC** | N/A (val only) | `make test-all-func-parallel` | `make run-all-func-parallel` |
| **Test FULL** | N/A (val only) | `make test-all-full-parallel` | `make run-all-full-parallel` |
| **Lint all** | `make lint-all` | `make lint-all` | `make lint-all` |
| **Lint STREAM** | `make lint-stream` | `make lint-stream` | (navigate to stream/rtl) |
| **Status** | `make status` | `make status` | `make status` |
| **Clean** | `make clean-all` | `make clean-all` | `make clean-all` |

---

## See Also

- `projects/components/MAKEFILE_GUIDE.md` - Detailed component Makefile guide
- `projects/components/CLAUDE.md` - AI assistant guidance for components
- `projects/components/PRD.md` - Component design standards
- Root `/Makefile` - Repository master Makefile

---

**Version:** 1.0
**Last Updated:** 2025-10-24
**Maintained By:** RTL Design Sherpa Project
