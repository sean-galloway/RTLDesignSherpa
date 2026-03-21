# Coverage Tracking - RTL Design Sherpa

**Last Updated:** 2026-03-19
**Purpose:** Track Verilator code coverage rollout across all test environments
**Goal:** Every component supports `make coverage` and `make coverage-report`

---

## Root Makefile Targets

The root Makefile has unified coverage targets:
- `make coverage` - Run tests with coverage (all supported components)
- `make coverage-report` - Generate coverage reports
- `make clean-coverage` - Clean all coverage artifacts

---

## Coverage Status by Component

### projects/components/

| Component | Coverage Makefile Targets | Coverage Scripts | Status |
|-----------|--------------------------|------------------|--------|
| **stream** | `run-coverage`, `run-coverage-parallel`, `run-coverage-full`, `coverage-report`, `fresh-coverage` | `bin/generate_coverage_report.py` | DONE |
| **rapids** | `coverage-full-report`, `coverage-report`, `clean-coverage` | Uses `bin/cov_utils/` | DONE |
| **bridge** | - | - | TODO |
| **apb_xbar** | - | - | TODO |
| **converters** | - | - | TODO |
| **retro_legacy_blocks** | - | - | TODO |
| **delta** | - | - | TODO (no tests yet) |
| **bch** | - | - | TODO (no tests yet) |
| **hive** | - | - | TODO (no tests yet) |
| **timing_characterization** | - | - | TODO |

### val/ (RTL Validation)

| Area | Coverage Makefile Targets | Status |
|------|--------------------------|--------|
| **val/common** | - | TODO |
| **val/amba** | - | TODO |
| **val/integ_common** | - | TODO |
| **val/integ_amba** | - | TODO |

---

## What Needs to Be Done Per Component

### 1. Add Verilator Coverage to Makefile

Each component's `dv/tests/Makefile` needs these targets:

```makefile
# Coverage targets
COVERAGE_DIR = coverage_data

.PHONY: run-coverage
run-coverage:
    REG_LEVEL=FUNC $(PYTEST) $(TEST_FILES) \
        --verilator-coverage \
        --coverage-dir $(COVERAGE_DIR) \
        -v

.PHONY: run-coverage-full
run-coverage-full:
    REG_LEVEL=FULL $(PYTEST) $(TEST_FILES) \
        --verilator-coverage \
        --coverage-dir $(COVERAGE_DIR) \
        -v -n logical

.PHONY: coverage-report
coverage-report:
    python3 $(REPO_ROOT)/bin/cov_utils/generate_coverage_report.py \
        --coverage-dir $(COVERAGE_DIR)

.PHONY: clean-coverage
clean-coverage:
    rm -rf $(COVERAGE_DIR) coverage_html
```

### 2. Reference Implementations

- **STREAM FUB coverage:** `projects/components/stream/dv/tests/fub/Makefile` (lines 404-435)
- **RAPIDS coverage:** `projects/components/rapids/dv/tests/Makefile` (lines 655-709)
- **Shared coverage utils:** `bin/cov_utils/` (13 files)

### 3. Coverage Report Generation

The `bin/cov_utils/` framework provides:
- `generate_coverage_report.py` - HTML/text report generation
- `verilator_coverage.py` - Verilator coverage data parsing
- `coverage_exclusions.txt` - Exclusion patterns for known uncoverable code
- `functional_coverage_tracker.py` - Functional coverage tracking
- `calc_coverage_excluding_building_blocks.py` - Exclude reused blocks from metrics

### 4. Update Root Makefile

As components gain coverage support, update the root `Makefile` `coverage` target to include them.

---

## Priority Order

1. **bridge** - Has tests, high complexity, most benefit from coverage
2. **apb_xbar** - Has tests, moderate complexity
3. **converters** - Has tests
4. **retro_legacy_blocks** - Has tests
5. **timing_characterization** - Has tests (45 tests)
6. **val/common** - Large test suite, high impact
7. **val/amba** - Large test suite, high impact
8. **val/integ_common** - Integration tests
9. **val/integ_amba** - Integration tests
10. **delta, bch, hive** - Need tests first

---

## Coverage Goals

- **Target:** >80% line coverage for all components with tests
- **Stretch:** >90% line + branch coverage
- **Report:** Unified HTML report accessible from root
