# Coverage Tracking - RTL Design Sherpa

**Last Updated:** 2026-03-20
**Purpose:** Track Verilator code coverage rollout across all test environments
**Goal:** Every component supports `make coverage` and `make coverage-report`

---

## Root Makefile Targets

The root Makefile has unified coverage targets:
- `make coverage` - Run tests with coverage (STREAM, RAPIDS, Bridge, Converters)
- `make coverage-report` - Generate coverage reports
- `make coverage-unified` - Generate unified cross-component report
- `make clean-coverage` - Clean all coverage artifacts

---

## Coverage Status by Component

### projects/components/

| Component | Coverage Makefile Targets | Coverage Scripts | Status |
|-----------|--------------------------|------------------|--------|
| **stream** | `run-coverage`, `run-coverage-parallel`, `run-coverage-full`, `coverage-report`, `fresh-coverage` | `bin/generate_coverage_report.py` | DONE |
| **rapids** | `coverage-full-report`, `coverage-report`, `clean-coverage` | Uses `bin/cov_utils/` | DONE |
| **bridge** | `run-coverage`, `run-coverage-func`, `coverage-report`, `fresh-coverage`, `clean-coverage` | Uses shared `bin/cov_utils/conftest_coverage.py` | DONE |
| **converters** | `run-coverage`, `run-coverage-parallel`, `coverage-report`, `fresh-coverage`, `clean-coverage` | Uses shared `bin/cov_utils/conftest_coverage.py` | DONE |
| **apb_xbar** | - | - | TODO |
| **retro_legacy_blocks** | - | - | TODO |
| **delta** | - | - | TODO (no tests yet) |
| **bch** | - | - | TODO (no tests yet) |
| **hive** | - | - | TODO (no tests yet) |
| **timing_characterization** | - | - | TODO |

### val/ (RTL Validation)

| Area | Coverage Makefile Targets | Status |
|------|--------------------------|--------|
| **val/common** | conftest.py has coverage hooks | PARTIAL (needs Makefile targets) |
| **val/amba** | conftest.py has coverage hooks | PARTIAL (needs Makefile targets) |
| **val/integ_common** | - | TODO |
| **val/integ_amba** | - | TODO |

---

## Infrastructure Improvements (2026-03-20)

### Completed

1. **Shared conftest coverage module** (`bin/cov_utils/conftest_coverage.py`)
   - Eliminates duplicated coverage aggregation code across conftest.py files
   - Uses MAX-based hit merging (not SUM) for correct deduplication
   - Merges both Verilator .dat files AND protocol JSON summaries

2. **Bridge + Converters wired into root Makefile**
   - `make coverage` now runs all four components
   - `make coverage-report` generates reports for all four

3. **Unified cross-component report** (`bin/cov_utils/unified_coverage_report.py`)
   - `make coverage-unified` generates a single dashboard
   - Separate thresholds: 95% line, 90% branch, 85% toggle, 80% protocol
   - JSON output for CI integration

4. **Coverage waivers** (`bin/cov_utils/coverage_waivers.yaml`)
   - Structured per-exclusion rationale with reviewer, date, category
   - Replaces informal glob-only exclusions

5. **Separate line/branch/toggle reporting** (`verilator_coverage.py`)
   - New `get_merged_coverage_breakdown()` returns per-type metrics
   - Reports now show each coverage type individually

6. **CI coverage gate** (`.github/workflows/coverage.yml`)
   - Runs on push/PR to main
   - Runs all component coverage, generates unified report
   - Fails PR if coverage below thresholds

7. **Auto-detect scenario status** (`functional_coverage_tracker.py`)
   - Parses JUnit XML from pytest `--junitxml` output
   - Maps test results to testplan scenarios automatically
   - Falls back to manual status when XML not available

### What Needs to Be Done Per Component

Each component's `dv/tests/Makefile` needs these targets:

```makefile
COVERAGE_DIR = coverage_data

.PHONY: run-coverage
run-coverage:
    COVERAGE=1 REG_LEVEL=FUNC $(PYTEST) $(TEST_FILES) $(PYTEST_VERBOSE)

.PHONY: coverage-report
coverage-report:
    python3 $(REPO_ROOT)/bin/cov_utils/generate_coverage_report.py --component <name>

.PHONY: fresh-coverage
fresh-coverage: clean-coverage run-coverage coverage-report

.PHONY: clean-coverage
clean-coverage:
    rm -rf $(COVERAGE_DIR) coverage_html
```

Each component's `conftest.py` should use the shared module:
```python
from cov_utils.conftest_coverage import aggregate_all_coverage

def _aggregate_coverage():
    base_dir = os.path.dirname(os.path.abspath(__file__))
    aggregate_all_coverage(base_dir, 'component_name')
```

### Reference Implementations

- **STREAM coverage:** `projects/components/stream/dv/tests/fub/Makefile`
- **RAPIDS coverage:** `projects/components/rapids/dv/tests/Makefile`
- **Bridge coverage:** `projects/components/bridge/dv/tests/Makefile` (uses shared module)
- **Converters coverage:** `projects/components/converters/dv/tests/Makefile` (uses shared module)
- **Shared coverage utils:** `bin/cov_utils/` (16 files)

---

## Priority Order (Remaining)

1. **apb_xbar** - Has tests, moderate complexity
2. **retro_legacy_blocks** - Has tests
3. **timing_characterization** - Has tests (45 tests)
4. **val/common** - Large test suite, needs Makefile targets
5. **val/amba** - Large test suite, needs Makefile targets
6. **val/integ_common** - Integration tests
7. **val/integ_amba** - Integration tests
8. **delta, bch, hive** - Need tests first

---

## Coverage Goals

- **Line:** 95%+ (production target from rtl_coverage_guidelines.md)
- **Branch:** 90%+
- **Toggle:** 85-90%
- **Protocol:** 80%+
- **Report:** Unified cross-component report via `make coverage-unified`
