# Bridge Testplans

This directory contains YAML testplans for all bridge configurations, following the format used in `val/amba/testplans/`.

## Purpose

Testplans document:
- Functional scenarios covered by tests
- Parameter combinations tested
- Coverage gaps and limitations
- RTL-to-test mapping

## Testplan Files

### Tested Configurations (9 total - 75%)

1. **bridge_1x2_testplan.yaml** - Single master, dual slaves (rd/wr variants)
   - Status: FULLY TESTED
   - Tests: test_bridge_1x2_rd.py, test_bridge_1x2_wr.py
   - Coverage: 100% (8/8 scenarios)

2. **bridge_1x3_testplan.yaml** - Single master, triple slaves (rd/wr variants)
   - Status: FULLY TESTED
   - Tests: test_bridge_1x3_rd.py, test_bridge_1x3_wr.py
   - Coverage: 100% (8/8 scenarios)

3. **bridge_1x4_testplan.yaml** - Single master, quad slaves with APB (rd/wr variants)
   - Status: PARTIALLY TESTED
   - Tests: test_bridge_1x4_rd.py, test_bridge_1x4_wr.py
   - Coverage: 62.5% (5/8 scenarios)
   - Gap: APB converter placeholder (Phase 3 pending)

4. **bridge_1x5_testplan.yaml** - Single master, five slaves with AXIL (rd/wr variants)
   - Status: PARTIALLY TESTED
   - Tests: test_bridge_1x5_rd.py, test_bridge_1x5_wr.py
   - Coverage: 55.6% (5/9 scenarios)
   - Gap: APB and AXIL converters placeholder (Phase 3 pending)

5. **bridge_2x2_rw_testplan.yaml** - Dual master, dual slaves, full duplex
   - Status: FULLY TESTED
   - Tests: test_bridge_2x2_rw.py
   - Coverage: 100% (11/11 scenarios)

### Untested Configurations (3 total - 25% GAP)

6. **bridge_4x4_rw_testplan.yaml** - Quad master, quad slaves, full duplex
   - Status: ⚠️ NOT TESTED
   - Tests: NONE (test file does not exist)
   - Coverage: 0% (0/10 scenarios)
   - Risk: HIGH - Generated RTL completely untested

7. **bridge_5x3_channels_testplan.yaml** - Five masters (mixed channels), three slaves
   - Status: ⚠️ NOT TESTED
   - Tests: NONE (test file does not exist)
   - Coverage: 0% (0/11 scenarios)
   - Risk: HIGH - Complex channel optimization untested

### Hand-Written Modules

8. **bridge_cam_testplan.yaml** - Content Addressable Memory for ID tracking
   - Status: INTEGRATION TESTED
   - Tests: Verified via all bridge tests (no standalone test)
   - Coverage: 81.8% (9/11 scenarios verified, 2 partial)
   - Note: Foundational module tested through bridges

## Testplan Format

Each testplan follows this structure:

```yaml
module: bridge_name
rtl_file: path/to/rtl
test_file: path/to/test

# Module description
parameters:
  - name: PARAM_NAME
    default: value
    description: explanation

address_map:
  - slave: name
    base: 0xADDRESS
    range: 0xSIZE
    description: purpose

functional_scenarios:
  - id: BRIDGE-XX-YY
    name: "Scenario name"
    description: What is tested
    test_function: "cocotb_test_function_name"
    covers_features:
      - Feature 1
      - Feature 2
    priority: high/medium/low
    status: verified/partial/not_tested
    notes: (optional) Additional context

parameter_coverage:
  - param1: value1
    param2: value2
    test_level: basic/medium/full
    status: verified/partial/not_tested

implied_coverage:
  total_scenarios: N
  verified_scenarios: M
  implied_percentage: (M/N * 100)
  notes: Coverage explanation

notes: |
  Overall testplan summary and context
```

## Coverage Summary

### Overall Bridge Coverage

| Configuration | Tests | Scenarios | Coverage | Status |
|--------------|-------|-----------|----------|--------|
| bridge_1x2 (rd/wr) | 2 | 8/8 | 100% | ✅ VERIFIED |
| bridge_1x3 (rd/wr) | 2 | 8/8 | 100% | ✅ VERIFIED |
| bridge_1x4 (rd/wr) | 2 | 5/8 | 62.5% | ⚠️ PARTIAL |
| bridge_1x5 (rd/wr) | 2 | 5/9 | 55.6% | ⚠️ PARTIAL |
| bridge_2x2_rw | 1 | 11/11 | 100% | ✅ VERIFIED |
| bridge_4x4_rw | 0 | 0/10 | 0% | ❌ NOT TESTED |
| bridge_5x3_channels | 0 | 0/11 | 0% | ❌ NOT TESTED |
| bridge_cam | integration | 9/11 | 81.8% | ✅ INTEGRATION |

**Total**: 9 test files, 12 configurations (including variants)

**Coverage by test status**:
- Fully tested: 5 configs (42%)
- Partially tested: 2 configs (17%)
- Not tested: 3 configs (25%)
- Integration tested: 1 config (8%)
- Hand-written: 1 module (8%)

**Total scenario coverage**: 46/76 scenarios verified (60.5%)

### Gap Analysis

**Critical Gaps** (High Risk):
1. bridge_4x4_rw - Completely untested
   - Complex 4-master arbitration
   - No test file exists
   - RTL may contain bugs

2. bridge_5x3_channels - Completely untested
   - Most complex configuration
   - Channel optimization unverified
   - No test file exists
   - RTL may contain bugs

**Medium Gaps** (Moderate Risk):
1. bridge_1x4 APB support - Partial (APB converter placeholder)
2. bridge_1x5 APB/AXIL support - Partial (converters placeholder)

**Low Gaps** (Acceptable):
1. bridge_cam Mode 2 - Structure verified, edge cases need explicit test
2. bridge_cam pipelined eviction - Needs explicit test

## Recommendations

### Immediate Actions (Priority 1)

1. **Create test_bridge_4x4_rw.py**
   - Follow bridge_2x2_rw pattern
   - Verify 4-way arbitration
   - Test all 10 scenarios

2. **Create test_bridge_5x3_channels.py**
   - Follow bridge_2x2_rw pattern
   - Verify channel-specific routing
   - Test all 11 scenarios

### Phase 3 Actions (Priority 2)

1. **Implement APB converter** (bridge_1x4, bridge_1x5)
   - AXI4 to APB protocol conversion
   - Complete APB-related scenarios

2. **Implement AXIL converter** (bridge_1x5)
   - AXI4 to AXI4-Lite conversion
   - Burst splitting
   - Complete AXIL-related scenarios

### Optional Improvements (Priority 3)

1. **Create standalone CAM test**
   - Mode 2 (ALLOW_DUPLICATES=1) edge cases
   - Pipelined eviction (PIPELINE_EVICT=1)
   - Explicit timing verification

2. **Add stress tests**
   - High transaction rates
   - Sustained contention
   - CAM capacity limits

## Usage

### Viewing Testplans

```bash
# View specific testplan
cat bridge_1x2_testplan.yaml

# View all testplans
ls -la *.yaml

# Search for coverage gaps
grep -r "not_tested" *.yaml
grep -r "partial" *.yaml
```

### Creating New Testplans

When adding a new bridge configuration:

1. Generate RTL first (using bridge_generator.py)
2. Create corresponding test file
3. Create testplan YAML documenting:
   - All functional scenarios
   - Parameter combinations
   - Coverage status
4. Run tests and verify coverage
5. Update testplan with actual results

### Testplan Maintenance

Update testplans when:
- Adding new test scenarios
- Fixing bugs (document what was broken)
- Improving coverage
- Adding new bridge configurations
- Completing Phase 3 converters

## References

- **Format reference**: `/mnt/data/github/rtldesignsherpa/val/amba/testplans/axil4_slave_wr_testplan.yaml`
- **Bridge architecture**: `projects/components/bridge/docs/BRIDGE_ARCHITECTURE.md`
- **Test files**: `projects/components/bridge/dv/tests/test_bridge_*.py`
- **RTL files**: `projects/components/bridge/rtl/generated/bridge_*/`

## Version

- **Created**: 2025-01-18
- **Format**: YAML testplan (following val/amba/testplans pattern)
- **Coverage baseline**: 60.5% (46/76 scenarios verified)
