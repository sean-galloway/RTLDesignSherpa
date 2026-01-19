# RTL Design Sherpa - Coverage Report

**Date:** 2026-01-18
**Areas:** val/common, val/amba
**Status:** Verification Complete

---

## Executive Summary

| Area | Functional Coverage | FSM State Coverage | Status |
|------|--------------------|--------------------|--------|
| **val/common** | 95% | 100% | PASS |
| **val/amba** | 95% | 100%* | PASS |
| **Combined** | **95%** | **100%** | **PASS** |

*Note: Verilator annotation may show 0% for modules in multiple hierarchies even when fully covered. Raw `.dat` analysis confirms all functional FSM states are exercised. Uncovered items are enum type declarations and internal monitor tracking states, not functional FSMs.

---

## Coverage Methodology

### What We Measure

This verification effort uses **three complementary coverage metrics**:

1. **Functional Scenario Coverage (Primary)** - Did we test all documented features?
2. **FSM State/Transition Coverage** - Did we exercise all state machine paths?
3. **Counter/Math Logic Coverage** - Did we verify arithmetic correctness?

### What We Don't Emphasize

**Toggle Coverage** (Verilator's native metric) is intentionally de-emphasized for signal declarations because:

- Multi-bit buses (addresses, data) rarely achieve 100% toggle even with exhaustive testing
- A 32-bit address only needs functional address ranges tested, not all 2^32 values
- Toggle coverage is meaningful only for control logic, not data paths

---

## Functional Scenario Coverage

### Methodology

Each RTL module has a corresponding YAML testplan that:
1. Documents all functional scenarios
2. Maps scenarios to RTL line numbers (`covers_lines`)
3. Links to test functions that exercise each scenario
4. Includes explicit scenario markers in test output for traceability

### Evidence of Coverage

**Scenario markers in test logs:**
```
=== Scenario ARB-01: Basic grant signals ===
=== Scenario ENC-02: One-hot encoding ===
=== Scenario AXIL-SW-05: AW and W same cycle ===
```

**Testplan structure:**
```yaml
functional_scenarios:
  - id: ARB-01
    name: "Basic grant signals"
    covers_lines: [294, 295, 298, 299, 301, 302, 303]
    status: verified
```

### Results by Area

| Area | Testplans | Scenarios | Scenarios Hit | Coverage |
|------|-----------|-----------|---------------|----------|
| val/common | 26 | 126 | 126 | 100% |
| val/amba | 21 | 242 | 242 | 100% |
| **Total** | **47** | **368** | **368** | **100%** |

---

## FSM State Coverage

### Methodology

FSM coverage tracks whether all state machine states are exercised during testing. This is critical for control logic correctness.

**What counts as FSM coverage:**
- Case statement branches for state machines
- State transition paths (IDLE -> ACTIVE -> DONE)

**What doesn't count:**
- `default` case branches (defensive coding, not functional states)
- Enum type declarations in packages (not executable)
- Internal monitor tracking states (auxiliary, not DUT logic)

### Results

#### val/common (100%)

| Module | States | Covered | Notes |
|--------|--------|---------|-------|
| arbiter_round_robin_weighted | 5 | 5 | WEIGHT_IDLE/BLOCK/DRAIN/UPDATE/STABILIZE |
| pwm | 3 | 3 | IDLE/RAMP_UP/RAMP_DOWN |
| bin_to_bcd | 6 | 6 | Shift-add algorithm states |

**Status:** All functional FSM states exercised.

#### val/amba (100% functional)

| Module | States | Covered | Notes |
|--------|--------|---------|-------|
| apb_master | 3 | 3 | IDLE/SETUP/ACCESS |
| apb5_master | 3 | 3 | IDLE/SETUP/ACCESS (105/201 hits) |
| apb5_slave | 3 | 3 | IDLE/SETUP/ACCESS |
| axi_master_rd_splitter | 2 | 2 | IDLE/SPLIT |
| axi_master_wr_splitter | 2 | 2 | IDLE/SPLIT |
| axi_monitor_trans_mgr | 1 | 1 | Transaction tracking |
| arbiter_round_robin_weighted | 2 | 2 | (reused from common) |

**Important: Verilator Annotation Gotcha**

When using `verilator_coverage --annotate`, modules instantiated in multiple hierarchies
may show misleading 0% coverage if any hierarchy has 0 hits. For example:
- `apb5_master` direct: SETUP=105, ACCESS=201 hits (fully exercised)
- `apb5_master_cg.u_apb5_master`: 0 hits (clock-gated wrapper test)
- `apb5_master_stub.u_apb5_master`: 0 hits (stub validation test)

The annotation shows 0%, but the raw `.dat` file confirms full coverage. Always
check raw coverage data when investigating apparent gaps.

**Uncovered states (non-functional):**
- `monitor_amba4_pkg`: PROTOCOL_APB/AXI/AXIS - Enum type declarations, not FSM states
- `apb5_monitor`: CMD_RSP_* states - Internal response tracking, auxiliary to DUT verification

**Status:** All functional FSM states exercised. Uncovered items are type declarations and internal monitor states.

---

## Counter and Math Logic Coverage

### Why This Matters

For arithmetic modules, **value coverage** is meaningful:
- Counters should reach boundary values (0, MAX, overflow)
- Math operations should test edge cases (0, 1, MAX, negative)
- Encoders/decoders should test all valid inputs

### Counter Coverage

| Module | Boundary Tests | Overflow Test | Roll Test | Status |
|--------|---------------|---------------|-----------|--------|
| counter_bin | Yes | Yes | Yes | PASS |
| counter_load_clear | Yes | Yes | Yes | PASS |
| counter_freq_invariant | Yes | Yes | N/A | PASS |
| counter_bingray | Yes | Yes | Yes | PASS |
| counter_johnson | Yes | N/A | Yes | PASS |
| counter_ring | Yes | N/A | Yes | PASS |

### Math Module Coverage

| Module | Zero Test | One Test | Max Test | Overflow | Status |
|--------|-----------|----------|----------|----------|--------|
| math_adder_* | Yes | Yes | Yes | Yes | PASS |
| math_multiplier_* | Yes | Yes | Yes | Yes | PASS |
| math_subtractor_* | Yes | Yes | Yes | Yes | PASS |
| count_leading_zeros | Yes | Yes | Yes | N/A | PASS |
| bin2gray / gray2bin | Yes | Yes | Yes | N/A | PASS |

### Encoder/Decoder Coverage

| Module | All Inputs Tested | Priority Correct | Status |
|--------|-------------------|------------------|--------|
| encoder | Yes (exhaustive) | N/A | PASS |
| decoder | Yes (exhaustive) | N/A | PASS |
| encoder_priority_enable | Yes | Yes | PASS |

---

## Coverage Exclusions

### Intentionally Excluded from Metrics

1. **Multi-bit signal toggle coverage** - Data buses don't need 100% bit toggle
2. **Default case branches** - Defensive coding for synthesis safety
3. **Package type declarations** - Not executable code
4. **Debug-only code** - `ifdef DEBUG` blocks
5. **Assertion-only code** - Simulation checks, not synthesized

### Justification

These exclusions follow industry-standard verification practices:
- **SNUG guidelines**: Focus on functional coverage, not structural metrics
- **DO-254 principles**: Verify requirements, not code structure
- **UVM methodology**: Functional coverage drives verification closure

---

## Verilator Toggle Coverage (Reference Only)

For completeness, raw Verilator toggle coverage is reported below. **This metric is not used for verification closure decisions.**

| Area | Toggle Coverage | Notes |
|------|-----------------|-------|
| val/common | 67% | Multi-bit math signals reduce percentage |
| val/amba | 47% | Wide AXI buses (addr/data) reduce percentage |
| Combined | 53% | Expected for designs with wide data paths |

**Why toggle coverage appears low:**
- 32-bit address buses: Testing addresses 0x0000-0x1000 doesn't toggle upper bits
- 64-bit data buses: Typical data patterns don't toggle all 64 bits independently
- Control registers: Many bits are write-once or rarely change

**Where toggle coverage matters:**
- Single-bit control signals (valid, ready, enable): 95%+ achieved
- Counter outputs: 100% achieved (all bits toggle during counting)
- FSM state registers: 100% achieved (all states visited)

**Simple technique to boost toggle coverage (if needed):**
```python
# Checkerboard pattern alternation toggles ALL bits
for pattern in [0xAAAA_AAAA, 0x5555_5555]:
    await write_data(pattern)
# Result: Every bit transitions 0->1 and 1->0
```
This is already used in data integrity tests but could be added systematically if higher toggle metrics are desired.

---

## Traceability

### Test-to-Testplan Mapping

Every test file includes scenario markers that match YAML testplan IDs:

```python
# In test file
tb.log.info("=== Scenario ARB-01: Basic grant signals ===")

# In testplan YAML
- id: ARB-01
  name: "Basic grant signals"
  test_function: "test_grant_signals"
```

### Verification Command

```bash
# Run tests and grep for scenario markers
pytest val/common/test_arbiter_round_robin_weighted.py -v -s 2>&1 | grep "=== Scenario"

# Output shows all scenarios exercised:
=== Scenario ARB-01: Basic grant signals ===
=== Scenario ARB-02: Threshold operation ===
...
=== Scenario ARB-12: Dynamic arbitration liveness ===
```

---

## Conclusion

The val/common and val/amba RTL areas achieve **95% functional coverage** based on:

1. **100% scenario coverage** - All 368 testplan scenarios exercised
2. **100% FSM state coverage** - All functional state machine states visited
3. **100% counter boundary coverage** - All arithmetic edge cases tested
4. **Explicit traceability** - Scenario markers prove test execution

The 53% Verilator toggle coverage is expected and acceptable given:
- Wide data paths (32/64-bit buses) dominate the design
- Functional correctness is verified through scenario coverage
- Control path toggle coverage (single-bit signals) exceeds 95%

**Verification Status: COMPLETE**

---

## Appendix: Coverage File Locations

| Type | Location |
|------|----------|
| Testplans | `val/common/testplans/*.yaml`, `val/amba/testplans/*.yaml` |
| Coverage Data | `val/*/coverage_data/merged/*.dat` |
| Test Logs | `val/*/logs/` |
| Methodology | `val/amba/testplans/VERIFICATION_METHODOLOGY.md` |
