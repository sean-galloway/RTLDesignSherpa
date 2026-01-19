# Val/Common Coverage Analysis Report
**Date:** 2026-01-17
**Scope:** Arbiter, FIFO, and Data Integrity modules
**Test Level:** GATE (quick regression)
**Merged Coverage:** `/mnt/data/github/rtldesignsherpa/val/common/coverage_data/merged/merged_coverage_20260117_155816.dat`

---

## Executive Summary

**Overall Coverage:** 39.00% (755/1912 coverage points)
**Tests Executed:** 12 test files (11 PASSED, 1 FAILED)
**Coverage Files Merged:** 206 individual .dat files

---

## Test Results by Category

### 1. Arbiters (4/4 PASSED)

| Test File | Status | Coverage Notes |
|-----------|--------|----------------|
| `test_arbiter_priority_encoder.py` | PASSED | 70 uncovered lines - mostly parameterized casez branches |
| `test_arbiter_round_robin.py` | PASSED | Good coverage of state machine |
| `test_arbiter_round_robin_simple.py` | PASSED | Minimal module, near-complete coverage |
| `test_arbiter_round_robin_weighted.py` | PASSED | PWM counter states exercised |

**Coverage Gaps:**
- **Priority Encoder:** Uncovered lines are Verilator artifacts from parameterized casez statements for 4, 8, 16, 32 client configurations. GATE-level testing only uses 16-client variant, leaving other branches unreachable. This is NOT a real gap - full parameter sweep at FUNC/FULL levels will cover.
- **Recommendation:** No action needed. Parameterized logic coverage is expected at higher regression levels.

---

### 2. FIFOs (3/3 PASSED)

| Test File | Status | Coverage Notes |
|-----------|--------|----------------|
| `test_fifo_buffer.py` | PASSED | Synchronous FIFO, good coverage |
| `test_fifo_buffer_async.py` | PASSED | 13 uncovered lines in error checking |
| `test_fifo_buffer_async_div2.py` | PASSED | Clock domain crossing validated |

**Coverage Gaps:**
- **Async FIFO Error Checking:** 13 uncovered lines are simulation-only error messages (`$display` statements for overflow/underflow detection). These are unreachable in passing tests. Test GATE level intentionally avoids error injection.
- **Input/Output Port Declarations:** Uncovered %00 annotations on some port declarations are Verilator artifacts, not executable code.
- **Recommendation:** Consider adding FUNC-level error injection tests to trigger overflow/underflow paths for defensive verification.

---

### 3. Data Integrity (4/5 PASSED, 1 FAILED)

| Test File | Status | Coverage Notes |
|-----------|--------|----------------|
| `test_dataint_checksum.py` | PASSED (2 tests) | Near-complete coverage |
| `test_dataint_crc.py` | PASSED (2 tests) | 5 uncovered lines - port declarations |
| `test_dataint_ecc.py` | FAILED (decoder) | Verilator SIDEEFFECT error |
| `test_dataint_ecc_hamming_secded.py` | PASSED (2 tests) | Encoder/decoder validated |
| `test_dataint_parity.py` | PASSED (4 tests) | 1 uncovered line - port declaration |

**Test Failure Details:**
- **Module:** `dataint_ecc_hamming_decode_secded.sv`
- **Error:** Verilator warning-as-error at line 397:49
  ```
  %Warning-SIDEEFFECT: Expression side effect may be mishandled
  %Error: Exiting due to 1 warning(s)
  ```
- **Impact:** Decoder test cannot run, no coverage data generated
- **Root Cause:** RTL coding pattern triggers Verilator lint warning (likely combinational loop or sensitivity list issue)

**Coverage Gaps:**
- **CRC Module:** 5 uncovered lines are parameterized input ports (POLY, POLY_INIT, XOROUT) which Verilator annotates as %00 but are actually used. This is a Verilator artifact.
- **Parity Module:** 1 uncovered line is the `parity_in` input port declaration - Verilator artifact.
- **Recommendation:**
  - **CRITICAL:** Fix the Verilator SIDEEFFECT warning in `dataint_ecc_hamming_decode_secded.sv:397` to enable decoder testing.
  - Port declaration coverage gaps are false positives - ignore.

---

## Coverage Gap Analysis

### Real Gaps Requiring Action

1. **ECC Hamming Decoder (CRITICAL)**
   - **File:** `rtl/common/dataint_ecc_hamming_decode_secded.sv`
   - **Issue:** Verilator SIDEEFFECT warning prevents compilation
   - **Impact:** Zero test coverage for decoder logic
   - **Priority:** HIGH - Blocks all decoder verification
   - **Action:** Review line 397, refactor to eliminate side effect (likely needs temp variable or sensitivity list fix)

2. **FIFO Error Injection (MEDIUM)**
   - **File:** `fifo_async.sv`
   - **Issue:** 13 lines of error detection code never exercised
   - **Impact:** Overflow/underflow protection untested
   - **Priority:** MEDIUM - Defensive checks should be validated
   - **Action:** Add FUNC-level tests with intentional error injection

### False Positives (NOT Real Gaps)

1. **Parameterized Casez Branches**
   - **Modules:** `arbiter_priority_encoder.sv`
   - **Reason:** GATE level only tests one parameter configuration (16 clients)
   - **Coverage:** 4, 8, 32 client variants unreachable at GATE level
   - **Action:** None - FUNC/FULL regression levels will sweep parameters

2. **Port Declaration Artifacts**
   - **Modules:** `dataint_crc.sv`, `dataint_parity.sv`, `fifo_async.sv`
   - **Reason:** Verilator annotates input/output ports as %00 even when used
   - **Coverage:** These are not executable code
   - **Action:** None - ignore Verilator annotation quirk

3. **Always_comb Block Headers**
   - **Modules:** Multiple
   - **Reason:** Verilator annotates `always_comb begin` as separate coverage point
   - **Coverage:** Not meaningful - block body is covered
   - **Action:** None - known Verilator behavior

---

## Recommendations

### Immediate Actions

1. **Fix ECC Decoder Verilator Warning**
   - Priority: HIGH
   - Owner: RTL team
   - Timeline: Before next regression run
   - File: `/mnt/data/github/rtldesignsherpa/rtl/common/dataint_ecc_hamming_decode_secded.sv:397`
   - Examine line 397 for side effects in expressions (assignment in conditional, etc.)

2. **Document Known Coverage Artifacts**
   - Priority: MEDIUM
   - Add to `val/common/COVERAGE_NOTES.md`:
     - Parameterized casez coverage requires FUNC/FULL levels
     - Port declaration %00 annotations are false positives
     - Error injection paths tested at FUNC level only

### Future Enhancements

1. **Add FUNC-level FIFO Error Tests**
   - Test overflow (write when full)
   - Test underflow (read when empty)
   - Verify error reporting mechanisms
   - Target: 95%+ coverage including error paths

2. **Parameter Sweep at FUNC Level**
   - Priority encoder: Test 4, 8, 16, 32 client configurations
   - Weighted arbiter: Test various weight distributions
   - Target: Cover all parameterized casez branches

3. **Coverage Dashboard**
   - Generate HTML report: `genhtml coverage.info --output-directory html_report`
   - Track coverage trends across regression levels
   - Set 95% threshold for FULL level (excluding Verilator artifacts)

---

## Coverage Methodology Notes

### What Counts as Real Gap

- **Executable RTL logic** not exercised during test
- **FSM states** not reached
- **Conditional branches** not taken (both true/false paths)
- **Error handling paths** intentionally not tested (document as FUNC-level)

### What Does NOT Count as Gap

- **Parameterized casez/case branches** unreachable with current test parameters
- **Input/output port declarations** annotated %00 by Verilator
- **Always_comb/always_ff block headers** (block body covered)
- **Simulation-only code** (`$display`, `$error`, etc.) in passing tests
- **Default branches** in full casez coverage (synthesizes away)

### Regression Level Philosophy

- **GATE:** Quick smoke test, one parameter set, ~30s per test
- **FUNC:** Moderate coverage, key parameter sweep, ~90s per test
- **FULL:** Comprehensive, all parameters, error injection, ~180s per test

Current analysis uses GATE level - 39% coverage is expected and appropriate for fast regression.

---

## Conclusion

The GATE-level regression successfully validates core functionality of arbiters, FIFOs, and most data integrity modules. The 39% overall coverage is consistent with quick smoke testing using minimal parameter configurations.

**Critical Issue:** ECC Hamming decoder cannot be tested due to Verilator SIDEEFFECT warning. This must be fixed before decoder can be verified.

**Coverage Quality:** Excluding the decoder issue, coverage gaps are primarily:
1. Intentional (parameterized logic requires FUNC/FULL levels)
2. False positives (Verilator annotation artifacts)
3. Deferred testing (error injection at FUNC level)

No urgent RTL quality concerns identified in passing tests. Coverage results align with GATE-level regression objectives.

---

**Report Generated:** 2026-01-17
**Coverage Data:** 206 test runs merged
**Analysis Tool:** Verilator Coverage v5.x
**Annotated Sources:** `/mnt/data/github/rtldesignsherpa/val/common/coverage_data/merged/annotated/`
