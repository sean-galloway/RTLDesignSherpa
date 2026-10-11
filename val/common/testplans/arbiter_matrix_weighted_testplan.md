# Test Plan: arbiter_matrix_weighted

## Module: rtl/common/arbiter_matrix_weighted.sv
## Test File: val/common/test_arbiter_matrix_weighted.py
## Scenarios

| ID | Scenario | Description | Tested | Coverage Gap |
|----|----------|-------------|--------|--------------|
| AMW-01 | Weighted sequence | Documented consecutive-grant sequence (e.g., CLIENTS=3 weights [3,1,2] → [0,0,0,1,2,2]) | YES | - |
| AMW-02 | One-hot / request match | Grant is one-hot or zero and only granted to a requesting, eligible client | YES | - |
| AMW-03 | Zero weight | A weight=0 client is never granted | YES | - |
| AMW-04 | Weight change mid-stream | New weight takes effect at the next credit reload | YES | - |
| AMW-05 | Single requester | A lone requester is granted in the next cycle | YES | - |
| AMW-06 | Reset order | Client 0 wins the first grant after reset | YES | - |
| AMW-07 | block_arb | Arbitration pauses while block_arb is asserted | YES | - |
| AMW-08 | Idle gap | Rotation remains correct after a partial-request idle gap | YES | - |
| AMW-09 | grant_ack hold | Grant held until the winning client acknowledges | YES | - |
| AMW-10 | Foreign-ack immunity | ACK bits from non-granted clients are ignored | YES | - |
| AMW-11 | Same-cycle handoff | Next grant issued in the same cycle the ACK arrives | YES | - |
| AMW-12 | Single-requester ACK | A lone requester is re-granted after each ACK | YES | - |
| AMW-13 | Various CLIENTS (1,2,4,5,8) | Different client counts in no-ACK mode | YES | - |
| AMW-14 | ACK mode parameter sweep | WAIT_GNT_ACK=1 at REG_LEVEL=GATE and FULL | YES | - |
| AMW-15 | Non-uniform weights per level | At least one non-uniform weight pattern per REG_LEVEL | YES | - |
| AMW-16 | Single-client degenerate branch | CLIENTS==1 grants immediately and credits reload in both ACK and no-ACK modes | YES | - |
| AMW-17 | Mid-credit idle | A multi-credit winner idles mid-turn; others proceed and credits persist | YES | - |

## Uncovered Lines Analysis

No measured coverage data is recorded in this plan. Run:

```bash
COVERAGE=1 REG_LEVEL=GATE pytest val/common/test_arbiter_matrix_weighted.py -v
```

and inspect `coverage.dat` / `make coverage-report` output if a coverage-driven
review is required.

## Action Items

1. ~~Collect Verilator line/toggle coverage for the new credit-counter paths, the
   single-client degenerate branch (`CLIENTS==1`), and the ACK-mode handoff.~~
   Directed tests now cover `CLIENTS==1` in both ACK and no-ACK modes.
2. If coverage holes remain in the conditional matrix-update logic, add targeted
   directed tests or extend the weighted-sequence window.

## Recommended Test Additions

```python
async def test_weight_reload_timing(dut):
    """Verify reload happens exactly when a counter reaches 0."""
    # 1. Drive weight=2 for client 0 and weight=1 for all others.
    # 2. Request all clients continuously.
    # 3. Confirm client 0 wins twice consecutively, then rotates.
```

## Test Commands

```bash
# Default functional regression (no-ACK only)
TEST_LEVEL=func venv/bin/python -m pytest val/common/test_arbiter_matrix_weighted.py -q

# Gate-level smoke (includes ACK mode)
REG_LEVEL=GATE TEST_LEVEL=gate venv/bin/python -m pytest val/common/test_arbiter_matrix_weighted.py -q

# Full regression (includes ACK mode)
REG_LEVEL=FULL TEST_LEVEL=full venv/bin/python -m pytest val/common/test_arbiter_matrix_weighted.py -q

# With coverage
COVERAGE=1 REG_LEVEL=GATE pytest val/common/test_arbiter_matrix_weighted.py -v
```

<!-- ============================================================ -->

## Notes

This test plan follows the same structure as `arbiter_matrix_testplan.md`. The
weighted matrix arbiter reuses the base matrix's ACK-mode directed tests and
adds credit-counter-specific checks for consecutive-grant weight scheduling.
