# Test Plan: arbiter_matrix

## Module: rtl/common/arbiter_matrix.sv
## Test File: val/common/test_arbiter_matrix.py
## Current Coverage: TBD (Verilator line coverage not yet measured)

## Scenarios

| ID | Scenario | Description | Tested | Coverage Gap |
|----|----------|-------------|--------|--------------|
| AMX-01 | Single requester | Only one client requesting | YES | - |
| AMX-02 | All requesters | All clients requesting simultaneously | YES | - |
| AMX-03 | Strong fairness | Each client served once per CLIENTS consecutive grants | YES | - |
| AMX-04 | Matrix update | Priority matrix drops winner to lowest priority after grant | YES | - |
| AMX-05 | Cold start / gaps | Rotation is correct from reset and after partial-request idle gaps | YES | - |
| AMX-06 | Reset order | Client 0 wins the first grant after reset | YES | - |
| AMX-07 | block_arb | Arbitration pauses while block_arb is asserted | YES | - |
| AMX-08 | grant_ack hold | Grant held until the winning client acknowledges | YES | - |
| AMX-09 | Foreign-ack immunity | ACK bits from non-granted clients are ignored | YES | - |
| AMX-10 | Same-cycle handoff | Next grant is issued in the same cycle the ACK arrives | YES | - |
| AMX-11 | Single-requester ACK | A lone requester is re-granted after each ACK | YES | - |
| AMX-12 | Various CLIENTS (2,4,5,8) | Different client counts in no-ACK mode | YES | - |
| AMX-13 | ACK mode parameter sweep | WAIT_GNT_ACK=1 at REG_LEVEL=GATE and FULL | YES | - |

## Uncovered Lines Analysis

TBD: run `COVERAGE=1 REG_LEVEL=GATE pytest val/common/test_arbiter_matrix.py -v`
and inspect `coverage.dat` / `make coverage-report` output.

## Action Items

1. Collect Verilator line/toggle coverage for the new ACK-mode paths and the
   single-client degenerate branch (`CLIENTS==1`).
2. If coverage holes remain in the matrix-update logic, add targeted directed
   tests or extend the existing fairness window.

## Recommended Test Additions

```python
async def test_grant_ack_handshake(dut):
    """Test proper grant acknowledgment flow"""
    # 1. Assert requests[0]
    # 2. Wait for grant[0]
    # 3. Assert grant_ack[0]
    # 4. Verify arbiter moves to next requester in the same cycle
    # 5. Repeat for all clients
```

## Test Commands

```bash
# Default functional regression (no-ACK only)
TEST_LEVEL=func venv/bin/python -m pytest val/common/test_arbiter_matrix.py -q

# Gate-level smoke (includes ACK mode)
REG_LEVEL=GATE TEST_LEVEL=gate venv/bin/python -m pytest val/common/test_arbiter_matrix.py -q

# Full regression (includes ACK mode)
REG_LEVEL=FULL TEST_LEVEL=full venv/bin/python -m pytest val/common/test_arbiter_matrix.py -q

# With coverage
COVERAGE=1 REG_LEVEL=FUNC pytest val/common/test_arbiter_matrix.py -v
```

<!-- ============================================================ -->

## Notes

This test plan was created during review round 1 for `arbiter_matrix`. The
ACK-mode directed tests (`test_ack_hold_until_owner_ack`,
`test_ack_foreign_ack_immunity`, `test_ack_back_to_back_handoff`,
`test_ack_single_requester`) exercise the same-cycle ACK handoff added to match
`arbiter_round_robin` Rule 4.
