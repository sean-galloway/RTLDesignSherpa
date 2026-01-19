# Test Plan: arbiter_round_robin_simple

## Module: rtl/common/arbiter_round_robin_simple.sv
## Test File: val/common/test_arbiter_round_robin_simple.py
## Current Coverage: ~90% (GOOD)

## Module Overview

Rotating-priority arbiter without if/case ladders:
- Uses rotation and lowest-set-bit isolate: x & (~x + 1)
- Remembers last granted index in r_last_grant
- grant_valid when any request granted
- grant is one-hot, grant_id is encoded index

## Scenarios

| ID | Scenario | Description | Tested | Coverage Gap |
|----|----------|-------------|--------|--------------|
| ARRS-01 | Reset state | r_last_grant = N-1 | YES | rst_n low hits |
| ARRS-02 | Single request | One agent requests | YES | - |
| ARRS-03 | Round robin | Multiple agents fair sharing | YES | - |
| ARRS-04 | Priority rotation | Verify rotation after grant | YES | - |
| ARRS-05 | No requests | request = 0 | YES | - |
| ARRS-06 | All requests | All bits set simultaneously | YES | - |
| ARRS-07 | Shift amount=0 | r_last_grant at N-1 | PARTIAL | w_shift_amount=0 |
| ARRS-08 | Shift amount=N-1 | r_last_grant at 0 | YES | - |
| ARRS-09 | grant_id stable | No grant → keeps last | UNKNOWN | May need check |
| ARRS-10 | Parameter N=4 | Default configuration | YES | - |
| ARRS-11 | Parameter N=8 | Larger configuration | UNKNOWN | May not be tested |

## Uncovered Lines Analysis

```
%000007     input  logic          rst_n,         // active-low reset
 000070     logic [N-1:0] w_rot_sel;
 000084     )   // End of always_ff
```

The coverage shows:
- rst_n: 7 hits (minimal reset assertions)
- w_rot_sel: 70 hits (lower than request 1034 hits)
- always_ff end: 84 hits

Most logic is well-exercised (60K+ clock hits, 180K+ always_comb evaluations).

## Root Cause Analysis

The arbiter is well-tested overall. Minor gaps:
1. Reset path is minimally exercised
2. w_rot_sel might not exercise all bit patterns

## Action Items

1. **ARRS-01**: More reset exercises:
   - Assert reset mid-operation
   - Multiple reset cycles
   - Verify r_last_grant returns to N-1

2. **ARRS-07**: Test shift_amount=0 path more:
   - Ensure r_last_grant reaches N-1
   - Verify request passes through unmodified

3. **ARRS-11**: Test larger N:
   - N=8 configuration
   - Verify all agents get fair service

## Recommended Test Additions

```python
async def test_reset_mid_operation(dut):
    """Test reset during active arbitration"""
    dut.request.value = 0xF  # All requesting
    for _ in range(5):
        await RisingEdge(dut.clk)

    # Assert reset
    dut.rst_n.value = 0
    await RisingEdge(dut.clk)
    # r_last_grant should be N-1 (3 for N=4)

    dut.rst_n.value = 1
    await RisingEdge(dut.clk)
    # First grant should go to agent 0 (after N-1)

async def test_shift_amount_zero(dut):
    """Test when r_last_grant = N-1 (shift_amount = 0)"""
    N = 4
    # Grant to agent N-1 to set r_last_grant = N-1
    dut.request.value = (1 << (N-1))  # Only agent N-1 requests
    for _ in range(N):  # May need multiple cycles
        await RisingEdge(dut.clk)
        if dut.grant.value == (1 << (N-1)):
            break

    # Now r_last_grant should be N-1, shift_amount = 0
    # Next request should use unrotated priority
    dut.request.value = 0b1111
    await RisingEdge(dut.clk)
    assert dut.grant.value == 0b0001  # Agent 0 wins
```

## Test Commands

```bash
# Run with coverage
COVERAGE=1 REG_LEVEL=FUNC pytest val/common/test_arbiter_round_robin_simple.py -v
```
