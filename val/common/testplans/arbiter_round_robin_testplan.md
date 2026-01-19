# Test Plan: arbiter_round_robin

## Module: rtl/common/arbiter_round_robin.sv
## Test File: val/common/test_arbiter_round_robin.py
## Current Coverage: ~90%

## Scenarios

| ID | Scenario | Description | Tested | Coverage Gap |
|----|----------|-------------|--------|--------------|
| ARR-01 | Single requester | Only one client requesting | YES | - |
| ARR-02 | All requesters | All clients requesting simultaneously | YES | - |
| ARR-03 | Round-robin fairness | Verify fair rotation of grants | YES | - |
| ARR-04 | Priority update | Mask updates after grant | YES | - |
| ARR-05 | grant_ack handshake | Client acknowledges grant before next | NO | w_mask_decode, w_win_mask_decode |
| ARR-06 | Pending client tracking | r_pending_client management | NO | r_pending_client uncovered |
| ARR-07 | Other requests filter | w_other_requests excluding ACK'd | NO | w_other_requests uncovered |
| ARR-08 | REG_OUTPUT=0 (combo) | Combinational output mode | YES | - |
| ARR-09 | REG_OUTPUT=1 (pipelined) | Registered output mode | YES | - |
| ARR-10 | Various CLIENTS (2,4,8) | Different client counts | YES | - |

## Uncovered Lines Analysis

```
%000008     input  logic                rst_n,
%000000     input  logic [CLIENTS-1:0]  grant_ack,
%000000     logic [CLIENTS-1:0] w_mask_decode [CLIENTS];
%000000     logic [CLIENTS-1:0] w_win_mask_decode [CLIENTS];
%000000     logic [N-1:0]       r_pending_client;
%000000     logic [CLIENTS-1:0] w_other_requests;
```

## Action Items

1. **ARR-05/06/07**: The `grant_ack` input is not being exercised in current tests.
   Need to add tests that:
   - Assert grant_ack after receiving a grant
   - Verify arbiter behavior with pending acknowledgments
   - Test back-to-back grants with proper handshaking

2. **Root Cause**: Current tests may not be using the grant_ack signal at all,
   treating the arbiter as "grant and forget" rather than proper handshake protocol.

## Recommended Test Additions

```python
async def test_grant_ack_handshake(dut):
    """Test proper grant acknowledgment flow"""
    # 1. Assert requests[0]
    # 2. Wait for grant[0]
    # 3. Assert grant_ack[0]
    # 4. Verify arbiter moves to next requester
    # 5. Repeat for all clients
```

## Test Commands

```bash
# Run with coverage
COVERAGE=1 REG_LEVEL=FUNC pytest val/common/test_arbiter_round_robin.py -v
```
