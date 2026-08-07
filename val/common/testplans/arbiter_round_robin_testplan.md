# Test Plan: arbiter_round_robin

## Module: rtl/common/arbiter_round_robin.sv
## Test File: val/common/test_arbiter_round_robin.py
## Current Coverage: **94.6** (Verilator line, measured 2026-08-07)
<!-- The "~90%" that stood here had no measurement behind it. Verilator
     line/toggle coverage had never been collected for val/common at all. -->

## Scenarios

| ID | Scenario | Description | Tested | Coverage Gap |
|----|----------|-------------|--------|--------------|
| ARR-01 | Single requester | Only one client requesting | YES | - |
| ARR-02 | All requesters | All clients requesting simultaneously | YES | - |
| ARR-03 | Round-robin fairness | Verify fair rotation of grants | YES | - |
| ARR-04 | Priority update | Mask updates after grant | YES | - |
| ARR-05 | grant_ack handshake | Client acknowledges grant before next | YES | WAIT_GNT_ACK=1 is half of every REG_LEVEL grid, and the compliance verdict is asserted on in ACK mode since 2026-08-07 (COMMON-019). It was NOT checked before that: 1958 of ~1966 ACKs discarded their compliance check |
| ARR-06 | Pending client tracking | r_pending_client management | NO | r_pending_client uncovered |
| ARR-07 | Other requests filter | w_other_requests excluding ACK'd | NO | w_other_requests uncovered |
| ARR-08 | ~~REG_OUTPUT=0~~ | **WITHDRAWN — no such parameter.** `arbiter_round_robin` takes CLIENTS/WAIT_GNT_ACK/N only, and its grants are already registered in an `always_ff`. Nothing was ever enabled by it, so "YES" here was testing fiction | n/a | - |
| ARR-09 | ~~REG_OUTPUT=1~~ | **WITHDRAWN** — same. The phantom came from the docs and was swept from them in the qc round; it survived here | n/a | - |
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

**ARR-05/06/07 status, 2026-08-07: the premise was wrong.** `grant_ack` IS
exercised -- `WAIT_GNT_ACK=1` is half of every REG_LEVEL grid and the TB drives
ACKs through ArbiterMaster. What was missing is that nothing CHECKED the
result: the compliance model's ACK path discarded 1958 of ~1966 deferred
round-robin checks (RTLDesignSherpa-DV#50), so ACK mode reported "0 errors"
while performing 8 checks per run. Fixed upstream; the TB now asserts on the
verdict in ACK mode. The uncovered-line list below predates that and should be
re-derived from the fresh coverage run.

Original text, kept for history:

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

<!-- ============================================================ -->

## External test audit (Kimi rounds 3-4, 2026-08-06/07)

The area's first external review of its test collateral, plus a scoped
re-round over what the fixes touched. 42 findings across both rounds; every
one triaged, none dropped on a verdict alone. All items below are FIXED unless
marked otherwise.

**What the rounds say about this plan's own claims.** A test plan records what
is *intended* to be covered. The audit measured what is actually *checked*, and
the gap was the story: mechanisms that existed but drove nothing, and
assertions that could not fail. A "Tested: YES" row is only as good as the
assertion behind it.

### arbiter_round_robin

- `r3` Walking-requests phase is stimulus-only in ACK mode (WAIT_GNT_ACK=1)
- `r3` Framework compliance verdict not asserted in ACK mode
- `r4` Round-robin ordering compliance can never fail the test when WAIT_GNT_ACK=1
- `r4` Walking-requests per-client grant coverage is warn-only in ACK mode

### arbiter_round_robin_weighted

- `r3` Weighted TB never reads the framework compliance verdict it configures
- `r3` test_ack_mode_edge_cases' only assertion reads cumulative counters and cannot fail
- `r3` test_weighted_fairness passes the suite with a fully failed weight scenario
- `r3` test_threshold_operation asserts on cumulative grant count, not on the weight changes it names
- `r3` TEST_LEVEL depth is wired to exactly one call site per TB — weighted FULL ≈ GATE for all checking phases
- `r4` WRR TB: ACK-mode fairness grant target is unreachable — counter is bounded by the monitor's 1000-entry transaction deque
- `r4` WRR scenario ARB-07 (test_walking_requests) cannot fail — no assertion on grant arrival
