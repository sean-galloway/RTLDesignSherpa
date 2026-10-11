<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

**[← Back to Main Index](../index.md)** | **[rtl-common Index](index.md)**

# Matrix Arbiter

Fair, distributed-state arbitration using a priority matrix. Each requester carries a complete picture of its rank relative to every other requester, so the arbiter never needs a rotating barrel shifter or priority-encoder chain to pick a winner.

## Overview

The `arbiter_matrix` module implements the matrix arbiter described in Dally & Towles, *Principles and Practices of Interconnection Networks*, chapter 17 §18.5. Priority is encoded as a `CLIENTS`×`CLIENTS` bit matrix `M`:

- `M[i][j] = 1` means requester `i` currently outranks requester `j`.
- `M[i][j] = 0` means requester `i` is outranked by requester `j`.
- The diagonal is a don't-care.

Because `M[j][i] = ~M[i][j]`, only the `CLIENTS·(CLIENTS-1)/2` upper-triangle bits are stored; the lower triangle is derived combinationally. On each grant, the winner's row is cleared and its column is set, dropping that winner to the lowest priority. The result is strong fairness: any persistently requesting client is served within `CLIENTS` consecutive grants.

In this document, `N` refers to the bit width of `grant_id` (`$clog2(CLIENTS)`, guarded to 1 for `CLIENTS==1`). It is not the number of clients; the number of clients is always `CLIENTS`.

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| CLIENTS | int | 4 | Number of requesting clients (must be ≥ 1) |
| WAIT_GNT_ACK | int | 0 | When 1, holds the grant until the winner acknowledges it |
| N | int | $clog2(CLIENTS) (guarded) | **Derived** bit width of `grant_id`; do not override |

## Ports

### Inputs

| Port | Width | Description |
|------|-------|-------------|
| clk | 1 | System clock |
| rst_n | 1 | Active-low asynchronous reset |
| block_arb | 1 | When asserted, masks all requests to zero and stops grants |
| request | CLIENTS | One-bit request per client |
| grant_ack | CLIENTS | Per-client grant acknowledgment (used when `WAIT_GNT_ACK = 1`) |

### Outputs

| Port | Width | Description |
|------|-------|-------------|
| grant_valid | 1 | High when a valid grant is being issued |
| grant | CLIENTS | One-hot grant vector (exactly one bit set when `grant_valid=1`) |
| grant_id | `N` (`$clog2(CLIENTS)`, guarded) | Binary-encoded ID of the granted client |
| last_grant | CLIENTS | Previous cycle's grant (for debugging/history) |

## Functional Description

### Matrix Representation

The stored state is the upper triangle of `M` packed into `CLIENTS*(CLIENTS-1)/2` bits. Reset initializes every upper-triangle entry to 1, which corresponds to the total priority order:

```text
0 > 1 > 2 > ... > CLIENTS-1
```

Requester 0 wins all ties from reset.

### Grant Logic

The grant for client `i` is computed combinationally as:

```text
g[i] = request[i] AND (for all j != i: NOT(request[j] AND M[j][i]))
```

In words: client `i` wins if and only if no other requesting client outranks it. Because the matrix is a tournament (anti-symmetric and complete), exactly one client wins whenever at least one request is present.

### Matrix Update

When client `k` wins:

- **Row `k` cleared**: `M[k][j] = 0` for all `j > k` — `k` loses to all higher-index clients.
- **Column `k` set**: `M[i][k] = 1` for all `i < k` — all lower-index clients outrank `k`.

Client `k` therefore drops to the lowest priority. The new order becomes:

```text
0 > 1 > ... > k-1 > k+1 > ... > CLIENTS-1 > k
```

### No-ACK Mode (`WAIT_GNT_ACK = 0`)

A one-cycle grant is issued every cycle a winner exists, and the matrix is updated every cycle.

### ACK Mode (`WAIT_GNT_ACK = 1`)

The grant is held until the granted client asserts the corresponding bit of `grant_ack`. The matrix is updated only when the ACK arrives, so the priority state does not advance while a transaction is in flight.

When the owner's `grant_ack` bit is asserted, the matrix is updated for the retiring winner and the next waiting requester is granted in the **same clock cycle** (same-cycle ACK handoff). This means that with all clients continuously requesting, grants advance every cycle once each ACK is provided. Only the bit of `grant_ack` belonging to the currently granted client can retire the held grant; ACK bits from other clients are ignored (foreign-ack immunity).

### Block Arbitration

Asserting `block_arb` masks all requests to zero. No grants are issued while it is high; grants resume from the current matrix state when it is released.

## Timing Characteristics

This module is **sequential**: grants are registered and appear one clock cycle after the requests that produced them. The matrix update is also registered, so in no-ACK mode the next winner is computed from the updated matrix on the following cycle.

In ACK mode, the post-ACK matrix update and next-winner computation are performed combinationally in the cycle the ACK arrives, and the new grant is registered in the same cycle. Therefore a continuous stream of ACKs produces back-to-back grants with no idle cycle between them.

No synthesis frequency or area figures are quoted; none have been measured against a target device.

---

## Usage Examples

```systemverilog
arbiter_matrix #(
    .CLIENTS     (8),
    .WAIT_GNT_ACK(0)
) u_arbiter_matrix (
    .clk         (clk),
    .rst_n       (rst_n),
    .block_arb   (1'b0),
    .request     (request_vec),
    .grant_ack   ('0),                 // Unused in No-ACK mode
    .grant_valid (grant_valid),
    .grant       (grant_vec),
    .grant_id    (winner_id),
    .last_grant  (last_grant_vec)
);
```

---

## Design Notes

### Usage Notes

- From reset, client 0 has the highest priority; the first grant with all clients requesting goes to client 0.
- The matrix update is local and distributed: there is no central rotating pointer or mask register, only the pairwise priority bits.
- Because the grant is registered, a lone requester sees a grant in the cycle after its request is asserted.
- The matrix arbiter is especially attractive for small `CLIENTS`; for very large `CLIENTS` the `O(CLIENTS²)` matrix storage and the cross-client comparison network can dominate area and timing.

## Related Modules

**Instantiated by:** (none yet)

**See also:**
- `arbiter_round_robin` — pointer/mask-based round-robin arbiter
- `arbiter_round_robin_simple` — minimal rotating-priority arbiter
- `arbiter_priority_encoder` — fixed-priority encoder used by the round-robin variants

---

## Testing

`val/common/test_arbiter_matrix.py` exercises the module. It validates:

- One-hot or zero grant, never granted to an unrequested client
- Strong fairness over `4·CLIENTS` consecutive grants with all clients requesting
- Correct rotation from cold start and after partial-request idle gaps
- Immediate service for a single requester regardless of matrix state
- Reset restoring client 0 as the highest-priority requester
- In ACK mode: hold-until-owner-ack, foreign-ack immunity, back-to-back same-cycle handoff, and single-requester re-grant
- Parameterization across `CLIENTS = 2, 4, 5, 8` in no-ACK mode, plus ACK mode at `REG_LEVEL=GATE` and `FULL`

```bash
source env_python
pytest val/common/test_arbiter_matrix.py -v
```

---

## Navigation

- **[← Back to rtl-common Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**

---

## Testbench Methodology Alignment Report

`bin/TBClasses/common/arbiter_matrix_tb.py` was reworked to follow the same `ArbiterMaster` / `ArbiterMonitor` methodology used by the round-robin arbiter testbench:

- A `RoundRobinArbiterMonitor` is attached because the observable rotation of the matrix arbiter is equivalent to round-robin.
- Randomized scenario phases (grant-signals, basic-arbitration, walking-requests, block-arb, bursty-traffic, rapid-request-changes, single-client-saturation, fairness) drive stimulus through `ArbiterMaster` and assert one-hot, no-unrequested-grant, and rotation behavior through the monitor.
- Deterministic directed supplements are retained for corner cases the randomized master/monitor cannot express cleanly: one-hot/request-match, strong-fairness-continuous, fairness-cold-start-and-gaps, single-requester-immediate, and reset-order.  ACK-mode equivalents are exercised separately (hold-until-owner-ack, foreign-ack immunity, back-to-back handoff, single-requester).
- `ArbiterCompliance` protocol checking is enabled and asserted at the end of the run.
- Directed tests shut the master down via `enter_directed_mode()` / `exit_directed_mode()` so the testbench pokes the DUT signals directly without interference.
- Verification passes at `REG_LEVEL=GATE`, `FUNC`, and `FULL` across `CLIENTS = 2, 4, 5, 8` (no-ACK), plus ACK mode at `GATE` and `FULL`.

## References

- Dally, William J. and Towles, Brian, *Principles and Practices of Interconnection Networks*, Morgan Kaufmann, 2004, ISBN 978-0122007514, ch. 17 §18.5 (matrix arbiters). Backs the grant/update scheme and the observation that matrix arbiters are well suited to small arbiters.
