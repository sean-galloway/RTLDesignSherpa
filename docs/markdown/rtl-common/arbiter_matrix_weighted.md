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

# Weighted Matrix Arbiter

Fair, distributed-state arbitration with per-client credit counters. The matrix arbiter's strong-fairness priority state is rotated only after the current winner has consumed its full weight in grants, so a client with weight `W` can receive up to `W` consecutive grants before dropping to lowest priority.

## Overview

The `arbiter_matrix_weighted` module extends the matrix arbiter described in Dally & Towles, *Principles and Practices of Interconnection Networks*, chapter 17 §18.5, with the weighted-arbiter semantics discussed in §18.4.4. Priority is encoded as a `CLIENTS`×`CLIENTS` bit matrix `M`:

- `M[i][j] = 1` means requester `i` currently outranks requester `j`.
- `M[i][j] = 0` means requester `i` is outranked by requester `j`.
- The diagonal is a don't-care.

Only the `CLIENTS·(CLIENTS-1)/2` upper-triangle bits are stored; the lower triangle is derived combinationally. Unlike the unweighted matrix arbiter, the update that drops the winner to lowest priority is deferred until the winner's credit counter reaches 0.

In this document, `N` refers to the bit width of `grant_id` (`$clog2(CLIENTS)`, guarded to 1 for `CLIENTS==1`). It is not the number of clients; the number of clients is always `CLIENTS`.

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| MAX_LEVELS | int | 16 | Maximum weight value per client (must be ≥ 1) |
| CLIENTS | int | 4 | Number of requesting clients (must be ≥ 1) |
| WAIT_GNT_ACK | int | 0 | When 1, holds the grant until the winner acknowledges it |
| MAX_LEVELS_WIDTH | int | `$clog2(MAX_LEVELS)` | **Derived** credit counter width |
| N | int | `$clog2(CLIENTS)` (guarded) | **Derived** bit width of `grant_id`; do not override |

## Ports

### Inputs

| Port | Width | Description |
|------|-------|-------------|
| clk | 1 | System clock |
| rst_n | 1 | Active-low asynchronous reset |
| block_arb | 1 | When asserted, masks all requests to zero and stops new grants |
| max_thresh | `CLIENTS * MAX_LEVELS_WIDTH` | Packed per-client weights `{weight[N-1], ..., weight[0]}` |
| request | CLIENTS | One-bit request per client |
| grant_ack | CLIENTS | Per-client grant acknowledgment (used when `WAIT_GNT_ACK = 1`) |

### Outputs

| Port | Width | Description |
|------|-------|-------------|
| grant_valid | 1 | High when a valid grant is being issued |
| grant | CLIENTS | One-hot grant vector (exactly one bit set when `grant_valid=1`) |
| grant_id | `N` | Binary-encoded ID of the granted client |
| last_grant | CLIENTS | Previous cycle's grant (for debugging/history) |

## Functional Description

### Matrix Representation

The stored state is the upper triangle of `M` packed into `CLIENTS*(CLIENTS-1)/2` bits. Reset initializes every upper-triangle entry to 1, which corresponds to the total priority order:

```text
0 > 1 > 2 > ... > CLIENTS-1
```

Requester 0 wins all ties from reset.

### Credit Counters and Weight Semantics

Each client has a down-counter loaded from its `max_thresh` field. A client is eligible for arbitration only when its weight is non-zero **and** its credit counter is greater than 0.

- **Grant completion** decrements the winner's counter.
  - No-ACK mode: completion is the grant cycle itself.
  - ACK mode: completion is the cycle in which the winner's `grant_ack` bit is asserted.
- **Reload and rotation**: When a decrement drives a counter to 0, the counter is reloaded from the current `max_thresh` field and the matrix is updated for that winner.
- **Weight = 0**: The client is immediately disabled; its counter is forced to 0 and it is never eligible.
- **Dynamic weight changes**: A new weight takes effect at the next reload for that client (i.e., the next time its counter reaches 0). If the weight is increased from 0 while the counter is 0, the counter loads the new weight on the next cycle.

### Grant Logic

The grant for client `i` is computed combinationally as:

```text
g[i] = eligible[i] AND (for all j != i: NOT(eligible[j] AND M[j][i]))
```

where `eligible[i] = request[i] AND block_arb==0 AND weight[i]>0 AND credit[i]>0`.

Because the matrix is a tournament, exactly one client wins whenever at least one client is eligible.

### Matrix Update

When client `k` wins **and** its credit counter reaches 0 on that grant:

- **Row `k` cleared**: `M[k][j] = 0` for all `j > k` — `k` loses to all higher-index clients.
- **Column `k` set**: `M[i][k] = 1` for all `i < k` — all lower-index clients outrank `k`.

Client `k` therefore drops to the lowest priority. The new order becomes:

```text
0 > 1 > ... > k-1 > k+1 > ... > CLIENTS-1 > k
```

Between rotation events, the same winner keeps re-winning as long as it still has credits and keeps requesting.

### Weighted Sequence Example

With `CLIENTS = 3` and weights `[3, 1, 2]` and all clients continuously requesting, the grant order repeats:

```text
0, 0, 0, 1, 2, 2
```

Client 0 receives three consecutive grants, client 1 one grant, and client 2 two grants, per full weighted turn.

### No-ACK Mode (`WAIT_GNT_ACK = 0`)

A one-cycle grant is issued every cycle an eligible winner exists. The matrix is updated only when the winner's credits are exhausted. Latency from a request change to the registered grant is one cycle, plus a one-cycle credit-load bubble immediately after reset.

### ACK Mode (`WAIT_GNT_ACK = 1`)

The grant is held until the granted client asserts the corresponding bit of `grant_ack`. The matrix is updated only when the ACK exhausts the winner's credits; otherwise the same winner re-wins on the same-cycle handoff.

When the owner's `grant_ack` bit is asserted, the next waiting requester is granted in the **same clock cycle** (same-cycle ACK handoff). Only the bit of `grant_ack` belonging to the currently granted client can retire the held grant; ACK bits from other clients are ignored (foreign-ack immunity).

A held grant is a completed grant only when ACK'd; an ACK handoff itself does **not** consume a credit — credits count grants, not ACKs.

### Block Arbitration

Asserting `block_arb` masks all requests to zero. No new grants are issued while it is high; a held grant in ACK mode remains held until it is acknowledged. Grants resume from the current matrix and credit state when `block_arb` is released.

## Timing Characteristics

This module is **sequential**: grants are registered and appear one clock cycle after the requests that produced them. The matrix update and credit reload are also registered.

In ACK mode, the post-ACK matrix update and next-winner computation are performed combinationally in the cycle the ACK arrives, and the new grant is registered in the same cycle. Therefore a continuous stream of ACKs produces back-to-back grants with no idle cycle between them (provided each ACK exhausts the previous winner's credits; otherwise the same winner is re-granted).

No synthesis frequency or area figures are quoted; none have been measured against a target device.

---

## Usage Examples

```systemverilog
localparam int NUM_CLIENTS = 4;
localparam int MAX_WEIGHT  = 16;
localparam int WEIGHT_W    = $clog2(MAX_WEIGHT);

logic [NUM_CLIENTS-1:0] req, gnt;
logic [WEIGHT_W-1:0] weights [NUM_CLIENTS];
logic [NUM_CLIENTS*WEIGHT_W-1:0] packed_weights;

// Pack weights: client 0 occupies the least-significant field.
assign packed_weights = {weights[3], weights[2], weights[1], weights[0]};

arbiter_matrix_weighted #(
    .CLIENTS     (NUM_CLIENTS),
    .MAX_LEVELS  (MAX_WEIGHT),
    .WAIT_GNT_ACK(0)
) u_weighted_arbiter (
    .clk         (clk),
    .rst_n       (rst_n),
    .block_arb   (1'b0),
    .max_thresh  (packed_weights),
    .request     (req),
    .grant_ack   ('0),
    .grant_valid (grant_valid),
    .grant       (gnt),
    .grant_id    (winner_id),
    .last_grant  (last_grant_vec)
);
```

---

## Design Notes

### Usage Notes

- From reset, client 0 has the highest priority; the first grant with all clients requesting goes to client 0.
- A weight of 0 disables a client immediately, even if it had leftover credits.
- Weight changes are not instantaneous: they take effect when the affected client's counter next reaches 0 and reloads.
- The matrix update is local and distributed; there is no central rotating pointer.
- Because the grant is registered, a lone requester sees a grant in the cycle after its request is asserted.
- The weighted matrix arbiter is especially attractive for small `CLIENTS`; for very large `CLIENTS` the `O(CLIENTS²)` matrix storage and the cross-client comparison network can dominate area and timing.

## Related Modules

**Instantiated by:** (none yet)

**See also:**
- `arbiter_matrix` — unweighted matrix (distributed-state) fair arbiter
- `arbiter_round_robin` — pointer/mask-based round-robin arbiter
- `arbiter_round_robin_weighted` — weighted round-robin arbiter (credit-interleaved shares)
- `arbiter_deficit_round_robin` — deficit round-robin arbiter (cost-proportional shares)

---

## Testing

`val/common/test_arbiter_matrix_weighted.py` exercises the module. It validates:

- Documented weighted grant sequences (e.g., `CLIENTS=3`, weights `[3,1,2]` → `[0,0,0,1,2,2]`)
- One-hot or zero grant, never granted to an unrequested or credit-ineligible client
- Weight = 0 disables the client
- Dynamic weight changes take effect at the next credit reload
- Immediate service for a single requester regardless of matrix state
- Reset restores client 0 as the highest-priority requester
- `block_arb` pauses new grants
- In ACK mode: hold-until-owner-ack, foreign-ack immunity, back-to-back same-cycle handoff, and single-requester re-grant
- Parameterization across `CLIENTS = 2, 4, 5, 8` in no-ACK mode, plus ACK mode at `REG_LEVEL=GATE` and `FULL`

```bash
source env_python
pytest val/common/test_arbiter_matrix_weighted.py -v
```

---

## Navigation

- **[← Back to rtl-common Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**

---

## References

- Dally, William J. and Towles, Brian, *Principles and Practices of Interconnection Networks*, Morgan Kaufmann, 2004, ISBN 978-0122007514, ch. 17 §18.5 (matrix arbiters). Backs the grant/update scheme and the observation that matrix arbiters are well suited to small arbiters.
- Dally & Towles, ch. 17 §18.4.4 (weighted arbiters). Backs the credit-based weighting semantics and the trade-off between controlled long-term shares and short-term burstiness.
