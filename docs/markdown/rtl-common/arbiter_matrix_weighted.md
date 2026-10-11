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

Weighted fairness, matrix style. Every client gets a credit counter, and the priority matrix only rotates after the current winner has burned its full weight in grants — so a client with weight `W` can string together up to `W` consecutive wins before it heads to the back of the line.

## Overview

This module takes the matrix arbiter from Dally & Towles, *Principles and Practices of Interconnection Networks*, chapter 17 §18.5 and bolts on the weighted-arbiter semantics from §18.4.4. Priority still lives in a `CLIENTS`×`CLIENTS` bit matrix `M`:

- `M[i][j] = 1` means requester `i` currently outranks requester `j`.
- `M[i][j] = 0` means requester `i` is outranked by requester `j`.
- The diagonal is a don't-care.

As in the unweighted module, only the `CLIENTS·(CLIENTS-1)/2` upper-triangle bits are stored; the lower triangle derives combinationally. The difference: the update that drops the winner to last place waits until the winner's credit counter hits 0.

One naming note, same as the unweighted page: `N` is the bit width of `grant_id` — `$clog2(CLIENTS)`, guarded to 1 when `CLIENTS==1`. It's not the client count. The client count is always `CLIENTS`.

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

The stored state is the upper triangle of `M`, packed into `CLIENTS*(CLIENTS-1)/2` bits. Out of reset every stored bit is 1, so power-on priority is the plain total order:

```text
0 > 1 > 2 > ... > CLIENTS-1
```

Client 0 wins everything until that first grant shuffles the deck.

### Credit Counters and Weight Semantics

Each client owns a down-counter loaded from its `max_thresh` field. Eligibility is strict — weight non-zero **and** counter greater than 0:

- **Grant completion** decrements the winner's counter.
  - No-ACK mode: completion is the grant cycle itself.
  - ACK mode: completion is the cycle in which the winner's `grant_ack` bit is asserted.
- **Reload and rotation**: When a decrement drives a counter to 0, the counter is reloaded from the current `max_thresh` field and the matrix is updated for that winner.
- **Weight = 0**: The client is immediately disabled; its counter is forced to 0 and it is never eligible.
- **Dynamic weight changes**: A new weight takes effect at the next reload for that client (i.e., the next time its counter reaches 0). If the weight is increased from 0 while the counter is 0, the counter loads the new weight on the next cycle.

### Grant Logic

Same vote as the unweighted module, just over the eligible set:

```text
g[i] = eligible[i] AND (for all j != i: NOT(eligible[j] AND M[j][i]))
```

where `eligible[i] = request[i] AND block_arb==0 AND weight[i]>0 AND credit[i]>0`.

The matrix is still a tournament, so whenever at least one client is eligible, exactly one wins.

### Matrix Update

When client `k` wins **and** that grant drives its counter to 0:

- **Row `k` cleared**: `M[k][j] = 0` for all `j > k` — `k` loses to all higher-index clients.
- **Column `k` set**: `M[i][k] = 1` for all `i < k` — all lower-index clients outrank `k`.

Client `k` drops to the lowest priority, and the new order becomes:

```text
0 > 1 > ... > k-1 > k+1 > ... > CLIENTS-1 > k
```

Between rotations, the same winner keeps re-winning as long as it has credits and keeps asking. That's the entire trick — the matrix holds still through a client's burst.

### Weighted Sequence Example

Concretely: `CLIENTS = 3`, weights `[3, 1, 2]`, everybody requesting forever. The grant order repeats:

```text
0, 0, 0, 1, 2, 2
```

Three in a row for client 0, one for client 1, two for client 2. Notice the burstiness — that's what this scheme buys you. If you'd rather see shares interleave cycle by cycle, that's the round-robin weighted module's party trick, not this one.

### No-ACK Mode (`WAIT_GNT_ACK = 0`)

One-cycle grants go out every cycle an eligible winner exists, and the matrix only moves when the winner's credits run dry. Request-to-grant latency is one cycle, plus a single credit-load bubble right after reset.

### ACK Mode (`WAIT_GNT_ACK = 1`)

The grant holds until the granted client asserts its own `grant_ack` bit, and the matrix rotates only when that ACK exhausts the winner's credits — otherwise the same winner re-wins on the same-cycle handoff. The handoff works exactly like the unweighted module: next winner computed combinationally in the ACK cycle, registered on the same edge.

Foreign-ack immunity applies here too. Only the granted client's ack bit can retire the grant; everyone else's ACKs are noise.

One subtlety worth spelling out: a held grant only *completes* when it's ACK'd, and the handoff itself doesn't spend a credit. Credits track completed grants, not ACK transactions.

### Block Arbitration

`block_arb` squashes all requests to zero, so no new grants issue while it's high. A held ACK-mode grant stays held until its ACK shows up — that's deliberate. Release the block and arbitration resumes from the current matrix and credit state.

## Timing Characteristics

Registered outputs, same as the unweighted module: one cycle from request to grant, with the matrix and credit updates registered alongside.

ACK mode pulls the update into the ACK cycle, combinationally, so a continuous ACK stream produces back-to-back grants — though if an ACK doesn't exhaust the winner's credits you'll watch the same winner re-grant instead of the priority rotating. Still no idle cycles.

Same disclaimer as the unweighted page: no measured MHz or LUT numbers yet. Nothing's been run against a target device.

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

- Out of reset, client 0 is king — the first all-requesting grant goes to client 0.
- Weight 0 disables a client immediately, leftover credits or not. The deviation note below explains why that's safe here.
- Weight changes aren't instant. They take effect at the client's next reload — the next time its counter reaches 0.
- No central pointer, no mask register. Just the pairwise bits, updating locally.
- The grant is registered, so a lone requester waits exactly one cycle after raising its request.
- Same sizing advice as the unweighted module: great at small `CLIENTS`. As the port count climbs, the `O(CLIENTS²)` matrix and comparison web get expensive, and you'll feel it in area and timing.

### Deviation from `arbiter_round_robin_weighted`

So why doesn't weight-0 disable route through the multi-cycle `WEIGHT_BLOCK → DRAIN → UPDATE → STABILIZE` FSM that `arbiter_round_robin_weighted` uses? Because that FSM exists to protect the RR module's rotating pointer and request mask — mask a client mid-grant over there and you can leave stale state behind.

This datapath has no pointer and no mask. Eligibility is just `request[i] && weight[i] > 0 && credit[i] > 0`, and the matrix only rotates on a completed grant. So when a weight drops to 0 I force the credit counter to 0 and the client simply stops being eligible next cycle. Nothing stale, nothing to drain. The deviation is deliberate, and it's safe for exactly the reason the FSM exists on the other side.

## Related Modules

**Instantiated by:** (none yet)

**See also:**
- `arbiter_matrix` — unweighted matrix (distributed-state) fair arbiter
- `arbiter_round_robin` — pointer/mask-based round-robin arbiter
- `arbiter_round_robin_weighted` — weighted round-robin arbiter (credit-interleaved shares)
- `arbiter_deficit_round_robin` — deficit round-robin arbiter (cost-proportional shares)

---

## Testing

`val/common/test_arbiter_matrix_weighted.py` puts the module through its paces. It validates:

- Documented weighted grant sequences (e.g., `CLIENTS=3`, weights `[3,1,2]` → `[0,0,0,1,2,2]`)
- One-hot or zero grant, never granted to an unrequested or credit-ineligible client
- Weight = 0 disables the client
- Dynamic weight changes take effect at the next credit reload
- Immediate service for a single requester regardless of matrix state
- Reset restoring client 0 as the highest-priority requester
- `block_arb` pauses new grants
- In ACK mode: hold-until-owner-ack, foreign-ack immunity, back-to-back same-cycle handoff, and single-requester re-grant
- Parameterization across `CLIENTS = 1, 2, 4, 5, 8` in no-ACK mode, plus ACK mode at `REG_LEVEL=GATE` and `FULL`
- Dedicated single-client (`CLIENTS==1`) directed tests for both ACK and no-ACK modes

```bash
source env_python
pytest val/common/test_arbiter_matrix_weighted.py -v
```

The testbench (`bin/TBClasses/common/arbiter_matrix_weighted_tb.py`) sticks to the same `ArbiterMaster` / `ArbiterMonitor` methodology as the round-robin testbench:

- A `WeightedRoundRobinArbiterMonitor` is attached with `is_weighted=True` so it tracks `max_thresh` and runs WRR compliance checks.
- Randomized scenario phases (grant-signals, basic-arbitration, walking-requests, block-arb, bursty-traffic, rapid-request-changes, single-client-saturation) drive stimulus through the weighted `ArbiterMaster` and assert one-hot, no-unrequested-grant, and weighted behavior through the monitor.
- The weighted-distribution phase resets the DUT and uses `ArbiterMaster` manual control to hold all requests continuously (with auto-ACK in ACK mode). This produces a clean saturation stimulus so the monitor's weight-compliance window sees the expected share ratio.
- Deterministic directed supplements cover weighted sequences, zero-weight, dynamic weight changes, idle gaps, mid-credit idle, single-requester immediacy, single-client no-ACK/ACK behavior, reset-order, and ACK-mode protocol.
- `ArbiterCompliance` protocol checking is enabled and asserted at the end of the run.
- Directed tests shut the master down via `enter_directed_mode()` / `exit_directed_mode()` so the testbench pokes the DUT signals directly without interference.
- Verification passes at `REG_LEVEL=GATE`, `FUNC`, and `FULL` across `CLIENTS = 1, 2, 4, 5, 8` in no-ACK mode, plus ACK mode at `GATE` and `FULL`.

---

## References

- Dally, William J. and Towles, Brian, *Principles and Practices of Interconnection Networks*, Morgan Kaufmann, 2004, ISBN 978-0122007514, ch. 17 §18.5 (matrix arbiters). Backs the grant/update scheme and the observation that matrix arbiters are well suited to small arbiters.
- Dally & Towles, ch. 17 §18.4.4 (weighted arbiters). Backs the credit-based weighting semantics and the trade-off between controlled long-term shares and short-term burstiness.

---

## Navigation

- **[← Back to rtl-common Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
