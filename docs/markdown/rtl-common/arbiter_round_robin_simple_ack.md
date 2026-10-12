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
# Simple Round-Robin Arbiter with Grant/ACK

A rotating-priority arbiter whose grant is registered and held until the granted agent acknowledges it, with back-to-back handoff on the acknowledge cycle.

## Overview

`arbiter_round_robin_simple_ack` uses the same priority datapath as [arbiter_round_robin_simple](arbiter_round_robin_simple.md). A win-mask keeps only the agents above the last winner eligible. If none of them is requesting, the scan falls back to the unmasked request vector, and a lowest-set-bit isolate picks the winner. The difference is the handshake. The grant is a flop, it stays asserted (one-hot) until the owner returns `grant_ack`, and only then does the arbiter move on. Use it when the granted agent needs the resource for a variable number of cycles, and the agent, not the arbiter, decides when the transfer is over. It is a simplified, educational module: the clearest place in the library to see a held-grant handshake in isolation.

```systemverilog
module arbiter_round_robin_simple_ack #(
    parameter int unsigned N = 4,
    parameter int unsigned W = (N > 1) ? $clog2(N) : 1
) (
    input  logic          clk,
    input  logic          rst_n,         // active-low reset
    input  logic [N-1:0]  request,       // request bits [N-1:0]
    input  logic [N-1:0]  grant_ack,     // per-agent ack; only the granted agent's bit counts
    output logic          grant_valid,   // a grant is outstanding
    output logic [N-1:0]  grant,         // one-hot grant, held until acked
    output logic [W-1:0]  grant_id       // encoded grant (undef if grant_valid==0)
);
```

### Key Features

- **Grant held until ACK**: once issued, `grant` does not change until `grant_ack[grant_id]` is sampled high
- **Back-to-back handoff**: on the ack cycle the arbiter re-arbitrates among the other requesters, so a waiting agent is granted on the next cycle with no bubble
- **No re-grant in the ack cycle**: if only the acked agent (or nobody) is requesting, the grant clears for one cycle
- **Stray acks ignored**: `grant_ack` bits from agents that do not hold the grant have no effect
- **N=1 elaborates**: `W` is guarded so `$clog2(1) = 0` does not produce a `[-1:0]` vector

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| N | int unsigned | 4 | Number of requesting agents (N >= 1) |
| W | int unsigned | `(N > 1) ? $clog2(N) : 1` | Width of `grant_id`. Derived from N -- leave it at the default; it is a parameter rather than a localparam only so it can be referenced in the port list. |

## Ports

### Inputs

| Port | Width | Description |
|------|-------|-------------|
| clk | 1 | Clock signal |
| rst_n | 1 | Active-low asynchronous reset |
| request | N | Request bits from N agents [N-1:0] |
| grant_ack | N | Per-agent acknowledge; only the bit of the currently granted agent is used |

### Outputs

| Port | Width | Description |
|------|-------|-------------|
| grant_valid | 1 | A grant is outstanding and waiting on its ack |
| grant | N | One-hot grant, registered, held until acked [N-1:0] |
| grant_id | W | Binary index of the held grant (undefined if grant_valid==0) |

## Functional Description

### Priority Selection

The priority path is entirely combinational and is evaluated every cycle. It is only loaded into the grant flops when the arbiter is idle or on an ack:

```systemverilog
// Agents above the last winner first; wrap to the full vector if none of them requests.
assign w_req_masked = request & w_win_mask_decode[r_last_grant];
assign w_req_sel    = (|w_req_masked) ? w_req_masked : request;

// Isolate lowest set bit (one-hot).
assign w_nxt_grant  = w_req_sel & ((~w_req_sel) + {{(N-1){1'b0}}, 1'b1});
```

`w_win_mask_decode[i]` is an elaboration-time constant, `~((1 << (i+1)) - 1)`: all agents strictly above `i`. After agent N-1 wins, the mask is all zero, so the scan restarts from agent 0.

### Grant Lifecycle

The state is three registers: `r_grant` (one-hot), `r_grant_valid`, and `r_last_grant` (the index of the current or most recent winner, which also drives `grant_id`).

| State | Condition | Next cycle |
|-------|-----------|------------|
| Idle (`grant_valid=0`) | any request | load the winner; `grant_valid=1` |
| Idle | no request | stay idle |
| Granted | owner's `grant_ack` low | hold `grant` unchanged |
| Granted | owner acks, another agent requests | load the next winner (back-to-back) |
| Granted | owner acks, no other agent requests | clear; `grant_valid=0` for at least one cycle |

On the ack cycle the acked agent is the last winner, so it is masked out whenever an agent above it is requesting. When it is the highest requester, the fallback to the unmasked vector picks the lowest requester, which is below it. Either way the handoff never re-grants the agent that just acked.

### Why the Grant Clears When Only the Acked Agent Requests

The ack completes the transfer. After it, the requester may legally drop its request, so re-granting it in the ack cycle would hand it a grant it may no longer want. This is the same contract as the `WAIT_GNT_ACK` mode of [arbiter_round_robin](arbiter_round_robin.md). If the agent still has work, it is re-granted from the idle state one cycle later.

### Request Rules

- An agent must hold `request` until it sees `grant`.
- The winner is captured in the cycle before the grant registers. A request dropped in that cycle is still granted and must still be acked; an un-acked grant is held forever.

### Reset Behavior

- `r_last_grant` resets to N-1, so the first arbitration after reset starts from agent 0.
- `r_grant` and `r_grant_valid` reset to zero.

## Timing Characteristics

This module is **sequential**: one `always_ff` block clocked on `clk` with active-low asynchronous reset `rst_n`. All three outputs come straight from flops.

| Characteristic | Value |
|----------------|-------|
| Request to grant (idle) | 1 cycle |
| Ack to next grant (another agent waiting) | 1 cycle, back-to-back |
| Ack to re-grant of the same agent (nobody else waiting) | 2 cycles (one idle cycle) |
| Grant hold | until the owner's `grant_ack` |

No synthesis frequency or area figures are quoted -- none have been measured against a target device.

### Handshake Sequence Example

N=3. All three agents request through cycle 4, then only agent 0; each owner acks in the cycle shown.

| Cycle | request | grant_ack | grant_valid | grant | grant_id | Note |
|-------|---------|-----------|-------------|-------|----------|------|
| 0 | 111 | 000 | 0 | 000 | - | idle; winner agent 0 is loaded |
| 1 | 111 | 000 | 1 | 001 | 0 | agent 0 holds the grant |
| 2 | 111 | 001 | 1 | 001 | 0 | agent 0 acks; agent 1 wins the handoff |
| 3 | 111 | 010 | 1 | 010 | 1 | agent 1 acks in its first cycle |
| 4 | 111 | 100 | 1 | 100 | 2 | agent 2 acks; mask wraps to agent 0 |
| 5 | 001 | 001 | 1 | 001 | 0 | agent 0 acks; nobody else requests |
| 6 | 001 | 000 | 0 | 000 | - | grant clears for one cycle |
| 7 | 001 | 000 | 1 | 001 | 0 | agent 0 re-granted from idle |

## Usage Examples

```systemverilog
arbiter_round_robin_simple_ack #(
    .N(4)
) u_arb (
    .clk        (clk),
    .rst_n      (rst_n),
    .request    (req_bits),     // [3:0], held until granted
    .grant_ack  (ack_bits),     // [3:0], owner pulses its bit when done
    .grant_valid(grant_valid),
    .grant      (grant_oh),     // [3:0] one-hot, held until acked
    .grant_id   (grant_bin)     // [1:0]
);
```

## Design Notes

- **Choosing between the round-robin variants.** Use [arbiter_round_robin_simple](arbiter_round_robin_simple.md) when a grant lasts exactly one cycle. Use this module when the owner holds the resource for a variable time and signals completion. Use [arbiter_round_robin](arbiter_round_robin.md) with `WAIT_GNT_ACK=1` when you also need its other features.
- **The idle cycle is deliberate.** It costs one cycle only when a single agent re-requests back-to-back with nobody else waiting. Under contention the handoff has no bubble.
- **`grant_id` is undefined while idle.** It holds the last winner's index; qualify it with `grant_valid`.
- **A teaching module.** This is a deliberately simplified example: it shows the grant/ack handshake on top of the smallest round-robin datapath, without the extra modes of `arbiter_round_robin`. It is meant to be read and experimented with, which is why no production RTL in the repository instantiates it.

## Related Modules

- [arbiter_round_robin_simple](arbiter_round_robin_simple.md) - Same priority datapath, single-cycle grant, no handshake
- [arbiter_round_robin](arbiter_round_robin.md) - Full round-robin arbiter; its `WAIT_GNT_ACK` mode defines the ack contract this module follows
- [arbiter_single_client](arbiter_single_client.md) - Degenerate one-client arbiter with the same registered, ack-held grant
- [arbiter_round_robin_weighted](arbiter_round_robin_weighted.md) - Weighted / QoS round-robin variant
- [arbiter_priority_encoder](arbiter_priority_encoder.md) - Fixed-priority arbiter

Source: `rtl/common/arbiter_round_robin_simple_ack.sv` (filelist `rtl/common/filelists/arbiter_round_robin_simple_ack.f`).

## Testing

From the test suite (`val/common/test_arbiter_round_robin_simple_ack.py`), parameterized over N:

- **GATE**: N = 4, 8
- **FUNC / FULL**: N = 2, 3, 4, 5, 6, 8, 16
- **Key Test Scenarios**:
  - ARB-01 to ARB-02: grant signal checks and basic arbitration
  - ARB-03 to ARB-05: request-set fairness, request-set changes, single-client saturation
  - ARB-06 to ARB-08: walking requests, bursty traffic, rapid request changes
  - ARB-09: grant held until the owner acks
  - ARB-10: back-to-back handoff on the ack cycle
  - ARB-11: dynamic arbitration liveness

**Test Command**: `make -C val/common clean-all && make -C val/common run-arbiter_round_robin_simple_ack-func`

## References

- Gupta, P., McKeown, N. "Designing and Implementing a Fast Crossbar Scheduler." *IEEE Micro*, 19(1), Jan.–Feb. 1999. DOI: [10.1109/40.748793](https://doi.org/10.1109/40.748793) — the programmable priority encoder built from a masked and an unmasked fixed-priority encoder; the same dual-encoder structure as this module's win-mask with fallback to the unmasked requests.
- Dally, W.J., Towles, B. *Principles and Practices of Interconnection Networks*, Morgan Kaufmann, 2004, ch. 18 "Arbitration", §18.4.2 "Round-Robin Arbiter" and §18.4.3 "Grant-Hold Circuit" — textbook treatment of the rotating priority and of holding a grant until the owner releases it (secondary source).
- Indexed in `rtl/common/references/README.md`

## Navigation

- **[← Back to rtl-common Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
