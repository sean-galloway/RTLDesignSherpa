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

# Deficit Round Robin Arbiter

**Module:** `rtl/common/arbiter_deficit_round_robin.sv`

## Overview

Deficit round-robin (DRR) arbiter — the sibling wrapper to
[arbiter_round_robin_weighted](arbiter_round_robin_weighted.md) around the
same [arbiter_round_robin](arbiter_round_robin.md) core. The two disciplines
answer different questions:

- **WRR:** shares proportional to **grant count**. Weight 4 means four
  grants per replenish round, whatever each grant costs.
- **DRR:** shares proportional to **cost served**. Quantum 4 means four
  cost-units (bytes, beats, bus cycles) per round, however many grants that
  takes.

With equal-cost requests the two give identical long-run shares — use the
cheaper WRR there. Reach for the DRR when a grant's resource usage varies
per request: packet lengths, burst sizes, variable-beat DMA descriptors.

```systemverilog
module arbiter_deficit_round_robin #(
    parameter int CLIENTS      = 4,
    parameter int MAX_QUANTUM  = 16,
    parameter int COST_WIDTH   = 4,
    parameter int WAIT_GNT_ACK = 0
) (
    input  logic              clk,
    input  logic              rst_n,
    input  logic              block_arb,
    input  logic [CXQW-1:0]   quantum,
    input  logic [CXCW-1:0]   req_cost,
    input  logic [C-1:0]      request,
    input  logic [C-1:0]      grant_ack,
    output logic              grant_valid,
    output logic [C-1:0]      grant,
    output logic [N-1:0]      grant_id
);
```

## Parameters

### User-Settable Parameters

| Parameter | Type | Default | Description |
|---|---|---|---|
| CLIENTS | int | 4 | Number of requesting clients (range: 2-32) |
| MAX_QUANTUM | int | 16 | Exclusive bound on per-client quantum; field width = $clog2(MAX_QUANTUM) (range: 2-256) |
| COST_WIDTH | int | 4 | Width of each client's request-cost input (costs 1..2^COST_WIDTH-1; range: 1-16) |
| WAIT_GNT_ACK | int | 0 | 0 = grant completes immediately, 1 = grant held until grant_ack |

### Derived Parameters

Declared in the parameter list so the port declarations can use them (strict
front ends reject body localparams in port ranges); overridable in principle,
and must not be — leave them to their derivations. Only DW is a true
localparam.

| Parameter | Default | Description |
|---|---|---|
| QW | $clog2(MAX_QUANTUM) | Quantum field width |
| DW | $clog2(2^COST_WIDTH + MAX_QUANTUM) + 1 | Deficit counter width — sized so every legal cost is reachable by accumulation, which is the no-livelock guarantee |
| N | $clog2(CLIENTS) | grant_id width |
| CXQW / CXCW | CLIENTS x QW / CLIENTS x COST_WIDTH | Packed array widths |

## Ports

### Inputs

| Port | Width | Description |
|---|---|---|
| clk | 1 | Clock |
| rst_n | 1 | Async active-low reset |
| block_arb | 1 | Block all arbitration while high |
| quantum | CXQW | Packed per-client quanta, client 0 in the low field. Zero disables a client. Changes go through the atomic-update FSM |
| req_cost | CXCW | Packed cost of each client's HEAD request. Stable while request held; the next frame's cost may be presented as soon as the current frame's grant is observed |
| request | CLIENTS | Request vector |
| grant_ack | CLIENTS | Grant acknowledgment (ACK mode only) |

### Outputs

| Port | Width | Description |
|---|---|---|
| grant_valid | 1 | Grant output valid |
| grant | CLIENTS | One-hot grant vector |
| grant_id | N | Binary-encoded winner |

## Functional Description

### The Deficit Discipline

Each client holds a deficit counter (reset 0). A requester is **eligible**
when its deficit covers its head cost. When requests exist but nobody can
afford service, a **replenish round** adds each requesting client's quantum
to its deficit — repeating on consecutive cycles until someone becomes
eligible, which is how a cost larger than one quantum is saved up for
(multi-round accumulation; the deficit width guarantees termination). On
grant completion the winner is debited the served cost and the **remainder
carries** to its next request — the carry is what keeps long-run shares on
the quantum ratio regardless of how costs divide into it.

**Anti-hoarding:** a client's deficit clears when its request deasserts
(classic DRR empty-queue rule). Service share is earned while competing —
an idle client cannot bank deficit and burst later. Hold request through
frame gaps if the carry should survive.

### The Cost Pipeline

The grant registers one cycle after the arbitration that won it. A consumer
naturally pops its frame on grant and presents the next frame's cost
immediately — so in the completion cycle `req_cost` may already belong to
the *next* frame. The arbiter therefore debits the **arbitration-cycle**
cost, captured in an internal one-deep pipeline. Without it, a back-to-back
client is debited the wrong frame's cost (this was caught during bring-up
by the testbench's deficit mirror, not by inspection — see the test).

### Share Example

Quanta [4,2,1,1], every request cost 2:

- Replenish gives deficits [4,2,1,1]: clients 0 and 1 afford immediately,
  clients 2 and 3 must accumulate a second round to reach 2.
- Long-run cost-units served settle at 4:2:1:1 — the quantum ratio — even
  though clients 2 and 3 are only served every other round.

### Quantum Changes and Disable

Runtime quantum changes pass through the same shadow-register FSM as the
WRR's weights (IDLE → BLOCK → DRAIN → UPDATE → STABILIZE; 10 cycles minimum,
~25 with the BLOCK timeout); deficits clear at STABILIZE so old carry cannot distort the new
policy. Quantum 0 disables a client entirely. A cost of 0 is defensively
served as cost 1.

## Timing Characteristics
| Property | Value |
|---|---|
| Latency | 1 cycle steady-state (deficit compare, masking and RR decision combinational; grant registered in the core) |
| Throughput | 1 grant/cycle max |
| Replenish | 1 cycle per round, repeats until affordable |
| Quantum update | 10-25 cycles (FSM; DRAIN occupies 3 cycles, STABILIZE 4) |

Critical path: the deficit >= cost comparator into the request mask into
the base arbiter — one comparator wider than the WRR's credit-nonzero
check. At high client counts consider registering eligibility (costs a
cycle of latency).

## Related Modules

- [arbiter_round_robin](arbiter_round_robin.md) — the shared base core
- [arbiter_round_robin_weighted](arbiter_round_robin_weighted.md) — the
  grant-count sibling; use it when requests are equal-sized
- [arbiter_round_robin_simple](arbiter_round_robin_simple.md),
  [arbiter_priority_encoder](arbiter_priority_encoder.md)

## Testing

**Location:** `val/common/test_arbiter_deficit_round_robin.py`

The property under test is cost-proportionality: served cost-units per
client must follow the quantum ratio whatever the per-request costs are.
Scenarios: equal-cost anchor, mixed random costs (the DRR-defining case),
cost > quantum accumulation, anti-hoarding, zero-quantum disable, dynamic
quantum change; both ACK modes, 4-16 clients. Every scenario also runs a
cycle mirror of the deficit discipline that fails the test on any grant to
a client whose deficit did not cover its arbitration-cycle cost.

```bash
pytest val/common/test_arbiter_deficit_round_robin.py -v
```

## Navigation

- **[Index](index.md)** · **[Overview](overview.md)**
