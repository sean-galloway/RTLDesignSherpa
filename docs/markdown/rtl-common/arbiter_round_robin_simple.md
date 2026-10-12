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

# Simple Round-Robin Arbiter

A generic rotating-priority arbiter that gives you fair arbitration among multiple requesting agents using a win-mask — no if/case ladders in the priority path.

## Overview

The `arbiter_round_robin_simple` module implements round-robin arbitration with fair access to a shared resource among N requesting agents. Fairness comes from remembering the last granted agent and giving priority to the agents above it on the next arbitration. The grant is combinational and lasts one cycle; for a grant that is held until the owner acknowledges it, see [arbiter_round_robin_simple_ack](arbiter_round_robin_simple_ack.md).

```systemverilog
module arbiter_round_robin_simple #(
    parameter int unsigned N = 4,
    parameter int unsigned W = $clog2(N)
) (
    input  logic          clk,
    input  logic          rst_n,         // active-low reset
    input  logic [N-1:0]  request,       // request bits [N-1:0]
    output logic          grant_valid,   // any grant
    output logic [N-1:0]  grant,         // one-hot grant
    output logic [W-1:0]  grant_id       // encoded grant (undef if grant_valid==0)
);
```

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| N | int unsigned | 4 | Number of requesting agents (N >= 2; see note) |
| W | int unsigned | `$clog2(N)` | Width of `grant_id`. Derived from N -- leave it at the default; it is a parameter rather than a localparam only so it can be referenced in the port list. |

## Ports

### Inputs

| Port | Width | Description |
|------|-------|-------------|
| clk | 1 | Clock signal |
| rst_n | 1 | Active-low asynchronous reset |
| request | N | Request bits from N agents [N-1:0] |

### Outputs

| Port | Width | Description |
|------|-------|-------------|
| grant_valid | 1 | Indicates if any grant is active |
| grant | N | One-hot grant output [N-1:0] |
| grant_id | $clog2(N) | Binary encoded grant ID (undefined if grant_valid==0) |

## Functional Description

### Round-Robin Algorithm

The arbiter implements a rotating priority scheme with a mask rather than a rotation:

1. **State Memory**: `r_last_grant` holds the index of the last granted agent
2. **Win-Mask**: requests are ANDed with a mask that keeps only the agents strictly above the last winner
3. **Wrap**: if no masked request remains, the unmasked request vector is used instead
4. **Priority Selection**: lowest-set-bit isolation (`x & (~x + 1)`) picks the winner in one step

### Key Features

- **Fair Arbitration**: Ensures all requesting agents get equal opportunity over time
- **Efficient Logic**: Uses bit manipulation instead of complex if/case structures
- **Single-Cycle Response**: Combinational grant generation with registered state update
- **Scalable**: Parameterizable for any number of agents (N >= 2). At N=1,
  `$clog2(1) = 0` collapses the shift/ID arithmetic into zero-size casts and
  zero replications that strict front ends reject (the same degeneracy the
  [arbiter_single_client](arbiter_single_client.md) page documents for the
  base arbiter) — use `arbiter_single_client` for the one-agent case

### Reset Behavior

- **Power-on Reset**: `r_last_grant` initialized to N-1, causing first arbitration to start from agent 0
- **Active Reset**: All state registers cleared, grant outputs become invalid
- **Reset Release**: Next arbitration cycle begins with agent 0 having highest priority

### Win-Mask Logic

```systemverilog
// After agent i wins, only agents above i stay eligible (elaboration-time constants).
for (genvar i = 0; i < N; i++) begin : gen_mask_lut
    assign w_win_mask_decode[i] = ~((N'(1) << (i + 1)) - N'(1));
end

// Agents above the last winner first; if none of them is requesting, wrap to
// the full request vector.
assign w_req_masked = request & w_win_mask_decode[r_last_grant];
assign w_any_masked = |w_req_masked;
assign w_req_sel    = w_any_masked ? w_req_masked : request;
```

After agent N-1 wins, its mask is all zero, so the fallback to the unmasked vector restarts the scan from agent 0. This is the same mask-plus-fallback structure as the programmable priority encoder of Gupta & McKeown (see References), and the same decode as `arbiter_round_robin`. Unlike a rotate-based round-robin, nothing is shifted, so the request vector never has to be rotated into place and the result rotated back.

### Priority Selection

The module uses lowest-set-bit isolation for efficient one-hot selection:

```systemverilog
// Isolate lowest set bit (one-hot)
w_nxt_grant = w_req_sel & ((~w_req_sel) + {{(N-1){1'b0}}, 1'b1});
```

### Grant Encoding

A compact one-hot to binary encoder generates the grant ID:

```systemverilog
always_comb begin
    w_grant_id = r_last_grant; // default to last grant
    for (int i = 0; i < N; i++) begin
        if (w_nxt_grant[i]) w_grant_id = i[W-1:0];
    end
end
```

## Timing Characteristics
| Characteristic | Value |
|----------------|-------|
| Setup Time | 1 clock cycle for state update |
| Response Time | Combinational (0 cycles) |
| Reset Recovery | 1 clock cycle |

## Usage Examples

### Basic 4-Agent Arbiter

```systemverilog
arbiter_round_robin_simple #(
    .N(4)
) u_arbiter (
    .clk        (clk),
    .rst_n      (rst_n),
    .request    (req_bits),     // [3:0]
    .grant_valid(grant_valid),
    .grant      (grant_oh),     // [3:0] one-hot
    .grant_id   (grant_bin)     // [1:0] binary
);
```

### 8-Agent System

```systemverilog
arbiter_round_robin_simple #(
    .N(8)
) u_8way_arbiter (
    .clk        (clk),
    .rst_n      (rst_n),
    .request    (agent_requests), // [7:0]
    .grant_valid(resource_granted),
    .grant      (agent_grants),   // [7:0]
    .grant_id   (winning_agent)   // [2:0]
);
```

### Arbitration Sequence Example

For N=4 with requests [3:0]:

| Cycle | Last Grant | Requests | Win Mask | Masked | Selected | Grant | Grant ID |
|-------|------------|----------|----------|--------|----------|-------|----------|
| 0 | 3 (init) | 1111 | 0000 | 0000 | 1111 (wrap) | 0001 | 0 |
| 1 | 0 | 1110 | 1110 | 1110 | 1110 | 0010 | 1 |
| 2 | 1 | 1101 | 1100 | 1100 | 1100 | 0100 | 2 |
| 3 | 2 | 1011 | 1000 | 1000 | 1000 | 1000 | 3 |
| 4 | 3 | 1111 | 0000 | 0000 | 1111 (wrap) | 0001 | 0 |

`Win Mask` keeps the agents above the last grant. `Selected` is the masked vector, or the full request vector when the masked one is empty (marked "wrap"). `Grant` is the lowest set bit of `Selected`.

## Design Notes

### Advantages

- **Simple Logic**: A constant mask, a 2:1 mux and a lowest-set-bit isolate; no shifter
- **Scalable**: Works for any number of agents with minimal logic overhead
- **Fair**: Guarantees round-robin fairness over time
- **Fast**: Single combinational path from request to grant

### Limitations

- **Grant Undefined**: `grant_id` is undefined when `grant_valid` is low
- **Request Requirement**: At least one request must be active for meaningful arbitration
- **Single-Cycle Grant**: The grant is not held; an agent that needs the resource for several cycles should use [arbiter_round_robin_simple_ack](arbiter_round_robin_simple_ack.md)

### Synthesis Considerations

- **Area**: N mask constants selected by `r_last_grant` (an N-way mux of N-bit constants), one N-bit 2:1 mux, an N-bit increment-and-AND for the isolate, and the one-hot to index encoder
- **Timing**: Critical path is `r_last_grant` -> mask select -> AND -> any-reduce -> fallback mux -> carry chain of the isolate -> `grant`
- **No barrel shifter**: the mask approach avoids the O(N log N) rotate-and-unrotate network of a rotation-based design

## Related Modules

- `arbiter_round_robin`: Enhanced round-robin arbiter with additional features
- [arbiter_round_robin_simple_ack](arbiter_round_robin_simple_ack.md): Same datapath with a registered grant held until the owner acks
- `arbiter_priority_encoder`: Fixed priority arbiter implementation
- `encoder_priority_enable`: Priority encoding utility module

For most round-robin arbitration needs in digital systems, `arbiter_round_robin_simple` is the efficient, fair answer.

## Testing

From the test suite (`val/common/test_arbiter_round_robin_simple.py`), parameterized over N:

- **GATE**: N = 4, 8
- **FUNC / FULL**: N = 2, 3, 4, 5, 6, 8, 16
- **Key Test Scenarios**:
  - ARB-01 to ARB-02: grant signal checks and basic arbitration
  - ARB-03 to ARB-05: request-set fairness, request-set changes, single-client saturation
  - ARB-06 to ARB-08: walking requests, bursty traffic, rapid request changes
  - ARB-09: dynamic arbitration liveness

**Test Command**: `make -C val/common clean-all && make -C val/common run-arbiter_round_robin_simple-func`

## References

- Gupta, P., McKeown, N. "Designing and Implementing a Fast Crossbar Scheduler." *IEEE Micro*, 19(1), Jan.–Feb. 1999. DOI: [10.1109/40.748793](https://doi.org/10.1109/40.748793) — the programmable priority encoder built from two fixed-priority encoders, one fed thermometer-masked requests and one fed unmasked requests; the same masked/unmasked dual-encoder structure (here the mask is the win-mask above the last winner, with fallback to the unmasked requests).
- Dally, W.J., Towles, B. *Principles and Practices of Interconnection Networks*, Morgan Kaufmann, 2004, ch. 18 "Arbitration", §18.4.2 "Round-Robin Arbiter" — textbook treatment (secondary source).
- Indexed in `rtl/common/references/README.md`

## Navigation

- **[← Back to rtl-common Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
