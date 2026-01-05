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

# arbiter_round_robin_simple

A generic rotating-priority arbiter with masking/rotation that provides fair arbitration among multiple requesting agents without using if/case ladders in the priority path.

## Overview

The `arbiter_round_robin_simple` module implements a round-robin arbitration scheme that ensures fair access to a shared resource among N requesting agents. It maintains fairness by remembering the last granted agent and starting the next arbitration from the next agent in sequence.

## Module Declaration

```systemverilog
module arbiter_round_robin_simple #(
    parameter int unsigned N = 4
) (
    input  logic                  clk,
    input  logic                  rst_n,         // active-low reset
    input  logic [N-1:0]          request,       // request bits [N-1:0]
    output logic                  grant_valid,   // any grant
    output logic [N-1:0]          grant,         // one-hot grant
    output logic [$clog2(N)-1:0]  grant_id       // encoded grant (undef if grant_valid==0)
);
```

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| N | int unsigned | 4 | Number of requesting agents (N >= 1) |

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

## Functionality

### Round-Robin Algorithm

The arbiter implements a rotating priority scheme using the following approach:

1. **State Memory**: Maintains `r_last_grant` register storing the last granted agent ID
2. **Rotation**: Rotates the request vector to prioritize agents after the last granted one
3. **Priority Selection**: Uses lowest-set-bit isolation (`x & (~x + 1)`) for efficient priority selection
4. **Restoration**: Rotates the result back to original bit positions

### Key Features

- **Fair Arbitration**: Ensures all requesting agents get equal opportunity over time
- **Efficient Logic**: Uses bit manipulation instead of complex if/case structures
- **Single-Cycle Response**: Combinational grant generation with registered state update
- **Scalable**: Parameterizable for any number of agents (N >= 1)

## Implementation Details

### Rotation Logic

```systemverilog
// Shift amount = last_grant + 1 (mod N)
logic [$clog2(N)-1:0] w_shift_amount;
assign w_shift_amount = (r_last_grant == ($clog2(N))'(N-1)) ? '0 : (r_last_grant + 1);

// Rotate-left request by w_shift_amount
if (w_shift_amount == '0) begin
    w_rot_req = request;
end else begin
    w_rot_req = (request << w_shift_amount) | (request >> (($clog2(N))'(N) - w_shift_amount));
end
```

### Priority Selection

The module uses lowest-set-bit isolation for efficient one-hot selection:

```systemverilog
// Isolate lowest set bit (one-hot)
w_rot_sel = w_rot_req & ((~w_rot_req) + {{(N-1){1'b0}}, 1'b1});
```

### Grant Encoding

A compact one-hot to binary encoder generates the grant ID:

```systemverilog
always_comb begin
    w_grant_id = r_last_grant; // default to last grant
    for (int i = 0; i < N; i++) begin
        if (w_nxt_grant[i]) w_grant_id = i[$clog2(N)-1:0];
    end
end
```

## Timing Characteristics

| Characteristic | Value |
|----------------|-------|
| Setup Time | 1 clock cycle for state update |
| Response Time | Combinational (0 cycles) |
| Reset Recovery | 1 clock cycle |

## Reset Behavior

- **Power-on Reset**: `r_last_grant` initialized to N-1, causing first arbitration to start from agent 0
- **Active Reset**: All state registers cleared, grant outputs become invalid
- **Reset Release**: Next arbitration cycle begins with agent 0 having highest priority

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

## Arbitration Sequence Example

For N=4 with requests [3:0]:

| Cycle | Last Grant | Requests | Rotated | Selected | Grant | Grant ID |
|-------|------------|----------|---------|----------|--------|----------|
| 0 | 3 (init) | 1111 | 1111 | 0001 | 0001 | 0 |
| 1 | 0 | 1110 | 1101 | 0001 | 0010 | 1 |
| 2 | 1 | 1101 | 0111 | 0001 | 0100 | 2 |
| 3 | 2 | 1011 | 1101 | 0001 | 1000 | 3 |
| 4 | 3 | 1111 | 1111 | 0001 | 0001 | 0 |

## Design Considerations

### Advantages

- **Simple Logic**: Uses efficient bit manipulation instead of complex priority encoders
- **Scalable**: Works for any number of agents with minimal logic overhead
- **Fair**: Guarantees round-robin fairness over time
- **Fast**: Single combinational path from request to grant

### Limitations

- **Grant Undefined**: `grant_id` is undefined when `grant_valid` is low
- **Request Requirement**: At least one request must be active for meaningful arbitration
- **Power Consumption**: Rotational logic may consume more power than simpler priority schemes

## Synthesis Considerations

- **Area**: Scales approximately as O(N log N) due to rotation logic
- **Timing**: Critical path through rotation and bit isolation logic
- **Power**: Barrel shifter logic may have higher switching activity
- **Optimization**: Consider using dedicated arbiter primitives for large N

## Verification Notes

- **Reset Testing**: Verify proper initialization and first-grant behavior
- **Fairness Testing**: Confirm round-robin sequence over multiple cycles
- **Edge Cases**: Test behavior with single request, all requests, and no requests
- **Timing**: Verify setup/hold requirements for state register updates

## Related Modules

- `arbiter_round_robin`: Enhanced round-robin arbiter with additional features
- `arbiter_priority_encoder`: Fixed priority arbiter implementation
- `encoder_priority_enable`: Priority encoding utility module

The `arbiter_round_robin_simple` module provides an efficient and fair arbitration solution suitable for most round-robin arbitration needs in digital systems.

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
