# Priority Encoder Arbiter

A high-speed combinational priority encoder optimized for arbitration applications, implementing fixed-priority arbitration where lower-indexed clients always have higher priority.

## Overview

The `arbiter_priority_encoder` module provides single-cycle priority encoding with optimized implementations for common client counts (4, 8, 16, 32) using fully unrolled casez logic. For other client counts, it uses a synthesizable loop-based approach. The module supports dual request inputs (masked and unmasked) for use in sophisticated arbitration schemes.

## Module Declaration

```systemverilog
module arbiter_priority_encoder #(
    parameter int CLIENTS = 4,          // Number of requesting clients
    parameter int N = $clog2(CLIENTS)   // Winner ID width (derived)
) (
    input  logic [CLIENTS-1:0]  requests_masked,      // Masked request vector
    input  logic [CLIENTS-1:0]  requests_unmasked,    // Unmasked request vector
    input  logic                any_masked_requests,  // Select masked vs unmasked
    output logic [N-1:0]        winner,               // Binary-encoded winner ID
    output logic                winner_valid          // Winner output is valid
);
```

## Parameters

### User-Settable Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| CLIENTS | int | 4 | Number of requesting clients (range: 2-1024) |

### Derived Localparam (Computed Internally)

| Localparam | Computation | Description |
|------------|-------------|-------------|
| N | $clog2(CLIENTS) | Winner ID width in bits |

**Note:** N is computed automatically and cannot be overridden by users.

## Ports

### Inputs

| Port | Width | Description |
|------|-------|-------------|
| requests_masked | CLIENTS | Masked request vector (higher priority source) |
| requests_unmasked | CLIENTS | Unmasked request vector (fallback source) |
| any_masked_requests | 1 | Select masked (1) or unmasked (0) requests |

### Outputs

| Port | Width | Description |
|------|-------|-------------|
| winner | N | Binary-encoded winner client ID |
| winner_valid | 1 | Asserted when at least one request is active |

## Functionality

### Priority Order

The module implements **fixed priority** arbitration:
- **Client 0**: Highest priority (always wins if requesting)
- **Client 1**: Second highest priority
- **...**
- **Client CLIENTS-1**: Lowest priority

### Request Selection

The module evaluates requests in priority order:

1. **If `any_masked_requests = 1`**: Use `requests_masked` input
2. **If `any_masked_requests = 0`**: Use `requests_unmasked` input
3. **Find lowest-indexed asserted bit** in selected request vector
4. **If no requests**: `winner = 0` (don't care), `winner_valid = 0`

### Combinational Operation

- **Zero cycles latency**: Purely combinational logic
- **No clock or reset**: Outputs update immediately with input changes
- **Single-cycle response**: Winner determined in one combinational path

## Implementation Details

### Optimized Implementations

The module uses different implementations based on client count:

**Power-of-2 Counts (4, 8, 16, 32):**
```systemverilog
// Fully unrolled casez logic for maximum performance
always_comb begin
    casez (w_priority_requests)
        4'b???1: begin winner = 2'd0; winner_valid = 1'b1; end  // Client 0
        4'b??10: begin winner = 2'd1; winner_valid = 1'b1; end  // Client 1
        4'b?100: begin winner = 2'd2; winner_valid = 1'b1; end  // Client 2
        4'b1000: begin winner = 2'd3; winner_valid = 1'b1; end  // Client 3
        default: begin winner = 2'd0; winner_valid = 1'b0; end
    endcase
end
```

**Other Client Counts:**
```systemverilog
// Generic loop-based implementation
always_comb begin
    winner = '0;
    winner_valid = 1'b0;

    // Find lowest-indexed requesting client
    for (int i = 0; i < CLIENTS; i++) begin
        if (w_priority_requests[i] && !winner_valid) begin
            winner = i[N-1:0];
            winner_valid = 1'b1;
        end
    end
end
```

### Priority Selection Logic

```systemverilog
// Internal priority request selection
logic [CLIENTS-1:0] w_priority_requests;
assign w_priority_requests = any_masked_requests ?
                              requests_masked :
                              requests_unmasked;
```

## Performance Characteristics

### Timing

| Metric | Optimized (4,8,16,32) | Generic (<64) | Generic (>64) |
|--------|----------------------|---------------|---------------|
| **Latency** | 0 cycles (combinational) | 0 cycles | 0 cycles |
| **Propagation Delay** | 1-2 LUT levels | 2-3 LUT levels | 3-4 LUT levels |
| **Max Frequency** | >500 MHz (FPGA) | >400 MHz | >300 MHz |

### Resource Utilization

| Client Count | Implementation | LUTs (Est.) | Area Complexity |
|--------------|----------------|-------------|-----------------|
| 4 | Optimized | ~8 | O(CLIENTS) |
| 8 | Optimized | ~16 | O(CLIENTS) |
| 16 | Optimized | ~32 | O(CLIENTS) |
| 32 | Optimized | ~64 | O(CLIENTS) |
| Other | Generic | ~CLIENTS×log(CLIENTS) | O(CLIENTS×log(CLIENTS)) |

## Usage Examples

### Standalone Priority Encoder

```systemverilog
// Simple fixed-priority arbiter (single request input)
arbiter_priority_encoder #(
    .CLIENTS(8)
) u_pri_enc (
    .requests_masked   (8'b0),          // Unused
    .requests_unmasked (client_reqs),    // Primary request vector
    .any_masked_requests(1'b0),         // Always use unmasked
    .winner            (winner_id),
    .winner_valid      (grant_valid)
);

// Convert winner ID to one-hot grant signal
logic [7:0] grant_one_hot;
always_comb begin
    grant_one_hot = '0;
    if (grant_valid) begin
        grant_one_hot[winner_id] = 1'b1;
    end
end
```

### Dual-Input Priority Encoder

```systemverilog
// Masked + unmasked request inputs
arbiter_priority_encoder #(
    .CLIENTS(16)
) u_pri_enc_dual (
    .requests_masked    (masked_reqs),   // Higher priority requests
    .requests_unmasked  (all_reqs),      // All requests
    .any_masked_requests(|masked_reqs),  // Select masked if any present
    .winner             (winner_id),
    .winner_valid       (grant_valid)
);
```

### Integration in Round-Robin Arbiter

```systemverilog
// Used within arbiter_round_robin.sv
// Masked requests = clients above last winner
// Unmasked requests = all clients
arbiter_priority_encoder #(
    .CLIENTS(CLIENTS)
) u_priority_encoder (
    .requests_masked    (w_requests_masked),
    .requests_unmasked  (w_requests_unmasked),
    .any_masked_requests(w_any_masked_requests),
    .winner             (w_winner),
    .winner_valid       (w_winner_valid)
);
```

### Multi-Level Priority Groups

```systemverilog
// Implement priority groups: High (C0-C3), Med (C4-C7), Low (C8-C11)
logic [3:0] high_reqs, med_reqs, low_reqs;
logic [1:0] high_winner, med_winner, low_winner;
logic high_valid, med_valid, low_valid;

// Separate encoders for each priority group
arbiter_priority_encoder #(.CLIENTS(4)) u_high_pri (
    .requests_masked(4'b0),
    .requests_unmasked(high_reqs),
    .any_masked_requests(1'b0),
    .winner(high_winner),
    .winner_valid(high_valid)
);

arbiter_priority_encoder #(.CLIENTS(4)) u_med_pri (
    .requests_masked(4'b0),
    .requests_unmasked(med_reqs),
    .any_masked_requests(1'b0),
    .winner(med_winner),
    .winner_valid(med_valid)
);

arbiter_priority_encoder #(.CLIENTS(4)) u_low_pri (
    .requests_masked(4'b0),
    .requests_unmasked(low_reqs),
    .any_masked_requests(1'b0),
    .winner(low_winner),
    .winner_valid(low_valid)
);

// Select winner from highest priority group with requests
logic [3:0] final_winner;
always_comb begin
    if (high_valid)      final_winner = {2'b00, high_winner};
    else if (med_valid)  final_winner = {2'b01, med_winner};
    else if (low_valid)  final_winner = {2'b10, low_winner};
    else                 final_winner = 4'b0;
end
```

## Design Considerations

### When to Use

✅ **Appropriate Use Cases:**
- Fixed-priority arbitration systems
- Interrupt controllers
- Bus arbitration with priority levels
- Resource allocation with service levels
- Component within round-robin or weighted arbiters

### Performance Optimization

**For High-Speed Designs:**
- Use power-of-2 client counts (4, 8, 16, 32) for optimized implementation
- Pipeline outputs if critical path is too long
- Consider hierarchical encoding for >32 clients

**For Area Optimization:**
- Non-power-of-2 counts use smaller generic implementation
- Share encoder between multiple arbitration paths
- Use smallest practical CLIENTS parameter

### Synthesis Considerations

**Timing Optimization:**
```systemverilog
// Pipeline option for high-speed designs
logic [N-1:0] r_winner;
logic r_winner_valid;

always_ff @(posedge clk) begin
    r_winner <= winner;
    r_winner_valid <= winner_valid;
end
```

**Resource Optimization:**
- Optimized implementations use casez (efficient mux tree)
- Generic implementation uses priority loop (more logic levels)
- For CLIENTS > 32, consider hierarchical structure

## Priority Arbitration Theory

### Fixed Priority vs Round-Robin

| Aspect | Fixed Priority | Round-Robin |
|--------|---------------|-------------|
| **Fairness** | No (low-indexed clients favored) | Yes (all clients equal) |
| **Latency** | Deterministic for high-priority | Variable |
| **Starvation** | Possible for low-priority | Prevented |
| **Simplicity** | Very simple (this module) | More complex |
| **Best Use** | Interrupt handling, critical tasks | Data paths, fair scheduling |

### Priority Inversion

**Issue**: High-priority client blocked by low-priority client holding resource

**Mitigation Strategies:**
1. **Priority Inheritance**: Temporarily boost blocked client's priority
2. **Resource Preemption**: Force low-priority client to release resource
3. **Priority Ceiling**: Limit maximum priority of resource holders

## Example Priority Scenarios

### Scenario 1: Single Requester (Client 2)
```
requests_unmasked = 8'b0000_0100
any_masked_requests = 0

→ winner = 3'd2
→ winner_valid = 1
```

### Scenario 2: Multiple Requesters (Clients 0, 2, 5)
```
requests_unmasked = 8'b0010_0101
any_masked_requests = 0

→ winner = 3'd0  (lowest index wins)
→ winner_valid = 1
```

### Scenario 3: Masked Priority (Clients 3, 6 masked)
```
requests_masked   = 8'b0100_1000
requests_unmasked = 8'b0110_1101
any_masked_requests = 1

→ winner = 3'd3  (from masked, index 3 < 6)
→ winner_valid = 1
```

### Scenario 4: No Requests
```
requests_unmasked = 8'b0000_0000
any_masked_requests = 0

→ winner = 3'd0 (don't care)
→ winner_valid = 0
```

## Verification Notes

From comprehensive test suite (`val/common/test_arbiter_priority_encoder.py`):

- **Coverage**: 95%
- **Key Test Scenarios**:
  - Priority order verification (all bit patterns)
  - Masked vs unmasked selection
  - No requests (winner_valid = 0)
  - All clients requesting simultaneously
  - Single client at a time
  - Power-of-2 sizes (4, 8, 16, 32)
  - Non-power-of-2 sizes (5, 12)

**Test Command**: `pytest val/common/test_arbiter_priority_encoder.py -v`

## Common Pitfalls

❌ **Anti-Pattern 1**: Assuming fairness
```systemverilog
// WRONG: Fixed priority is NOT fair
// Client 0 will always win if requesting
```

❌ **Anti-Pattern 2**: Ignoring winner_valid
```systemverilog
// WRONG: Using winner when no requests
if (winner == 2'd0) ...  // Ambiguous: valid client 0 or no requests?

// RIGHT: Check winner_valid first
if (winner_valid && winner == 2'd0) ...
```

❌ **Anti-Pattern 3**: Mixing priority schemes
```systemverilog
// WRONG: Trying to implement round-robin with priority encoder alone
// Use arbiter_round_robin.sv instead
```

## Related Modules

- **arbiter_round_robin.sv** - Uses this module internally for winner selection
- **arbiter_round_robin_simple.sv** - Alternative simplified arbiter
- **arbiter_round_robin_weighted.sv** - Weighted arbitration with QoS
- **encoder.sv** - General-purpose binary encoder
- **priority_encoder.sv** - Alternative naming (may be same module)

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
