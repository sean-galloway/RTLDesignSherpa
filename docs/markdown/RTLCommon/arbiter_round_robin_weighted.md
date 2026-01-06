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

# Weighted Round Robin Arbiter

A credit-based weighted round-robin arbiter with Quality of Service (QoS) support, providing proportional bandwidth allocation to multiple clients while maintaining starvation-free operation.

## Overview

The `arbiter_round_robin_weighted` module combines fair round-robin arbitration with configurable per-client weights to provide proportional bandwidth allocation. Each client receives grants proportional to its assigned weight while preventing starvation. The module supports optional acknowledgment protocol and dynamic weight changes with atomic update semantics.

## Module Declaration

```systemverilog
module arbiter_round_robin_weighted #(
    parameter int MAX_LEVELS = 16,      // Maximum weight value per client
    parameter int CLIENTS = 4,          // Number of requesting clients
    parameter int WAIT_GNT_ACK = 0      // Enable ACK protocol (0=No-ACK, 1=ACK)
) (
    // Derived localparam (computed internally - not user-settable):
    // localparam int MAX_LEVELS_WIDTH = $clog2(MAX_LEVELS);  // Credit counter width
    // localparam int N = $clog2(CLIENTS);                     // Client ID width
    // localparam int C = CLIENTS;                             // Convenience alias
    // localparam int MTW = MAX_LEVELS_WIDTH;                  // Weight width alias
    // localparam int CXMTW = CLIENTS * MAX_LEVELS_WIDTH;      // Packed weight array width

    input  logic              clk,              // Clock input
    input  logic              rst_n,            // Active-low asynchronous reset
    input  logic              block_arb,        // Block all arbitration
    input  logic [CXMTW-1:0]  max_thresh,       // Packed weight values for all clients
    input  logic [C-1:0]      request,          // Request signals from clients
    input  logic [C-1:0]      grant_ack,        // Grant acknowledgment (ACK mode only)
    output logic              grant_valid,      // Grant output valid
    output logic [C-1:0]      grant,            // Grant vector (one-hot)
    output logic [N-1:0]      grant_id          // Grant client ID (binary encoded)
);
```

## Parameters

### User-Settable Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| MAX_LEVELS | int | 16 | Maximum weight value per client (range: 1-256) |
| CLIENTS | int | 4 | Number of requesting clients (range: 2-32) |
| WAIT_GNT_ACK | int | 0 | Enable ACK protocol (0=No-ACK, 1=ACK required) |

### Derived Localparam (Computed Internally)

| Localparam | Computation | Description |
|------------|-------------|-------------|
| MAX_LEVELS_WIDTH | $clog2(MAX_LEVELS) | Credit counter width in bits |
| N | $clog2(CLIENTS) | Client ID width in bits |
| C | CLIENTS | Convenience alias for port widths |
| MTW | MAX_LEVELS_WIDTH | Convenience alias for weight width |
| CXMTW | CLIENTS * MAX_LEVELS_WIDTH | Total packed weight array width |

**Note:** MAX_LEVELS_WIDTH, N, C, MTW, and CXMTW are computed internally and cannot be overridden by users.

## Ports

### Inputs

| Port | Width | Description |
|------|-------|-------------|
| clk | 1 | System clock |
| rst_n | 1 | Active-low asynchronous reset |
| block_arb | 1 | Block all arbitration (external gate) |
| max_thresh | CXMTW | Packed weight values: {weight[N-1], ..., weight[1], weight[0]} |
| request | C | Request signals from clients |
| grant_ack | C | Grant acknowledgment signals (ACK mode only) |

### Outputs

| Port | Width | Description |
|------|-------|-------------|
| grant_valid | 1 | Valid grant indicator |
| grant | C | Grant vector (one-hot encoded) |
| grant_id | N | Grant client ID (binary encoded) |

## Functionality

### Credit-Based Weighting

The arbiter uses a credit-based system for weighted bandwidth allocation:

1. **Credit Initialization**: Each client's credit counter is initialized to its weight value
2. **Grant Completion**: When a grant completes, the client's credit counter decrements
3. **Credit Eligibility**: Only clients with non-zero credits are eligible for round-robin arbitration
4. **Global Replenishment**: When no requesting clients have credits, all credits are reloaded

### Arbitration Stages

1. **Credit Eligibility**: Filter requests to only clients with credits > 0
2. **Round-Robin Selection**: Base arbiter (`arbiter_round_robin`) selects among eligible clients
3. **Grant Output**: Winning client receives one-hot grant signal
4. **Credit Update**: Winner's credit decrements on completion (immediate or ACK-based)

### Weight Ratio Example

For weights [4, 2, 1, 1]:
- **Client 0**: 4 credits → gets 4 consecutive grants
- **Client 1**: 2 credits → gets 2 consecutive grants
- **Client 2**: 1 credit → gets 1 grant
- **Client 3**: 1 credit → gets 1 grant
- **Pattern**: C0, C0, C0, C0, C1, C1, C2, C3, [replenish], repeat...
- **Bandwidth**: C0=50%, C1=25%, C2=12.5%, C3=12.5%

## Dynamic Weight Changes

### Weight Management FSM

The module includes a finite state machine for atomic weight updates:

| State | Description |
|-------|-------------|
| WEIGHT_IDLE | Normal operation |
| WEIGHT_BLOCK | Detect weight change, block new grants |
| WEIGHT_DRAIN | Wait for pending ACK completion (2 cycles) |
| WEIGHT_UPDATE | Atomic weight update, reset credits |
| WEIGHT_STABILIZE | System stabilization (3 cycles) |

### Weight Update Sequence

1. **Detection**: FSM detects `max_thresh` change from shadow register
2. **Block**: New grants blocked, pending grants drain
3. **Drain**: Wait for ACK completion (ACK mode) or fixed delay
4. **Update**: Atomic update of weights, credit counters reset
5. **Stabilize**: System stabilization period
6. **Resume**: Return to normal operation

**Total Latency**: 5-15 cycles depending on pending ACKs

### Safety Features

- **Shadow Register**: Active weights stored in `r_safe_max_thresh` for race-free updates
- **Timeout Protection**: 15-cycle timeout prevents FSM lockup
- **Credit Reset**: Credits reset to new weights during WEIGHT_STABILIZE state
- **ACK Awareness**: FSM waits for pending `grant_ack` before updating weights

## Implementation Details

### Credit Management

```systemverilog
// Credit decrement on grant completion
if (w_grant_completed[i] && r_credit_counter[i] > 0) begin
    w_credit_counter[i] = r_credit_counter[i] - 1;
end
```

**Grant Completion Modes:**
- **No-ACK Mode**: Completion when `grant[i] && grant_valid` (same cycle)
- **ACK Mode**: Completion when `grant[i] && grant_valid && grant_ack[i]` (delayed)

### Global Replenishment Logic

```systemverilog
// Replenish when no requesting clients have credits
assign w_global_replenish = (w_normal_operation && !w_pending_grants &&
                             (|request) && !w_requesting_clients_with_credits);

// On replenish: reload all credit counters to their weights
if (w_global_replenish) begin
    w_credit_counter[i] = client_weight[i];
end
```

### Request Masking for Fairness

```systemverilog
// Only pass eligible clients to round-robin arbiter
assign w_requesting_eligible[i] = request[i] &&
                                   ((w_has_crd[i]) ||
                                    (w_global_replenish && client_weight[i] > 0));

// Apply masking for fairness among multiple eligible clients
assign w_mask_req[i] = (multiple_eligible) ?
                       (w_requesting_eligible[i] && !grant[i]) :
                       (w_requesting_eligible[i] && r_credit_counter[i] > 1);
```

### Sub-Module: arbiter_round_robin

Uses base `arbiter_round_robin` module internally for fair selection among eligible clients:

```systemverilog
arbiter_round_robin #(
    .CLIENTS      (CLIENTS),
    .WAIT_GNT_ACK (WAIT_GNT_ACK)
) u_base_arbiter (
    .clk        (clk),
    .rst_n      (rst_n),
    .block_arb  (w_sub_block_arb),
    .request    (w_mask_req),
    .grant_ack  (grant_ack),
    .grant_valid(grant_valid),
    .grant      (grant),
    .grant_id   (grant_id),
    .last_grant (r_last_grant)
);
```

## Special Features

### Zero-Weight Client Handling

Clients with `max_thresh = 0` are effectively disabled:
- Never accumulate credits
- Never participate in arbitration
- Credit counters remain at zero

### ACK Protocol Support

When `WAIT_GNT_ACK = 1`:
- Grant remains asserted until `grant_ack` received
- Credit decrement waits for ACK
- Weight change FSM waits for pending ACKs
- Enables pipelined/posted transaction masters

When `WAIT_GNT_ACK = 0`:
- Grant completes immediately (1 cycle)
- Credit decrements same cycle as grant
- Optimal for simple masters (no pipeline)

### Starvation Prevention

The arbiter guarantees starvation-free operation:
- All non-zero weight clients eventually served
- Maximum starvation time: Sum of all other clients' weights
- Global replenishment ensures fairness

## Usage Examples

### Basic QoS Arbiter (No-ACK Mode)

```systemverilog
// 4-client arbiter with QoS weights: 8:4:2:1
localparam int NUM_CLIENTS = 4;
localparam int MAX_WEIGHT = 16;
localparam int WEIGHT_W = $clog2(MAX_WEIGHT);

logic [NUM_CLIENTS-1:0] client_req, client_grant;
logic grant_vld;
logic [$clog2(NUM_CLIENTS)-1:0] grant_idx;
logic [NUM_CLIENTS*WEIGHT_W-1:0] qos_weights;

// Assign QoS weights (high priority = higher weight)
assign qos_weights = {4'd1, 4'd2, 4'd4, 4'd8};  // {C3, C2, C1, C0}

arbiter_round_robin_weighted #(
    .CLIENTS(NUM_CLIENTS),
    .MAX_LEVELS(MAX_WEIGHT),
    .WAIT_GNT_ACK(0)           // No-ACK mode
) u_qos_arbiter (
    .clk        (clk),
    .rst_n      (rst_n),
    .block_arb  (1'b0),
    .max_thresh (qos_weights),
    .request    (client_req),
    .grant_ack  ('0),           // Unused in No-ACK mode
    .grant_valid(grant_vld),
    .grant      (client_grant),
    .grant_id   (grant_idx)
);
```

### Dynamic Weight Adjustment

```systemverilog
// Adjust weights based on priority events
logic [NUM_CLIENTS*WEIGHT_W-1:0] r_qos_weights;

always_ff @(posedge clk) begin
    if (high_priority_event) begin
        r_qos_weights[7:0] <= 4'd15;  // Boost Client 0 weight
    end else if (normal_priority) begin
        r_qos_weights[7:0] <= 4'd4;   // Reset Client 0 weight
    end
end

arbiter_round_robin_weighted #(
    .CLIENTS(NUM_CLIENTS),
    .MAX_LEVELS(MAX_WEIGHT),
    .WAIT_GNT_ACK(0)
) u_dynamic_arbiter (
    .clk        (clk),
    .rst_n      (rst_n),
    .block_arb  (1'b0),
    .max_thresh (r_qos_weights),  // Dynamic weights
    .request    (client_req),
    .grant_ack  ('0),
    .grant_valid(grant_vld),
    .grant      (client_grant),
    .grant_id   (grant_idx)
);
```

### ACK Mode for Pipelined Masters

```systemverilog
// ACK mode arbiter for pipelined masters
arbiter_round_robin_weighted #(
    .CLIENTS(2),
    .MAX_LEVELS(8),
    .WAIT_GNT_ACK(1)            // ACK required
) u_ack_arbiter (
    .clk        (clk),
    .rst_n      (rst_n),
    .block_arb  (bus_busy),
    .max_thresh ({4'd3, 4'd5}),  // Weights [5, 3]
    .request    (m_req),
    .grant_ack  (m_done),        // Master completion signal
    .grant_valid(m_grant_vld),
    .grant      (m_grant),
    .grant_id   (m_id)
);
```

## Timing Characteristics

### Latency and Throughput

- **Latency**: 2 cycles (credit calculation + round-robin arbitration)
- **Throughput**: 1 grant per cycle (maximum)
- **Grant Hold**: No-ACK=1 cycle, ACK=Until grant_ack asserted
- **Weight Update**: 5-15 cycles (FSM: BLOCK→DRAIN→UPDATE→STABILIZE)
- **Reset**: Asynchronous (all credits→1, weights→default)

### Critical Paths

1. **Credit Comparison**: Credit counter → eligibility logic
2. **Request Filtering**: Eligible clients → masked requests
3. **Round-Robin**: Base arbiter selection logic

## Design Considerations

### When to Use Each Mode

**No-ACK Mode (WAIT_GNT_ACK=0):**
- ✅ Simple masters without pipelining
- ✅ Combinational logic masters
- ✅ Maximum throughput (1 grant/cycle)
- ⚠️ Grant completes same cycle (no hold)

**ACK Mode (WAIT_GNT_ACK=1):**
- ✅ Pipelined masters (e.g., AXI)
- ✅ Posted transaction buses
- ✅ Multi-cycle operations
- ⚠️ Reduced throughput (grant held until ACK)

### Weight Selection Guidelines

- **Finer QoS Control**: Increase `MAX_LEVELS` (but more credit counter bits)
- **Typical Range**: MAX_LEVELS=8 to 32 for most applications
- **Weight Ratio**: Should reflect desired bandwidth ratios
- **Zero Weights**: Effectively disable clients (never granted)

### Dynamic Weight Change Best Practices

- **⚠️ DO NOT** change weights every cycle (causes FSM thrashing)
- ✅ **Recommended**: Change weights on policy updates (millisecond timescale)
- ✅ **Safe**: FSM ensures atomic updates without race conditions
- ✅ **Timeout**: 15-cycle timeout prevents lockup

## Performance Characteristics

### Resource Utilization

| CLIENTS | MAX_LEVELS | FFs (Est.) | LUTs (Est.) |
|---------|------------|------------|-------------|
| 4 | 16 | ~40 | ~50 |
| 8 | 16 | ~70 | ~90 |
| 4 | 32 | ~45 | ~55 |
| 8 | 32 | ~80 | ~110 |

### Maximum Frequency

- **Typical**: 300-500 MHz (modern FPGAs)
- **Limiting Factor**: Credit comparison and request filtering logic

## Verification Notes

From the comprehensive test suite (`val/common/test_arbiter_round_robin_weighted.py`):

- **Coverage**: 94%
- **Key Test Scenarios**:
  - Weight ratio verification ([4,2,1,1] patterns)
  - Global credit replenishment
  - Dynamic weight changes (atomic updates)
  - ACK mode timing and weight updates
  - Zero weight handling (client disable)
  - Single client optimization
  - FSM timeout protection
  - Starvation prevention

**Test Command**: `pytest val/common/test_arbiter_round_robin_weighted.py -v`

## Related Modules

- **arbiter_round_robin.sv** - Base round-robin arbiter (used internally)
- **arbiter_round_robin_simple.sv** - Lightweight RR arbiter (no weights)
- **arbiter_priority_encoder.sv** - Fixed priority arbiter

## Navigation

- **[← Back to RTLCommon Index](index.md)**
- **[← Back to Main Documentation Index](../index.md)**
