# Monitor Bus Round-Robin Arbiter

**Module:** `monbus_arbiter.sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

The Monitor Bus Round-Robin Arbiter aggregates monitor bus packet streams from multiple clients into a single output stream using fair round-robin arbitration with ACK protocol. Optional skid buffers on inputs and output improve timing closure and provide elasticity for backpressure scenarios.

### Key Features

- Round-robin arbitration for monitor bus packet streams
- ACK mode operation (grants held until acknowledged)
- Optional input skid buffers per client (2, 4, 6, or 8 entry depth)
- Optional output skid buffer (2, 4, 6, or 8 entry depth)
- 64-bit monitor bus packet interface
- Parameterizable client count (1-64)
- Zero-latency pass-through when skid buffers disabled

---

## Module Purpose

This module serves as an aggregation point for monitor bus streams from multiple monitoring sources (AXI monitors, APB monitors, arbiter monitors, etc.). It ensures fair access to the consolidated monitor bus output while preventing packet loss through integrated buffering and proper backpressure handling.

The ACK protocol ensures that granted clients can complete their packet transmission before the arbiter moves to the next request, preventing fragmentation of multi-cycle transfers.

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| CLIENTS | int | 4 | Number of monitor bus clients (1-64) |
| INPUT_SKID_ENABLE | int | 1 | Enable skid buffers on input interfaces |
| OUTPUT_SKID_ENABLE | int | 1 | Enable skid buffer on output interface |
| INPUT_SKID_DEPTH | int | 2 | Depth of input skid buffers (2, 4, 6, or 8) |
| OUTPUT_SKID_DEPTH | int | 2 | Depth of output skid buffer (2, 4, 6, or 8) |

---

## Port Groups

### Clock and Reset

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| axi_aclk | input | 1 | Clock signal |
| axi_aresetn | input | 1 | Active-low asynchronous reset |

### Block Arbitration

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| block_arb | input | 1 | Block arbitration when asserted |

### Monitor Bus Inputs (Array of CLIENTS)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| monbus_valid_in[CLIENTS] | input | CLIENTS | Per-client packet valid signals |
| monbus_ready_in[CLIENTS] | output | CLIENTS | Per-client ready signals |
| monbus_packet_in[CLIENTS] | input | CLIENTS * 64 | Per-client 64-bit packets |

### Monitor Bus Output (Aggregated)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| monbus_valid | output | 1 | Aggregated packet valid |
| monbus_ready | input | 1 | Aggregated ready from downstream |
| monbus_packet | output | 64 | Aggregated 64-bit packet |

### Debug/Status Outputs

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| grant_valid | output | 1 | Grant is active this cycle |
| grant | output | CLIENTS | One-hot grant vector |
| grant_id | output | $clog2(CLIENTS) | Binary encoded grant ID |
| last_grant | output | CLIENTS | Previous grant (for round-robin rotation) |

---

## Functional Description

### Arbiter Request and Grant ACK Logic

The module maps monitor bus protocol to arbiter protocol:

**Request Mapping**: Each client's `monbus_valid_in[i]` becomes arbiter `request[i]`

**Grant ACK Logic**: ACK occurs when both grant is asserted AND client has valid data:
```systemverilog
grant_ack[i] = grant[i] && monbus_valid_in[i]
```

This implements the "stick on grant until both request and grant ack are high" requirement, ensuring clients can complete their packet transmission.

### Round-Robin Arbiter Instance

Uses arbiter_round_robin with WAIT_GNT_ACK=1:
- Fair rotation through active requests
- Grant held until acknowledged
- Block_arb input for external control

### Client Ready Signal Generation

Each client's ready signal asserted when:
1. That client is currently granted AND
2. Downstream (internal output) is ready to accept data

```systemverilog
monbus_ready_in[i] = grant[i] && int_monbus_ready
```

This ensures only the granted client can transfer data, preventing collisions.

### Output Multiplexer

Selects data from the granted client:
```systemverilog
if (grant_valid)
    int_monbus_packet = monbus_packet_in[grant_id];
```

### Optional Skid Buffers

**Input Skid Buffers** (per client):
- Uses gaxi_skid_buffer instances
- Provides elasticity for clients with bursty traffic
- Improves timing closure by breaking long paths
- Depth configurable: 2, 4, 6, or 8 entries

**Output Skid Buffer**:
- Buffers aggregated stream before output
- Prevents backpressure propagation to arbiter
- Same depth options as input buffers

**When to Enable Skid Buffers**:
- Enable INPUT_SKID if clients have high-latency paths or bursty traffic
- Enable OUTPUT_SKID if downstream consumer has variable latency
- Disable both for minimum latency (zero-overhead pass-through)

---

## Usage Example

```systemverilog
// Aggregate monitor bus streams from 4 clients
monbus_arbiter #(
    .CLIENTS             (4),
    .INPUT_SKID_ENABLE   (1),    // Enable input buffers
    .OUTPUT_SKID_ENABLE  (1),    // Enable output buffer
    .INPUT_SKID_DEPTH    (4),    // 4-entry input buffers
    .OUTPUT_SKID_DEPTH   (4)     // 4-entry output buffer
) u_monbus_arb (
    .axi_aclk            (clk),
    .axi_aresetn         (rst_n),
    .block_arb           (1'b0),  // Not blocked

    // Connect 4 client monitor bus streams
    .monbus_valid_in     ('{mon0_valid, mon1_valid, mon2_valid, mon3_valid}),
    .monbus_ready_in     ('{mon0_ready, mon1_ready, mon2_ready, mon3_ready}),
    .monbus_packet_in    ('{mon0_packet, mon1_packet, mon2_packet, mon3_packet}),

    // Aggregated output stream
    .monbus_valid        (agg_valid),
    .monbus_ready        (agg_ready),
    .monbus_packet       (agg_packet),

    // Debug outputs
    .grant_valid         (arb_grant_valid),
    .grant               (arb_grant_onehot),
    .grant_id            (arb_grant_id),
    .last_grant          (arb_last_grant)
);

// Downstream consumer (FIFO or packet decoder)
gaxi_fifo_sync #(
    .DATA_WIDTH (64),
    .DEPTH      (256)
) u_mon_aggregated_fifo (
    .axi_aclk   (clk),
    .axi_aresetn(rst_n),
    .wr_valid   (agg_valid),
    .wr_data    (agg_packet),
    .wr_ready   (agg_ready),
    .rd_valid   (fifo_valid),
    .rd_data    (fifo_packet),
    .rd_ready   (consumer_ready)
);
```

---

## Design Notes

### ACK Mode Operation

The ACK mode ensures proper packet transfer:

**Grant Assertion**: When arbiter selects a client, grant[i] asserts
**Client Response**: Client's monbus_valid_in[i] must be high
**Grant ACK**: grant_ack[i] = grant[i] && monbus_valid_in[i]
**Hold Grant**: Arbiter holds grant[i] until grant_ack[i] asserts
**Next Client**: After ACK, arbiter moves to next requesting client

This prevents:
- Packet fragmentation (grant switching mid-transfer)
- Lost packets (grant removed before client ready)
- Unfair arbitration (clients getting multiple back-to-back grants)

### Skid Buffer Depth Selection

Choose depth based on system characteristics:

**2 Entries (Minimum)**:
- Minimal buffering for timing closure only
- Use when clients have low, consistent latency

**4 Entries (Recommended)**:
- Good balance of buffering and area
- Handles typical backpressure scenarios
- Recommended for most systems

**6-8 Entries**:
- High buffering for very bursty traffic
- Use when downstream has high variable latency
- Higher area cost

### Zero-Latency Configuration

For minimum latency:
```systemverilog
.INPUT_SKID_ENABLE  (0),
.OUTPUT_SKID_ENABLE (0)
```

This provides direct combinational paths:
- monbus_valid_in[grant_id] -> monbus_valid (combinational)
- monbus_packet_in[grant_id] -> monbus_packet (combinational)
- monbus_ready -> monbus_ready_in[grant_id] (combinational)

Use when:
- Timing is not critical
- Clients and downstream have matched latencies
- Minimum latency required for event ordering

### Assertions

The module includes comprehensive assertions:

**Grant One-Hot**: Verifies grant vector is one-hot when valid
**Grant ID Consistency**: Verifies grant_id corresponds to asserted grant bit
**Ready Exclusivity**: Verifies only granted client receives ready signal

---

## Related Modules

### Used By
- System-level monitor bus aggregation hierarchies
- Multi-subsystem monitoring infrastructures

### Uses
- arbiter_round_robin.sv (ACK-mode arbiter)
- gaxi_skid_buffer.sv (optional input/output buffering)

### Related Modules
- arbiter_monbus_common.sv (generates monitor bus packets)
- arbiter_rr_pwm_monbus.sv (arbiter with integrated monitoring)

---

## References

### Specifications
- Internal: rtl/amba/PRD.md (AMBA subsystem requirements)
- Internal: docs/markdown/RTLAmba/includes/monitor_package_spec.md (monitor bus protocol)

### Source Code
- RTL: `rtl/amba/shared/monbus_arbiter.sv`
- Tests: `val/amba/test_monbus_arbiter.py` (if exists)

---

**Last Updated:** 2025-10-24

---

## Navigation

- [Back to Shared Infrastructure Index](README.md)
- [Back to RTLAmba Index](../README.md)
