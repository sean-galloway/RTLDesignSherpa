# Weighted Round-Robin Arbiter with PWM and Monitor Bus

**Module:** `arbiter_wrr_pwm_monbus.sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

The Weighted Round-Robin Arbiter with PWM and Monitor Bus provides priority-based arbitration with configurable client weights, PWM flow control, and comprehensive silicon debug monitoring. This module extends round-robin arbitration with weight-based priority levels while maintaining the same monitoring infrastructure and standardized internal configurations.

### Key Features

- Weighted round-robin arbitration with configurable priorities
- Per-client weight thresholds (1 to MAX_LEVELS)
- PWM-based arbiter blocking for periodic control
- Standardized 16-bit PWM resolution
- Comprehensive fairness deviation monitoring
- Optional ACK protocol support
- Fixed internal sizing (16-entry FIFO, 256-cycle fairness reporting)
- Enhanced debug outputs for priority tracking

---

## Module Purpose

This module enables priority-based multi-master arbitration where different clients require different service levels. Higher-weight clients receive proportionally more grants while lower-weight clients still receive guaranteed service, preventing starvation. The integrated monitoring infrastructure tracks whether actual grant distribution matches configured weights and reports fairness violations.

The PWM integration allows temporal control of arbiter availability, enabling TDMA windows or bandwidth reservation combined with priority-based selection within each active window.

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| MAX_LEVELS | int | 16 | Maximum weight levels per client (1-64) |
| CLIENTS | int | 4 | Number of arbitration clients (1-64) |
| WAIT_GNT_ACK | int | 0 | ACK protocol enable (0=disable, 1=enable) |
| MON_AGENT_ID | logic [7:0] | 8'h10 | Monitor agent identifier |
| MON_UNIT_ID | logic [3:0] | 4'h0 | Monitor unit identifier |

### Fixed Internal Configurations (Not User-Configurable)

| Configuration | Value | Rationale |
|---------------|-------|-----------|
| PWM_WIDTH | 16 bits | Adequate resolution for most use cases |
| MON_FIFO_DEPTH | 16 entries | Optimal for monitoring scenarios |
| MON_FIFO_ALMOST_MARGIN | 2 entries | Safety margin for FIFO |
| FAIRNESS_REPORT_CYCLES | 256 cycles | Power-of-2 efficient interval |
| MIN_GRANTS_FOR_FAIRNESS | 64 grants | Statistical significance threshold |

---

## Port Groups

### Clock and Reset

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| clk | input | 1 | Clock signal |
| rst_n | input | 1 | Active-low asynchronous reset |

### Arbiter Configuration and Interface

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| cfg_arb_max_thresh | input | CLIENTS * $clog2(MAX_LEVELS) | Per-client weight thresholds |
| request | input | CLIENTS | Client request signals |
| grant_valid | output | 1 | Grant is valid this cycle |
| grant | output | CLIENTS | One-hot grant vector |
| grant_id | output | $clog2(CLIENTS) | Binary encoded grant ID |
| grant_ack | input | CLIENTS | Grant acknowledge signals (ACK mode only) |

### PWM Configuration

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| cfg_pwm_sync_rst_n | input | 1 | PWM synchronous reset (active-low) |
| cfg_pwm_start | input | 1 | Start PWM generation |
| cfg_pwm_duty | input | 16 | Duty cycle value (0 to period-1) |
| cfg_pwm_period | input | 16 | Period value (1 to 65535) |
| cfg_pwm_repeat_count | input | 16 | Number of periods (0=infinite) |
| cfg_pwm_sts_done | output | 1 | PWM sequence complete status |
| pwm_out | output | 1 | PWM output (controls arbiter blocking) |

### Monitor Configuration

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| cfg_mon_enable | input | 1 | Global monitor enable |
| cfg_mon_pkt_type_enable | input | 16 | Packet type enable mask |
| cfg_mon_latency_thresh | input | 16 | Latency threshold (cycles) |
| cfg_mon_starvation_thresh | input | 16 | Starvation threshold (cycles) |
| cfg_mon_fairness_thresh | input | 16 | Fairness deviation threshold (percent) |
| cfg_mon_active_thresh | input | 16 | Active request count threshold |
| cfg_mon_ack_timeout_thresh | input | 16 | ACK timeout threshold (cycles) |
| cfg_mon_efficiency_thresh | input | 16 | Grant efficiency threshold (percent) |
| cfg_mon_sample_period | input | 8 | Sample period for metrics |

### Monitor Bus Output

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| monbus_valid | output | 1 | Monitor bus packet valid |
| monbus_ready | input | 1 | Monitor bus ready (from downstream) |
| monbus_packet | output | 64 | 64-bit event packet |

### Enhanced Debug Outputs

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| debug_fifo_count | output | $clog2(17) | Monitor FIFO fill level |
| debug_packet_count | output | 16 | Total packets generated |
| debug_ack_timeout | output | CLIENTS | Per-client ACK timeout status |
| debug_protocol_violations | output | 16 | Protocol violation count |
| debug_grant_efficiency | output | 16 | Grant efficiency percentage |
| debug_client_starvation | output | CLIENTS | Per-client starvation flags |
| debug_fairness_deviation | output | 16 | Maximum fairness deviation |
| debug_monitor_state | output | 3 | Monitor internal state |

---

## Functional Description

The module integrates four key components:

### Weighted Round-Robin Arbiter

Provides priority-based arbitration using arbiter_round_robin_weighted:
- Per-client weight configuration via cfg_arb_max_thresh
- Higher weight = higher priority
- Fair rotation within same weight level
- Prevents starvation of low-priority clients
- Optional ACK protocol support

**Weight Encoding**: cfg_arb_max_thresh is a concatenated vector:
```
cfg_arb_max_thresh = {weight[CLIENTS-1], ..., weight[1], weight[0]}
```
Where each weight is $clog2(MAX_LEVELS) bits wide.

**Arbitration Algorithm**:
1. Identify all active requests
2. Select highest weight among active requests
3. Round-robin among clients with that weight
4. Issue grant and update rotation pointer

### PWM Generator

Controls arbiter availability (same as RR variant):
- 16-bit resolution
- Configurable duty cycle and period
- PWM output directly drives arbiter block_arb

### Monitor Bus Common

Comprehensive monitoring with enhanced fairness tracking:
- **WEIGHTED_MODE = 1** enables weight-aware fairness analysis
- Compares actual vs expected grant distribution based on configured weights
- Detects fairness violations when distribution deviates from weight ratios

**Fairness Calculation Example**:
```
4 clients with weights [8, 4, 2, 1] (total weight = 15)
Expected distribution:
  Client 0: (8/15) * 100 = 53.3%
  Client 1: (4/15) * 100 = 26.7%
  Client 2: (2/15) * 100 = 13.3%
  Client 3: (1/15) * 100 = 6.7%

Actual distribution measured over 256-cycle window.
Deviation = |actual% - expected%| for each client.
Event generated if max deviation > cfg_mon_fairness_thresh.
```

### Operation Flow

1. Configure per-client weights via cfg_arb_max_thresh
2. Clients assert request signals
3. PWM output modulates arbiter availability
4. When active, weighted arbiter grants highest-priority request
5. Monitor tracks grants and calculates fairness metrics
6. Fairness violations reported if distribution deviates from weights

---

## Usage Example

```systemverilog
// 4-client weighted arbiter with priorities [8, 4, 2, 1]
localparam int MAX_LEVELS = 16;
localparam int CLIENTS = 4;
localparam int WEIGHT_WIDTH = $clog2(MAX_LEVELS);  // 4 bits

// Configure client weights
logic [WEIGHT_WIDTH-1:0] client_weights [CLIENTS];
assign client_weights[0] = 4'd8;   // Highest priority
assign client_weights[1] = 4'd4;
assign client_weights[2] = 4'd2;
assign client_weights[3] = 4'd1;   // Lowest priority

wire [CLIENTS*WEIGHT_WIDTH-1:0] cfg_weights = {
    client_weights[3], client_weights[2],
    client_weights[1], client_weights[0]
};

arbiter_wrr_pwm_monbus #(
    .MAX_LEVELS              (MAX_LEVELS),
    .CLIENTS                 (CLIENTS),
    .WAIT_GNT_ACK            (1),         // Enable ACK protocol
    .MON_AGENT_ID            (8'h18),
    .MON_UNIT_ID             (4'h4)
) u_wrr_arb (
    .clk                     (clk),
    .rst_n                   (rst_n),

    // Arbiter configuration
    .cfg_arb_max_thresh      (cfg_weights),
    .request                 (client_requests),
    .grant_valid             (grant_valid),
    .grant                   (grant_onehot),
    .grant_id                (grant_binary),
    .grant_ack               (grant_ack),

    // PWM configuration - 40% availability
    .cfg_pwm_sync_rst_n      (1'b1),
    .cfg_pwm_start           (pwm_start),
    .cfg_pwm_duty            (16'd60),    // Block for 60 cycles
    .cfg_pwm_period          (16'd100),   // Out of 100 total
    .cfg_pwm_repeat_count    (16'd0),     // Infinite
    .cfg_pwm_sts_done        (pwm_done),
    .pwm_out                 (pwm_signal),

    // Monitor configuration
    .cfg_mon_enable          (1'b1),
    .cfg_mon_pkt_type_enable (16'h003F),
    .cfg_mon_latency_thresh  (16'd100),
    .cfg_mon_starvation_thresh (16'd500),
    .cfg_mon_fairness_thresh (16'd10),    // 10% deviation threshold
    .cfg_mon_active_thresh   (16'd4),
    .cfg_mon_ack_timeout_thresh (16'd200),
    .cfg_mon_efficiency_thresh (16'd75),
    .cfg_mon_sample_period   (8'd100),

    // Monitor bus output
    .monbus_valid            (mon_valid),
    .monbus_ready            (mon_ready),
    .monbus_packet           (mon_packet),

    // Enhanced debug outputs
    .debug_fifo_count        (mon_fifo_level),
    .debug_packet_count      (mon_pkt_count),
    .debug_ack_timeout       (mon_ack_timeouts),
    .debug_protocol_violations (mon_violations),
    .debug_grant_efficiency  (mon_efficiency),
    .debug_client_starvation (mon_starvation),
    .debug_fairness_deviation (mon_fairness_dev),
    .debug_monitor_state     (mon_state)
);
```

---

## Design Notes

### Weight Configuration

The cfg_arb_max_thresh parameter requires careful configuration:

**Valid Range**: Each client weight must be 1 to (MAX_LEVELS-1)
**Zero Weights**: Zero-weight clients are effectively disabled
**Dynamic Updates**: Weights can be changed runtime, but may cause temporary fairness violations during transition

**Example Calculation** (4 clients, MAX_LEVELS=16):
```systemverilog
localparam WEIGHT_WIDTH = 4;  // $clog2(16) = 4
logic [WEIGHT_WIDTH-1:0] w0 = 4'd12;  // 75% of max
logic [WEIGHT_WIDTH-1:0] w1 = 4'd6;   // 37.5% of max
logic [WEIGHT_WIDTH-1:0] w2 = 4'd3;   // 18.75% of max
logic [WEIGHT_WIDTH-1:0] w3 = 4'd1;   // 6.25% of max

assign cfg_arb_max_thresh = {w3, w2, w1, w0};  // LSB is client 0
```

### Fairness Deviation Threshold

The cfg_mon_fairness_thresh parameter should account for statistical variation:

**Recommended Values**:
- 5% for strict fairness enforcement
- 10% for typical systems (allows reasonable variation)
- 20% for relaxed monitoring

**Factors Affecting Deviation**:
- Short measurement windows (MIN_GRANTS_FOR_FAIRNESS)
- Bursty request patterns
- Weight ratio extremes (e.g., 16:1 vs 2:1)
- PWM blocking periods

### Enhanced Debug Outputs

This module exposes complete debug outputs from arbiter_monbus_common:

- **debug_client_starvation**: Bit vector showing starved clients
  - Use to identify clients not receiving service
  - Indicates potential weight configuration issues

- **debug_fairness_deviation**: Maximum deviation percentage
  - Real-time fairness metric without consuming monitor bus bandwidth
  - Connect to system debug registers for runtime visibility

- **debug_grant_efficiency**: Grant completion ratio
  - Low efficiency may indicate ACK timeout issues or downstream congestion

### ACK Mode with Weighted Arbitration

When WAIT_GNT_ACK=1, the arbiter waits for grant_ack before issuing next grant. This can affect fairness:

**Impact on Fairness**:
- Slow-ACK clients may receive fewer grants than their weight warrants
- ACK timeout tracking helps identify problematic clients
- Consider increasing cfg_mon_ack_timeout_thresh for clients with known slower response

---

## Related Modules

### Used By
- Priority-based interconnect arbiters
- QoS-aware memory controllers
- Multi-tier scheduling hierarchies

### Uses
- arbiter_round_robin_weighted.sv (core WRR arbiter)
- pwm.sv (PWM generator)
- arbiter_monbus_common.sv (monitoring with WEIGHTED_MODE=1)

### Related Modules
- arbiter_rr_pwm_monbus.sv (equal-priority variant)
- monbus_arbiter.sv (aggregates monitor bus streams)

---

## References

### Specifications
- Internal: rtl/amba/PRD.md (AMBA subsystem requirements)
- Internal: docs/markdown/RTLAmba/shared/arbiter_monbus_common.md (monitoring details)

### Source Code
- RTL: `rtl/amba/shared/arbiter_wrr_pwm_monbus.sv`
- Tests: `val/amba/test_arbiter_wrr_pwm_monbus.py`

---

**Last Updated:** 2025-10-24

---

## Navigation

- [Back to Shared Infrastructure Index](README.md)
- [Back to RTLAmba Index](../README.md)
