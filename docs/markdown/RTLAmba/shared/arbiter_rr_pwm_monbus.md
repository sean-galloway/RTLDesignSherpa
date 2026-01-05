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

# Round-Robin Arbiter with PWM and Monitor Bus

**Module:** `arbiter_rr_pwm_monbus.sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

The Round-Robin Arbiter with PWM and Monitor Bus combines fair round-robin arbitration with PWM-based flow control and comprehensive silicon debug monitoring. This standardized module uses fixed internal configurations for consistency while exposing only essential user-configurable parameters.

### Key Features

- Fair round-robin arbitration across N clients
- PWM-based arbiter blocking for periodic control
- Standardized 16-bit PWM resolution
- Comprehensive monitoring via arbiter_monbus_common
- Optional ACK protocol support
- Fixed internal sizing for consistency (16-entry FIFO, 256-cycle fairness reporting)
- Configurable client count (1-64)
- Real-time performance and fairness tracking

---

## Module Purpose

This module provides a complete arbitration solution for multi-master systems where equal priority access is required. The integrated PWM generator enables precise timing control for periodic arbitration windows, while the monitor bus integration provides real-time visibility into arbitration behavior, request latencies, and potential issues like starvation or protocol violations.

The standardized internal configurations (PWM width, FIFO depth, fairness intervals) ensure consistent behavior across all instantiations, simplifying integration and reducing parameter proliferation.

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
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

### Arbiter Interface

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
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
| cfg_pwm_repeat_count | input | 16 | Number of periods to generate (0=infinite) |
| cfg_pwm_sts_done | output | 1 | PWM sequence complete status |
| pwm_out | output | 1 | PWM output (controls arbiter blocking) |

### Monitor Configuration

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| cfg_mon_enable | input | 1 | Global monitor enable |
| cfg_mon_pkt_type_enable | input | 16 | Packet type enable mask |
| cfg_mon_latency | input | 16 | Latency threshold (cycles) |
| cfg_mon_starvation | input | 16 | Starvation threshold (cycles) |
| cfg_mon_fairness | input | 16 | Fairness deviation threshold (percent) |
| cfg_mon_active | input | 16 | Active request count threshold |
| cfg_mon_period | input | 8 | Sample period for metrics |

### Monitor Bus Output

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| monbus_valid | output | 1 | Monitor bus packet valid |
| monbus_ready | input | 1 | Monitor bus ready (from downstream) |
| monbus_packet | output | 64 | 64-bit event packet |

### Debug Outputs

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| debug_fifo_count | output | $clog2(17) | Monitor FIFO fill level (0-16) |
| debug_packet_count | output | 16 | Total packets generated |

---

## Functional Description

The module integrates three key components:

### Round-Robin Arbiter

Provides fair arbitration using the arbiter_round_robin module:
- Equal priority for all clients
- Sequential rotation through active requests
- Optional ACK protocol (WAIT_GNT_ACK=1)
- Block_arb input for external flow control

### PWM Generator

Controls arbiter availability through periodic blocking:
- 16-bit resolution (65536 discrete levels)
- Configurable duty cycle and period
- Repeat count for finite sequences
- PWM output directly drives arbiter block_arb input

**Duty Cycle Calculation**:
- pwm_out = 1 (arbiter blocked) for `cfg_pwm_duty` cycles
- pwm_out = 0 (arbiter active) for `cfg_pwm_period - cfg_pwm_duty` cycles

**Example**: 25% arbiter availability:
```systemverilog
cfg_pwm_period = 16'd100;      // 100-cycle period
cfg_pwm_duty   = 16'd75;       // Block for 75 cycles
// Result: arbiter active for 25 cycles, blocked for 75 cycles
```

### Monitor Bus Common

Comprehensive monitoring via arbiter_monbus_common:
- Default client weights = 1 (equal priority)
- Tracks grant distribution, latencies, starvation
- Fixed internal configurations ensure consistency
- Event packets include request latency, starvation detection, active request count

### Operation Flow

1. Clients assert request signals
2. PWM output modulates arbiter availability (pwm_out -> block_arb)
3. When arbiter active (pwm_out=0), round-robin arbiter grants one request
4. Monitor tracks arbitration events (grants, timeouts, fairness)
5. Event packets generated to monitor bus output
6. If ACK mode enabled, arbiter waits for grant_ack before next grant

---

## Usage Example

```systemverilog
// 8-client round-robin arbiter with 30% availability window
arbiter_rr_pwm_monbus #(
    .CLIENTS      (8),
    .WAIT_GNT_ACK (0),        // No ACK protocol
    .MON_AGENT_ID (8'h15),
    .MON_UNIT_ID  (4'h3)
) u_rr_arb (
    .clk                     (clk),
    .rst_n                   (rst_n),

    // Arbiter interface
    .request                 (client_requests),
    .grant_valid             (grant_valid),
    .grant                   (grant_onehot),
    .grant_id                (grant_binary),
    .grant_ack               (8'h00),  // Not used (ACK disabled)

    // PWM configuration - 30% availability
    .cfg_pwm_sync_rst_n      (1'b1),
    .cfg_pwm_start           (pwm_start),
    .cfg_pwm_duty            (16'd70),    // Block for 70 cycles
    .cfg_pwm_period          (16'd100),   // Out of 100 cycles total
    .cfg_pwm_repeat_count    (16'd0),     // Infinite repeat
    .cfg_pwm_sts_done        (pwm_done),
    .pwm_out                 (pwm_signal),

    // Monitor configuration
    .cfg_mon_enable          (1'b1),
    .cfg_mon_pkt_type_enable (16'h000F),  // Error, timeout, completion, threshold
    .cfg_mon_latency         (16'd50),    // 50-cycle latency warning
    .cfg_mon_starvation      (16'd200),   // 200-cycle starvation threshold
    .cfg_mon_fairness        (16'd15),    // 15% fairness deviation
    .cfg_mon_active          (16'd7),     // Warn if 7+ active requests
    .cfg_mon_period          (8'd128),

    // Monitor bus output
    .monbus_valid            (mon_valid),
    .monbus_ready            (mon_ready),
    .monbus_packet           (mon_packet),

    // Debug
    .debug_fifo_count        (mon_fifo_level),
    .debug_packet_count      (mon_pkt_count)
);

// Start PWM generation
initial begin
    pwm_start = 1'b0;
    @(posedge clk);
    pwm_start = 1'b1;
    @(posedge clk);
    pwm_start = 1'b0;
end
```

---

## Design Notes

### PWM Control Strategy

The PWM output directly controls arbiter blocking:
- **pwm_out = 1**: Arbiter blocked (no grants issued)
- **pwm_out = 0**: Arbiter active (can issue grants)

This allows precise timing control for:
- Time-division multiple access (TDMA) scheduling
- Bandwidth reservation windows
- Periodic maintenance operations
- Energy-efficient arbitration (idle periods)

### Fixed Configuration Benefits

The standardized internal configurations provide:
- **Consistency**: All instances behave identically
- **Predictability**: Known FIFO depths, fairness intervals
- **Simplified Integration**: Fewer parameters to configure
- **Verified Operation**: Tested configurations

If different internal sizes are needed, create a new variant rather than parameterizing.

### Fairness in Round-Robin Mode

All clients have equal priority (weight = 1 in monitoring logic). Fairness deviation events generated if any client receives significantly more or fewer grants than expected over the FAIRNESS_REPORT_CYCLES window (256 cycles).

Expected: Each client receives (1/CLIENTS) * 100% of grants
Threshold: cfg_mon_fairness parameter (percent)

### Monitor Bus Integration

See arbiter_monbus_common.md for complete monitoring details. Key points:
- Uses PROTOCOL_ARB (3'b011) event encoding
- Fixed 16-entry FIFO prevents event loss
- Per-client latency and starvation tracking
- Grant efficiency monitoring

---

## Related Modules

### Used By
- System arbitration hierarchies
- Multi-master interconnects
- TDMA scheduling systems

### Uses
- arbiter_round_robin.sv (core RR arbiter)
- pwm.sv (PWM generator)
- arbiter_monbus_common.sv (monitoring infrastructure)

### Related Modules
- arbiter_wrr_pwm_monbus.sv (weighted variant)
- monbus_arbiter.sv (aggregates monitor bus streams)

---

## References

### Specifications
- Internal: rtl/amba/PRD.md (AMBA subsystem requirements)
- Internal: docs/markdown/RTLAmba/shared/arbiter_monbus_common.md (monitoring details)

### Source Code
- RTL: `rtl/amba/shared/arbiter_rr_pwm_monbus.sv`
- Tests: `val/amba/test_arbiter_rr_pwm_monbus.py`

---

**Last Updated:** 2025-10-24

---

## Navigation

- [Back to Shared Infrastructure Index](README.md)
- [Back to RTLAmba Index](../README.md)
