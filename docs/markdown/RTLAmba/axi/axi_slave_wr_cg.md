# axi_slave_wr_cg

This SystemVerilog module implements a clock-gated AXI slave write controller that extends the functionality of the base `axi_slave_wr` module with power-saving capabilities. It monitors activity on the AXI write channels and gates the clock when the interface is idle for a configurable duration.

## Module Parameters

### AXI Parameters
- `AXI_ID_WIDTH`: Width of the AXI ID field (default: 8).
- `AXI_ADDR_WIDTH`: Width of the AXI address bus (default: 32).
- `AXI_DATA_WIDTH`: Width of the AXI data bus (default: 32).
- `AXI_USER_WIDTH`: Width of the AXI user field (default: 1).

### Skid Buffer Depths
- `SKID_DEPTH_AW`: Depth of the AW channel skid buffer (default: 2).
- `SKID_DEPTH_W`: Depth of the W channel skid buffer (default: 4).
- `SKID_DEPTH_B`: Depth of the B channel skid buffer (default: 2).

### FIFO Parameters
- `ERROR_FIFO_DEPTH`: Depth of the error reporting FIFO (default: 2).

### Timeout Parameters (in clock cycles)
- `TIMEOUT_AW`: Write address channel timeout (default: 1000).
- `TIMEOUT_W`: Write data channel timeout (default: 1000).
- `TIMEOUT_B`: Write response channel timeout (default: 1000).

### Clock Gating Parameters
- `CG_IDLE_COUNT_WIDTH`: Width of the idle counter used for clock gating (default: 4).

### Derived Parameters
- Various shorthands for parameter names (`AW`, `DW`, `IW`, `UW`) and calculated signal widths for packet formats.

## Ports

### Global Signals
- `aclk`: System clock.
- `aresetn`: Active-low reset signal.

### Clock Gating Configuration
- `i_cfg_cg_enable`: Global clock gate enable signal. When set to 1, the clock gating functionality is enabled; when set to 0, clock gating is disabled.
- `i_cfg_cg_idle_count [CG_IDLE_COUNT_WIDTH-1:0]`: Idle countdown value. This sets the number of idle cycles that must elapse before clock gating is activated.

### Master AXI Interface (Input Side)

#### Write Address Channel (AW)
- Complete set of AW channel signals including ID, address, burst information, protection, QoS, etc.
- Handshake signals: `fub_awvalid`, `fub_awready`.

#### Write Data Channel (W)
- Complete set of W channel signals including data, strobe, last indicator, etc.
- Handshake signals: `fub_wvalid`, `fub_wready`.

#### Write Response Channel (B)
- Complete set of B channel signals including ID, response, etc.
- Handshake signals: `fub_bvalid`, `fub_bready`.

### Slave AXI Interface (Output Side to memory or backend)

#### Write Address Channel (AW)
- Complete set of AW channel signals mirroring the master interface.
- Handshake signals: `s_axi_awvalid`, `s_axi_awready`.

#### Write Data Channel (W)
- Complete set of W channel signals mirroring the master interface.
- Handshake signals: `s_axi_wvalid`, `s_axi_wready`.

#### Write Response Channel (B)
- Complete set of B channel signals mirroring the master interface.
- Handshake signals: `s_axi_bvalid`, `s_axi_bready`.

### Error Output FIFO Interface
- `fub_error_type [3:0]`: Type of error detected.
- `fub_error_addr [AXI_ADDR_WIDTH-1:0]`: Address associated with the error.
- `fub_error_id [AXI_ID_WIDTH-1:0]`: ID associated with the error.
- Handshake signals: `fub_error_valid`, `fub_error_ready`.

### Clock Gating Status
- `o_cg_gating`: Indicates when the clock is gated.
- `o_cg_idle`: Indicates when the interface is idle.

## Functionality

### Clock Gating

The module enhances the base AXI slave write functionality with power-saving capabilities:

1. **Activity Monitoring**: Continuously monitors AXI write channels for activity.
2. **Idle Detection**: Identifies when channels are idle (no pending transactions).
3. **Clock Gating**: Gates the clock when idle for the configured duration.
4. **Immediate Wake-up**: Quickly restores the clock when new activity is detected.

### Clock Gating Control

The clock gating behavior can be configured through:

1. **Global Enable (`i_cfg_cg_enable`)**: Enables or disables the entire clock gating functionality.
2. **Idle Count Threshold (`i_cfg_cg_idle_count`)**: Determines how many idle cycles must pass before activating clock gating.

### AXI Functionality

The module inherits and preserves all functionality from the base `axi_slave_wr` module:

1. **Transaction Buffering**: Buffers address, data, and response transactions.
2. **Error Monitoring**: Detects timeouts and error responses.
3. **Flow Control**: Manages proper flow control between master and slave interfaces.

## Implementation Details

### Top-Level Structure

The module uses a hierarchical design approach:

1. **Clock Gating Controller**: An instance of `amba_clock_gate_ctrl` that manages clock gating based on activity.
2. **Gated Core**: An instance of the base `axi_slave_wr` module driven by the gated clock.
3. **Interface Logic**: Logic that connects the ungated external interface to the gated core.

### Activity Detection

The module detects activity through:

1. **User-Side Signals**: Monitors `fub_awvalid`, `fub_wvalid`, `fub_bready`, and `fub_error_valid`.
2. **AXI-Side Signals**: Monitors `s_axi_awvalid`, `s_axi_wvalid`, and `s_axi_bvalid`.
3. **Combined Activity**: Combines all activity signals to determine when the interface is active.

### Ready Signal Management

The module implements special handling for ready signals:

1. **Ready Forcing**: Forces ready signals to 0 when clock gating is active.
2. **Internal Ready**: Maintains internal ready signals that are not affected by clock gating.
3. **Handshake Protection**: Ensures proper handshaking despite clock gating.

### Clock Gating Implementation

The clock gating logic:

1. ORs all user-side valid signals to detect user-side activity.
2. ORs all AXI-side valid signals to detect AXI-side activity.
3. Uses these combined activity signals to control the clock gate controller.
4. Gates the clock when no activity is detected for the configured duration.
5. Exposes gating status through dedicated output signals.

## Usage Considerations

1. **Clock Gating Configuration**:
   - Set `i_cfg_cg_enable` to 1 to enable clock gating.
   - Configure `i_cfg_cg_idle_count` based on application requirements:
     - Shorter values save more power but may introduce more switching overhead.
     - Longer values reduce switching overhead but save less power.

2. **Performance vs. Power Trade-offs**:
   - Clock gating introduces a small latency penalty when waking up from idle.
   - Configure idle count threshold to balance power savings with performance impact.

3. **Buffer Sizing**:
   - Adjust skid buffer depths based on expected traffic patterns.
   - Consider the impact of buffer depth on clock gating effectiveness.

4. **Status Monitoring**:
   - Monitor `o_cg_gating` and `o_cg_idle` to observe clock gating behavior.
   - These signals can be useful for power optimization and debugging.

## Integration Example

```systemverilog
axi_slave_wr_cg #(
    .AXI_DATA_WIDTH(64),            // 64-bit data bus
    .CG_IDLE_COUNT_WIDTH(6)         // 6-bit idle counter (0-63)
) i_axi_slave_wr_cg (
    .aclk(system_clock),
    .aresetn(system_reset_n),
    
    // Clock gating configuration
    .i_cfg_cg_enable(1'b1),         // Enable clock gating
    .i_cfg_cg_idle_count(6'd20),    // Gate after 20 idle cycles
    
    // Connect master side (from AXI interconnect or master)
    // ... (connection of all master-side AXI signals) ...
    
    // Connect slave side (to memory controller or backend logic)
    // ... (connection of all slave-side AXI signals) ...
    
    // Error handling
    .fub_error_valid(wr_error_valid),
    .fub_error_ready(wr_error_ready),
    // ... (other error signals) ...
    
    // Status monitoring
    .o_cg_gating(write_clock_gated),
    .o_cg_idle(write_channel_idle)
);
```

## Power Optimization Tips

1. **Idle Count Tuning**:
   - Monitor traffic patterns and idle periods in your application.
   - Set the idle count threshold to be slightly shorter than typical idle periods.

2. **Enable/Disable Control**:
   - Consider dynamically enabling/disabling clock gating based on system power modes.
   - Disable clock gating during high-performance modes and enable during low-power modes.

3. **Active Period Handling**:
   - For systems with well-defined active and idle periods, consider setting different idle thresholds.
   - Use shorter thresholds during mostly-idle periods and longer thresholds during mostly-active periods.

---

[Return to Index](index.md)

---