# axi_master_rd_cg

This SystemVerilog module implements a clock-gated AXI master read controller that extends the functionality of the base `axi_master_rd` module with power-saving capabilities. It monitors activity on the AXI read channels and gates the clock when the interface is idle for a configurable duration.

## Module Parameters

### Alignment Parameters
- `ALIGNMENT_WIDTH`: Width of the alignment specification (default: 3). Determines data alignment requirements (0:8b, 1:16b, 2:32b, 3:64b, 4:128b, 5:256b, 6:512b).

### AXI Parameters
- `AXI_ID_WIDTH`: Width of the AXI ID field (default: 8).
- `AXI_ADDR_WIDTH`: Width of the AXI address bus (default: 32).
- `AXI_DATA_WIDTH`: Width of the AXI data bus (default: 32).
- `AXI_USER_WIDTH`: Width of the AXI user field (default: 1).

### Skid Buffer Depths
- `SKID_DEPTH_AR`: Depth of the AR channel skid buffer (default: 2).
- `SKID_DEPTH_R`: Depth of the R channel skid buffer (default: 4).

### FIFO Parameters
- `SPLIT_FIFO_DEPTH`: Depth of the split information FIFO (default: 2).
- `ERROR_FIFO_DEPTH`: Depth of the error reporting FIFO (default: 2).

### Timeout Parameters (in clock cycles)
- `TIMEOUT_AR`: Read address channel timeout (default: 1000).
- `TIMEOUT_R`: Read data channel timeout (default: 1000).

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

### Alignment Information
- `alignment_mask [11:0]`: 12-bit mask defining memory alignment boundaries.

### Slave AXI Interface (Input Side)

#### Read Address Channel (AR)
- Complete set of AR channel signals including ID, address, burst information, protection, QoS, etc.
- Handshake signals: `fub_arvalid`, `fub_arready`.

#### Read Data Channel (R)
- Complete set of R channel signals including ID, data, response, last indicator, etc.
- Handshake signals: `fub_rvalid`, `fub_rready`.

### Master AXI Interface (Output Side)

#### Read Address Channel (AR)
- Complete set of AR channel signals mirroring the slave interface.
- Handshake signals: `m_axi_arvalid`, `m_axi_arready`.

#### Read Data Channel (R)
- Complete set of R channel signals mirroring the slave interface.
- Handshake signals: `m_axi_rvalid`, `m_axi_rready`.

### Split Information FIFO Interface
- `fub_split_addr [AXI_ADDR_WIDTH-1:0]`: Original address of the split transaction.
- `fub_split_id [AXI_ID_WIDTH-1:0]`: ID of the split transaction.
- `fub_split_cnt [7:0]`: Count of splits performed.
- Handshake signals: `fub_split_valid`, `fub_split_ready`.

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

The module enhances the base AXI master read functionality with power-saving capabilities:

1. **Activity Monitoring**: Continuously monitors AXI read channels for activity.
2. **Idle Detection**: Identifies when channels are idle (no pending transactions).
3. **Clock Gating**: Gates the clock when idle for the configured duration.
4. **Immediate Wake-up**: Quickly restores the clock when new activity is detected.

### Clock Gating Control

The clock gating behavior can be configured through:

1. **Global Enable (`i_cfg_cg_enable`)**: Enables or disables the entire clock gating functionality.
2. **Idle Count Threshold (`i_cfg_cg_idle_count`)**: Determines how many idle cycles must pass before activating clock gating.

### AXI Functionality

The module inherits and preserves all functionality from the base `axi_master_rd` module:

1. **Transaction Splitting**: Divides read transactions that cross alignment boundaries.
2. **Error Monitoring**: Detects timeouts and error responses.
3. **Buffering**: Implements configurable-depth buffers on all channels.

## Implementation Details

### Top-Level Structure

The module uses a hierarchical design approach:

1. **Clock Gating Controller**: An instance of `amba_clock_gate_ctrl` that manages clock gating based on activity.
2. **Gated Core**: An instance of the base `axi_master_rd` module driven by the gated clock.
3. **Interface Logic**: Logic that connects the ungated external interface to the gated core.

### Activity Detection

The module detects activity through:

1. **User-Side Signals**: Monitors `fub_arvalid`, `fub_rready`, `fub_split_valid`, and `fub_error_valid`.
2. **AXI-Side Signals**: Monitors `m_axi_arvalid` and `m_axi_rvalid`.
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

2. **Alignment Configuration**:
   - Set `alignment_mask` based on memory system requirements (typically 0xFFF for 4KB alignment).

3. **Performance vs. Power Trade-offs**:
   - Clock gating introduces a small latency penalty when waking up from idle.
   - Configure idle count threshold to balance power savings with performance impact.

4. **Buffer Sizing**:
   - Adjust skid buffer depths based on expected traffic patterns.
   - Consider the impact of buffer depth on clock gating effectiveness.

5. **Status Monitoring**:
   - Monitor `o_cg_gating` and `o_cg_idle` to observe clock gating behavior.
   - These signals can be useful for power optimization and debugging.

## Integration Example

```systemverilog
axi_master_rd_cg #(
    .AXI_DATA_WIDTH(64),            // 64-bit data bus
    .CG_IDLE_COUNT_WIDTH(6)         // 6-bit idle counter (0-63)
) i_axi_master_rd_cg (
    .aclk(system_clock),
    .aresetn(system_reset_n),
    
    // Clock gating configuration
    .i_cfg_cg_enable(1'b1),         // Enable clock gating
    .i_cfg_cg_idle_count(6'd20),    // Gate after 20 idle cycles
    
    // Alignment mask for 4KB boundaries
    .alignment_mask(12'hFFF),
    
    // Connect all AXI interfaces
    // ... (connection of all AXI signals) ...
    
    // Status monitoring
    .o_cg_gating(read_clock_gated),
    .o_cg_idle(read_channel_idle)
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