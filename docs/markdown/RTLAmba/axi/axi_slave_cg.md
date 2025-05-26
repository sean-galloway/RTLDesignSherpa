# axi_slave_cg

This SystemVerilog module implements a clock-gated AXI slave interface that extends the functionality of the base `axi_slave` module with power-saving capabilities. It monitors activity on all AXI channels and gates the clock when the interface is idle for a configurable duration.

## Module Parameters

### AXI Parameters
- `AXI_ID_WIDTH`: Width of the AXI ID field (default: 8).
- `AXI_ADDR_WIDTH`: Width of the AXI address bus (default: 32).
- `AXI_DATA_WIDTH`: Width of the AXI data bus (default: 32).
- `AXI_USER_WIDTH`: Width of the AXI user field (default: 1).

### Skid Buffer Depths
- `SKID_DEPTH_AR`: Depth of the AR channel skid buffer (default: 2).
- `SKID_DEPTH_R`: Depth of the R channel skid buffer (default: 4).
- `SKID_DEPTH_AW`: Depth of the AW channel skid buffer (default: 2).
- `SKID_DEPTH_W`: Depth of the W channel skid buffer (default: 4).
- `SKID_DEPTH_B`: Depth of the B channel skid buffer (default: 2).

### FIFO Parameters
- `ERROR_FIFO_DEPTH`: Depth of the error reporting FIFO (default: 2).

### Timeout Parameters (in clock cycles)
- `TIMEOUT_AR`: Read address channel timeout (default: 1000).
- `TIMEOUT_R`: Read data channel timeout (default: 1000).
- `TIMEOUT_AW`: Write address channel timeout (default: 1000).
- `TIMEOUT_W`: Write data channel timeout (default: 1000).
- `TIMEOUT_B`: Write response channel timeout (default: 1000).

### Clock Gating Parameters
- `CG_IDLE_COUNT_WIDTH`: Width of the idle counter used for clock gating (default: 4).

## Ports

### Global Signals
- `aclk`: System clock.
- `aresetn`: Active-low reset signal.

### Clock Gating Configuration
- `i_cfg_cg_enable`: Global clock gate enable signal. When set to 1, the clock gating functionality is enabled; when set to 0, clock gating is disabled.
- `i_cfg_cg_idle_count [CG_IDLE_COUNT_WIDTH-1:0]`: Idle countdown value. This sets the number of idle cycles that must elapse before clock gating is activated.

### READ CHANNEL - Master AXI Interface (Input Side)

#### Read Address Channel (AR)
- Complete set of AR channel signals including ID, address, burst information, protection, QoS, etc.
- Handshake signals: `fub_arvalid`, `fub_arready`.

#### Read Data Channel (R)
- Complete set of R channel signals including ID, data, response, last indicator, etc.
- Handshake signals: `fub_rvalid`, `fub_rready`.

### WRITE CHANNEL - Master AXI Interface (Input Side)

#### Write Address Channel (AW)
- Complete set of AW channel signals including ID, address, burst information, protection, QoS, etc.
- Handshake signals: `fub_awvalid`, `fub_awready`.

#### Write Data Channel (W)
- Complete set of W channel signals including data, strobe, last indicator, etc.
- Handshake signals: `fub_wvalid`, `fub_wready`.

#### Write Response Channel (B)
- Complete set of B channel signals including ID, response, etc.
- Handshake signals: `fub_bvalid`, `fub_bready`.

### READ CHANNEL - Slave AXI Interface (Output Side to memory/backend)

#### Read Address Channel (AR)
- Complete set of AR channel signals mirroring the master interface.
- Handshake signals: `s_axi_arvalid`, `s_axi_arready`.

#### Read Data Channel (R)
- Complete set of R channel signals mirroring the master interface.
- Handshake signals: `s_axi_rvalid`, `s_axi_rready`.

### WRITE CHANNEL - Slave AXI Interface (Output Side to memory/backend)

#### Write Address Channel (AW)
- Complete set of AW channel signals mirroring the master interface.
- Handshake signals: `s_axi_awvalid`, `s_axi_awready`.

#### Write Data Channel (W)
- Complete set of W channel signals mirroring the master interface.
- Handshake signals: `s_axi_wvalid`, `s_axi_wready`.

#### Write Response Channel (B)
- Complete set of B channel signals mirroring the master interface.
- Handshake signals: `s_axi_bvalid`, `s_axi_bready`.

### Error FIFOs

#### Read Channel Error Information
- `fub_rd_error_type [3:0]`: Type of read error detected.
- `fub_rd_error_addr [AXI_ADDR_WIDTH-1:0]`: Address associated with read error.
- `fub_rd_error_id [AXI_ID_WIDTH-1:0]`: ID associated with read error.
- Handshake signals: `fub_rd_error_valid`, `fub_rd_error_ready`.

#### Write Channel Error Information
- `fub_wr_error_type [3:0]`: Type of write error detected.
- `fub_wr_error_addr [AXI_ADDR_WIDTH-1:0]`: Address associated with write error.
- `fub_wr_error_id [AXI_ID_WIDTH-1:0]`: ID associated with write error.
- Handshake signals: `fub_wr_error_valid`, `fub_wr_error_ready`.

### Clock Gating Status
- `o_rd_cg_gating`: Indicates when the read channel clock is gated.
- `o_rd_cg_idle`: Indicates when the read channel is idle.
- `o_wr_cg_gating`: Indicates when the write channel clock is gated.
- `o_wr_cg_idle`: Indicates when the write channel is idle.

## Functionality

### Clock Gating

The module enhances the base AXI slave functionality with power-saving capabilities:

1. **Activity Monitoring**: Continuously monitors all AXI channels for activity.
2. **Idle Detection**: Identifies when channels are idle (no pending transactions).
3. **Clock Gating**: Gates the clock when idle for the configured duration.
4. **Immediate Wake-up**: Quickly restores the clock when new activity is detected.

### Clock Gating Control

The clock gating behavior can be configured through:

1. **Global Enable (`i_cfg_cg_enable`)**: Enables or disables the entire clock gating functionality.
2. **Idle Count Threshold (`i_cfg_cg_idle_count`)**: Determines how many idle cycles must pass before activating clock gating.

### Split Clock Domains

The module independently gates the clock for read and write channels:

1. **Read Path Clock Gating**: Monitors and gates the clock for AR and R channels.
2. **Write Path Clock Gating**: Monitors and gates the clock for AW, W, and B channels.

Each path has its own status signals (`o_rd_cg_gating`, `o_rd_cg_idle`, etc.) for monitoring.

### AXI Functionality

The module inherits and preserves all functionality from the base `axi_slave` module:

1. **Error Monitoring**: Detects timeouts and error responses.
2. **Buffering**: Implements configurable-depth buffers on all channels.
3. **Transaction Management**: Handles AXI protocol requirements including burst transactions.

## Implementation Details

### Top-Level Structure

The module instantiates two clock-gated submodules:

1. **axi_slave_rd_cg**: Manages the clock-gated read path (AR and R channels).
2. **axi_slave_wr_cg**: Manages the clock-gated write path (AW, W, and B channels).

Each submodule integrates an `amba_clock_gate_ctrl` instance for clock gating.

### Clock Gating Implementation

The clock gating logic in each submodule:

1. Combines valid signals from both master and slave sides of the interface.
2. Counts idle cycles when no activity is detected.
3. Gates the clock when the idle count reaches the configured threshold.
4. Immediately restores the clock when new activity is detected.
5. Forces ready signals to 0 when clock gating is active to prevent data loss.

### Gated Clock Distribution

The module implements a hierarchical clock gating approach:

1. Each submodule has its own instance of `amba_clock_gate_ctrl`.
2. The gated clock is used to drive all internal logic within the submodule.
3. Clock gating status is exposed through dedicated output signals.

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
   - Monitor `o_rd_cg_gating`, `o_rd_cg_idle`, `o_wr_cg_gating`, and `o_wr_cg_idle` to observe clock gating behavior.
   - These signals can be useful for power optimization and debugging.

## Integration Example

```systemverilog
axi_slave_cg #(
    .AXI_DATA_WIDTH(64),            // 64-bit data bus
    .CG_IDLE_COUNT_WIDTH(6)         // 6-bit idle counter (0-63)
) i_axi_slave_cg (
    .aclk(system_clock),
    .aresetn(system_reset_n),
    
    // Clock gating configuration
    .i_cfg_cg_enable(1'b1),         // Enable clock gating
    .i_cfg_cg_idle_count(6'd20),    // Gate after 20 idle cycles
    
    // Connect all AXI interfaces
    // ... (connection of all AXI signals) ...
    
    // Status monitoring
    .o_rd_cg_gating(rd_clock_gated),
    .o_rd_cg_idle(rd_channel_idle),
    .o_wr_cg_gating(wr_clock_gated),
    .o_wr_cg_idle(wr_channel_idle)
);
```

## Power Optimization Tips

1. **Idle Count Tuning**:
   - Monitor traffic patterns and idle periods in your application.
   - Set the idle count threshold to be slightly shorter than typical idle periods.

2. **Enable/Disable Control**:
   - Consider dynamically enabling/disabling clock gating based on system power modes.
   - Disable clock gating during high-performance modes and enable during low-power modes.

3. **Channel-Specific Monitoring**:
   - Use the separate status signals for read and write channels to identify power optimization opportunities.
   - Different traffic patterns may benefit from different idle count settings.

---

[Return to Index](index.md)

---