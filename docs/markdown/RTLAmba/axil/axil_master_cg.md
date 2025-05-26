# axil_master_cg

This SystemVerilog module implements a top-level AXI-Lite master interface with clock gating functionality to reduce power consumption during idle periods. It integrates separate read and write channels with error monitoring, configurable buffering, and clock gating control.

## Module Parameters

### AXI-Lite Parameters
- `AXIL_ADDR_WIDTH`: Width of the AXI-Lite address bus (default: 32).
- `AXIL_DATA_WIDTH`: Width of the AXI-Lite data bus (default: 32).
- `AXI_ID_WIDTH`: Width of the AXI ID field (default: 8) - used for error reporting.
- `AXIL_PROT_WIDTH`: Width of the AXI-Lite protection field (fixed at 3 for AXI-Lite).

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
- `CG_IDLE_COUNT_WIDTH`: Width of the idle counter (default: 4) - determines how many idle cycles before clock gating activates.

## Ports

### Global Signals
- `aclk`: System clock.
- `aresetn`: Active-low reset signal.

### Clock Gating Configuration
- `i_cfg_cg_enable`: Enable signal for clock gating functionality.
- `i_cfg_cg_idle_count [CG_IDLE_COUNT_WIDTH-1:0]`: Number of idle cycles before clock gating activates.

### Slave AXI-Lite Interface (Input Side)

The module provides a complete AXI4-Lite slave interface:

#### Write Address Channel (AW)
- `fub_awaddr [AXIL_ADDR_WIDTH-1:0]`: Address for the write transaction.
- `fub_awprot [AXIL_PROT_WIDTH-1:0]`: Protection type for the write transaction.
- Handshake signals: `fub_awvalid`, `fub_awready`.

#### Write Data Channel (W)
- `fub_wdata [AXIL_DATA_WIDTH-1:0]`: Write data.
- `fub_wstrb [AXIL_DATA_WIDTH/8-1:0]`: Write strobes.
- Handshake signals: `fub_wvalid`, `fub_wready`.

#### Write Response Channel (B)
- `fub_bresp [1:0]`: Write response.
- Handshake signals: `fub_bvalid`, `fub_bready`.

#### Read Address Channel (AR)
- `fub_araddr [AXIL_ADDR_WIDTH-1:0]`: Address for the read transaction.
- `fub_arprot [AXIL_PROT_WIDTH-1:0]`: Protection type for the read transaction.
- Handshake signals: `fub_arvalid`, `fub_arready`.

#### Read Data Channel (R)
- `fub_rdata [AXIL_DATA_WIDTH-1:0]`: Read data.
- `fub_rresp [1:0]`: Read response.
- Handshake signals: `fub_rvalid`, `fub_rready`.

### Master AXI-Lite Interface (Output Side)

The module provides a complete AXI4-Lite master interface mirroring the slave interface:

- All five channels (AR, R, AW, W, B) with identical signal sets as on the slave side.
- Each channel has proper handshaking signals.

### Error FIFOs

#### Read Channel Error Information
- `fub_rd_error_type [3:0]`: Type of read error detected.
- `fub_rd_error_addr [AXIL_ADDR_WIDTH-1:0]`: Address associated with read error.
- `fub_rd_error_id [AXI_ID_WIDTH-1:0]`: ID associated with read error.
- Handshake signals: `fub_rd_error_valid`, `fub_rd_error_ready`.

#### Write Channel Error Information
- `fub_wr_error_type [3:0]`: Type of write error detected.
- `fub_wr_error_addr [AXIL_ADDR_WIDTH-1:0]`: Address associated with write error.
- `fub_wr_error_id [AXI_ID_WIDTH-1:0]`: ID associated with write error.
- Handshake signals: `fub_wr_error_valid`, `fub_wr_error_ready`.

### Clock Gating Status
- `o_wr_cg_gating`: Write path active gating indicator.
- `o_wr_cg_idle`: Write path all buffers empty indicator.
- `o_rd_cg_gating`: Read path active gating indicator.
- `o_rd_cg_idle`: Read path all buffers empty indicator.

## Functionality

The module provides a comprehensive AXI4-Lite master interface with clock gating capability:

### Transaction Management

The `axil_master_cg` module serves as a top-level container that integrates and orchestrates:

1. **Read Path**: Managed by the `axil_master_rd_cg` submodule.
2. **Write Path**: Managed by the `axil_master_wr_cg` submodule.

Each path operates independently but shares the same clock and reset, with each implementing its own clock gating control.

### Clock Gating

The module implements intelligent clock gating to reduce power consumption:

1. **Idle Detection**: Monitors activity on all channels to determine when the module is idle.
2. **Configurable Idle Threshold**: Uses the idle counter to determine when to activate clock gating.
3. **Separate Gating**: Independent clock gating for read and write paths.
4. **Status Reporting**: Provides status signals indicating when clock gating is active.

### Error Monitoring

The module integrates comprehensive error monitoring for both read and write paths:

1. **Timeout Detection**: Detects timeouts on all AXI-Lite channels.
2. **Response Error Detection**: Identifies error responses (SLVERR, DECERR).
3. **Error Reporting**: Reports errors through dedicated FIFO interfaces.

### Buffering

The module implements buffering on all channels using skid buffers:

1. **Address Channels**: Buffers AR and AW transactions to improve timing and throughput.
2. **Data Channels**: Buffers R and W data to handle flow control.
3. **Response Channel**: Buffers B responses for proper handling.

## Implementation Details

### Top-Level Structure

The module instantiates two major submodules:

1. **axil_master_wr_cg**: Manages the complete write path (AW, W, and B channels) with clock gating.
2. **axil_master_rd_cg**: Manages the complete read path (AR and R channels) with clock gating.

Each submodule has its own error monitoring and clock gating capabilities.

### Clock Gating Architecture

Each path (read and write) implements its own clock gating controller:

1. **Activity Monitoring**: Monitors all valid signals to detect activity.
2. **Idle Counter**: Counts idle cycles to determine when to activate clock gating.
3. **Gated Clock Generation**: Generates a gated clock that stops when the path is idle.
4. **Ready Signal Handling**: Forces ready signals low when clock gating is active.

## Usage Considerations

1. **Clock Gating Configuration**:
   - Enable or disable clock gating using the `i_cfg_cg_enable` signal.
   - Configure the idle threshold using the `i_cfg_cg_idle_count` signal.

2. **Buffer Sizing**:
   - Adjust skid buffer depths based on expected traffic patterns.
   - Larger depths improve performance but consume more resources.

3. **Timeout Configuration**:
   - Set timeout values based on expected system latencies.
   - Longer timeouts avoid false detection but delay error notification.

4. **Error Handling**:
   - Implement proper handling for errors reported through the error FIFOs.
   - Consider implementing retry mechanisms for recoverable errors.

## Integration Example

```systemverilog
axil_master_cg #(
    .AXIL_DATA_WIDTH(64),            // 64-bit data bus
    .SKID_DEPTH_AR(4),               // Deeper AR skid buffer
    .TIMEOUT_AR(2000),               // Longer AR timeout
    .CG_IDLE_COUNT_WIDTH(6)          // Wider idle counter for more flexibility
) i_axil_master_cg (
    .aclk(system_clock),
    .aresetn(system_reset_n),
    
    // Clock gating configuration
    .i_cfg_cg_enable(cg_enable),
    .i_cfg_cg_idle_count(6'h20),     // 32 cycles before gating activates
    
    // Connect all AXI interfaces
    // ... (connection of all AXI signals) ...
    
    // Error handling
    .fub_rd_error_valid(rd_error_valid),
    .fub_rd_error_ready(rd_error_ready),
    // ... (other error signals) ...
    
    // Clock gating status
    .o_wr_cg_gating(wr_cg_gating),
    .o_wr_cg_idle(wr_cg_idle),
    .o_rd_cg_gating(rd_cg_gating),
    .o_rd_cg_idle(rd_cg_idle)
);
```

---

[Return to Index](index.md)

---