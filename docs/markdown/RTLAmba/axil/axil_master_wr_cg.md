# axil_master_wr_cg

This SystemVerilog module implements an AXI-Lite master write path with clock gating functionality. It handles the AW (address write), W (write data), and B (write response) channels of the AXI4-Lite interface with power-saving capabilities, error monitoring, buffering, and proper handshaking for AXI-Lite write transactions.

## Module Parameters

### AXI-Lite Parameters
- `AXIL_ADDR_WIDTH`: Width of the AXI-Lite address bus (default: 32).
- `AXIL_DATA_WIDTH`: Width of the AXI-Lite data bus (default: 32).
- `AXI_ID_WIDTH`: Width of the AXI ID field (default: 8) - used for error reporting.
- `AXIL_PROT_WIDTH`: Width of the AXI-Lite protection field (fixed at 3 for AXI-Lite).

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
- `CG_IDLE_COUNT_WIDTH`: Width of the idle counter (default: 4) - determines how many idle cycles before clock gating activates.

### Derived Parameters
- `AW`: Alias for AXIL_ADDR_WIDTH.
- `DW`: Alias for AXIL_DATA_WIDTH.
- `IW`: Alias for AXI_ID_WIDTH.
- `PW`: Alias for AXIL_PROT_WIDTH.

## Ports

### Global Signals
- `aclk`: System clock.
- `aresetn`: Active-low reset signal.

### Clock Gating Configuration
- `i_cfg_cg_enable`: Enable signal for clock gating functionality.
- `i_cfg_cg_idle_count [CG_IDLE_COUNT_WIDTH-1:0]`: Number of idle cycles before clock gating activates.

### Slave AXI-Lite Interface (Input Side)

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

### Master AXI-Lite Interface (Output Side)

#### Write Address Channel (AW)
- `m_axil_awaddr [AXIL_ADDR_WIDTH-1:0]`: Address for the write transaction.
- `m_axil_awprot [AXIL_PROT_WIDTH-1:0]`: Protection type for the write transaction.
- Handshake signals: `m_axil_awvalid`, `m_axil_awready`.

#### Write Data Channel (W)
- `m_axil_wdata [AXIL_DATA_WIDTH-1:0]`: Write data.
- `m_axil_wstrb [AXIL_DATA_WIDTH/8-1:0]`: Write strobes.
- Handshake signals: `m_axil_wvalid`, `m_axil_wready`.

#### Write Response Channel (B)
- `m_axil_bresp [1:0]`: Write response.
- Handshake signals: `m_axil_bvalid`, `m_axil_bready`.

### Error FIFO Interface
- `fub_error_type [3:0]`: Type of error detected.
- `fub_error_addr [AXIL_ADDR_WIDTH-1:0]`: Address associated with the error.
- `fub_error_id [AXI_ID_WIDTH-1:0]`: ID associated with the error.
- Handshake signals: `fub_error_valid`, `fub_error_ready`.

### Clock Gating Status
- `o_cg_gating`: Active gating indicator - shows when clock gating is active.
- `o_cg_idle`: All buffers empty indicator - shows when the module is in an idle state.

## Functionality

The module provides an AXI4-Lite master write path with clock gating capability:

### Clock Gating

The module implements intelligent clock gating to reduce power consumption:

1. **Idle Detection**: Monitors activity on all channels to determine when the module is idle.
2. **Configurable Idle Threshold**: Uses the idle counter to determine when to activate clock gating.
3. **Status Reporting**: Provides status signals indicating when clock gating is active.
4. **Ready Signal Handling**: Forces ready signals low when clock gating is active.

### Error Monitoring

The module includes comprehensive error monitoring for the write path:

1. **Timeout Detection**: Detects timeouts on AW, W, and B channels.
2. **Response Error Detection**: Identifies error responses (SLVERR, DECERR).
3. **Error Reporting**: Reports errors through a dedicated FIFO interface.

### Buffering

The module implements buffering on all three channels using skid buffers:

1. **AW Channel**: Buffers write address transactions to improve timing and throughput.
2. **W Channel**: Buffers write data to handle flow control.
3. **B Channel**: Buffers write responses for proper handling.

The buffer depths are configurable to adapt to different performance requirements.

### Flow Control

The module implements proper flow control for AXI-Lite write transactions:

1. **Backpressure Handling**: Properly handles backpressure from the downstream AXI-Lite slave.
2. **Error-Based Flow Control**: Can block new transactions when errors are detected.
3. **Clock Gating-Based Flow Control**: Forces ready signals low when clock gating is active.

## Implementation Details

### Internal Structure

The module consists of two main components:

1. **Clock Gate Controller**: `amba_clock_gate_ctrl` instance that manages the clock gating functionality.
2. **Base AXI-Lite Master Write Module**: `axil_master_wr` instance that handles the core functionality.

### Clock Gating Architecture

The clock gating architecture includes:

1. **Activity Monitoring**: OR-ing of all valid signals to detect activity.
2. **Idle Counter**: Counts idle cycles to determine when to activate clock gating.
3. **Gated Clock Generation**: Generates a gated clock that stops when the module is idle.
4. **Ready Signal Handling**: Forces ready signals low when clock gating is active.

### Signal Connections

The module connects signals as follows:

1. **Clock Signals**: Connects the system clock to the clock gate controller, and the gated clock to the base module.
2. **AXI-Lite Signals**: Connects the external AXI-Lite signals to the base module, with ready signals gated by the clock gating status.
3. **Error Signals**: Passes through error signals from the base module to the external interface.

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
   - Implement proper handling for errors reported through the error FIFO.
   - Consider implementing retry mechanisms for recoverable errors.

## Integration Example

```systemverilog
axil_master_wr_cg #(
    .AXIL_DATA_WIDTH(64),            // 64-bit data bus
    .SKID_DEPTH_AW(4),               // Deeper AW skid buffer
    .TIMEOUT_AW(2000),               // Longer AW timeout
    .CG_IDLE_COUNT_WIDTH(6)          // Wider idle counter for more flexibility
) i_axil_master_wr_cg (
    .aclk(system_clock),
    .aresetn(system_reset_n),
    
    // Clock gating configuration
    .i_cfg_cg_enable(cg_enable),
    .i_cfg_cg_idle_count(6'h20),     // 32 cycles before gating activates
    
    // Connect slave interface
    .fub_awaddr(s_axil_awaddr),
    .fub_awprot(s_axil_awprot),
    .fub_awvalid(s_axil_awvalid),
    .fub_awready(s_axil_awready),
    
    .fub_wdata(s_axil_wdata),
    .fub_wstrb(s_axil_wstrb),
    .fub_wvalid(s_axil_wvalid),
    .fub_wready(s_axil_wready),
    
    .fub_bresp(s_axil_bresp),
    .fub_bvalid(s_axil_bvalid),
    .fub_bready(s_axil_bready),
    
    // Connect master interface
    .m_axil_awaddr(m_axil_awaddr),
    .m_axil_awprot(m_axil_awprot),
    .m_axil_awvalid(m_axil_awvalid),
    .m_axil_awready(m_axil_awready),
    
    .m_axil_wdata(m_axil_wdata),
    .m_axil_wstrb(m_axil_wstrb),
    .m_axil_wvalid(m_axil_wvalid),
    .m_axil_wready(m_axil_wready),
    
    .m_axil_bresp(m_axil_bresp),
    .m_axil_bvalid(m_axil_bvalid),
    .m_axil_bready(m_axil_bready),
    
    // Connect error interface
    .fub_error_type(wr_error_type),
    .fub_error_addr(wr_error_addr),
    .fub_error_id(wr_error_id),
    .fub_error_valid(wr_error_valid),
    .fub_error_ready(wr_error_ready),
    
    // Connect clock gating status
    .o_cg_gating(wr_cg_gating),
    .o_cg_idle(wr_cg_idle)
);
```

---

[Return to Index](index.md)

---