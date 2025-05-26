# axil_master_rd

This SystemVerilog module implements an AXI-Lite master read path that handles the AR (address read) and R (read data) channels of the AXI4-Lite interface. It provides error monitoring, buffering capabilities, and proper handshaking for AXI-Lite read transactions.

## Module Parameters

### AXI-Lite Parameters
- `AXIL_ADDR_WIDTH`: Width of the AXI-Lite address bus (default: 32).
- `AXIL_DATA_WIDTH`: Width of the AXI-Lite data bus (default: 32).
- `AXI_ID_WIDTH`: Width of the AXI ID field (default: 8) - used for error reporting.
- `AXIL_PROT_WIDTH`: Width of the AXI-Lite protection field (fixed at 3 for AXI-Lite).

### Skid Buffer Depths
- `SKID_DEPTH_AR`: Depth of the AR channel skid buffer (default: 2).
- `SKID_DEPTH_R`: Depth of the R channel skid buffer (default: 4).

### FIFO Parameters
- `ERROR_FIFO_DEPTH`: Depth of the error reporting FIFO (default: 2).
- `ADDR_FIFO_DEPTH`: Depth of the address tracking FIFO (default: 4).

### Timeout Parameters (in clock cycles)
- `TIMEOUT_AR`: Read address channel timeout (default: 1000).
- `TIMEOUT_R`: Read data channel timeout (default: 1000).

### Derived Parameters
- `AW`: Alias for AXIL_ADDR_WIDTH.
- `DW`: Alias for AXIL_DATA_WIDTH.
- `IW`: Alias for AXI_ID_WIDTH.
- `PW`: Alias for AXIL_PROT_WIDTH.
- `ARSize`: Size of AR channel signals (AW+PW).
- `RSize`: Size of R channel signals (DW+2).

## Ports

### Global Signals
- `aclk`: System clock.
- `aresetn`: Active-low reset signal.

### Slave AXI-Lite Interface (Input Side)

#### Read Address Channel (AR)
- `fub_araddr [AXIL_ADDR_WIDTH-1:0]`: Address for the read transaction.
- `fub_arprot [AXIL_PROT_WIDTH-1:0]`: Protection type for the read transaction.
- Handshake signals: `fub_arvalid`, `fub_arready`.

#### Read Data Channel (R)
- `fub_rdata [AXIL_DATA_WIDTH-1:0]`: Read data.
- `fub_rresp [1:0]`: Read response.
- Handshake signals: `fub_rvalid`, `fub_rready`.

### Master AXI-Lite Interface (Output Side)

#### Read Address Channel (AR)
- `m_axil_araddr [AXIL_ADDR_WIDTH-1:0]`: Address for the read transaction.
- `m_axil_arprot [AXIL_PROT_WIDTH-1:0]`: Protection type for the read transaction.
- Handshake signals: `m_axil_arvalid`, `m_axil_arready`.

#### Read Data Channel (R)
- `m_axil_rdata [AXIL_DATA_WIDTH-1:0]`: Read data.
- `m_axil_rresp [1:0]`: Read response.
- Handshake signals: `m_axil_rvalid`, `m_axil_rready`.

### Error FIFO Interface
- `fub_error_type [3:0]`: Type of error detected.
- `fub_error_addr [AXIL_ADDR_WIDTH-1:0]`: Address associated with the error.
- `fub_error_id [AXI_ID_WIDTH-1:0]`: ID associated with the error.
- Handshake signals: `fub_error_valid`, `fub_error_ready`.

## Functionality

The module provides an AXI4-Lite master read path with the following key functions:

### Error Monitoring

The module includes comprehensive error monitoring for the read path:

1. **Timeout Detection**: Detects timeouts on both AR and R channels.
2. **Response Error Detection**: Identifies error responses (SLVERR, DECERR).
3. **Error Reporting**: Reports errors through a dedicated FIFO interface.

### Buffering

The module implements buffering on both AR and R channels using skid buffers:

1. **AR Channel**: Buffers read address transactions to improve timing and throughput.
2. **R Channel**: Buffers read data to handle flow control.

The buffer depths are configurable to adapt to different performance requirements.

### Flow Control

The module implements proper flow control for AXI-Lite read transactions:

1. **Backpressure Handling**: Properly handles backpressure from the downstream AXI-Lite slave.
2. **Error-Based Flow Control**: Can block new transactions when errors are detected.

## Implementation Details

### Internal Structure

The module consists of three main components:

1. **Error Monitor**: `axi_errmon_base` instance that monitors AXI-Lite read transactions for errors.
2. **AR Skid Buffer**: `gaxi_skid_buffer` instance for the AR channel.
3. **R Skid Buffer**: `gaxi_skid_buffer` instance for the R channel.

### Error Monitoring

The error monitor tracks the following types of errors:

1. **AR Channel Timeout**: Timeout on the read address channel.
2. **R Channel Timeout**: Timeout on the read data channel.
3. **Error Response**: SLVERR or DECERR response on the R channel.

When an error is detected, it is reported through the error FIFO interface.

### Skid Buffers

The skid buffers provide several benefits:

1. **Timing Improvement**: Break timing paths between input and output interfaces.
2. **Throughput Enhancement**: Allow full throughput even with backpressure.
3. **Buffering**: Store multiple transactions when needed.

### Signal Connections

The module connects signals as follows:

1. **AR Channel**: Connects `fub_ar*` signals to `m_axil_ar*` signals through the AR skid buffer.
2. **R Channel**: Connects `m_axil_r*` signals to `fub_r*` signals through the R skid buffer.
3. **Error Signals**: Connects error monitor outputs to the error FIFO interface.

## Usage Considerations

1. **Buffer Sizing**:
   - Adjust skid buffer depths based on expected traffic patterns.
   - Larger depths improve performance but consume more resources.

2. **Timeout Configuration**:
   - Set timeout values based on expected system latencies.
   - Longer timeouts avoid false detection but delay error notification.

3. **Error Handling**:
   - Implement proper handling for errors reported through the error FIFO.
   - Consider implementing retry mechanisms for recoverable errors.

## Integration Example

```systemverilog
axil_master_rd #(
    .AXIL_DATA_WIDTH(64),           // 64-bit data bus
    .SKID_DEPTH_AR(4),              // Deeper AR skid buffer
    .TIMEOUT_AR(2000)               // Longer AR timeout
) i_axil_master_rd (
    .aclk(system_clock),
    .aresetn(system_reset_n),
    
    // Connect slave interface
    .fub_araddr(s_axil_araddr),
    .fub_arprot(s_axil_arprot),
    .fub_arvalid(s_axil_arvalid),
    .fub_arready(s_axil_arready),
    
    .fub_rdata(s_axil_rdata),
    .fub_rresp(s_axil_rresp),
    .fub_rvalid(s_axil_rvalid),
    .fub_rready(s_axil_rready),
    
    // Connect master interface
    .m_axil_araddr(m_axil_araddr),
    .m_axil_arprot(m_axil_arprot),
    .m_axil_arvalid(m_axil_arvalid),
    .m_axil_arready(m_axil_arready),
    
    .m_axil_rdata(m_axil_rdata),
    .m_axil_rresp(m_axil_rresp),
    .m_axil_rvalid(m_axil_rvalid),
    .m_axil_rready(m_axil_rready),
    
    // Connect error interface
    .fub_error_type(rd_error_type),
    .fub_error_addr(rd_error_addr),
    .fub_error_id(rd_error_id),
    .fub_error_valid(rd_error_valid),
    .fub_error_ready(rd_error_ready)
);
```

---

[Return to Index](index.md)

---