# axil_slave_wr

This SystemVerilog module implements an AXI-Lite slave write path that handles the AW (address write), W (write data), and B (write response) channels of the AXI4-Lite interface. It provides error monitoring, buffering capabilities, and proper handshaking for AXI-Lite write transactions, designed to interface with a memory or backend block.

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
- `ADDR_FIFO_DEPTH`: Depth of the address tracking FIFO (default: 4).

### Timeout Parameters (in clock cycles)
- `TIMEOUT_AW`: Write address channel timeout (default: 1000).
- `TIMEOUT_W`: Write data channel timeout (default: 1000).
- `TIMEOUT_B`: Write response channel timeout (default: 1000).

### Derived Parameters
- `AW`: Alias for AXIL_ADDR_WIDTH.
- `DW`: Alias for AXIL_DATA_WIDTH.
- `IW`: Alias for AXI_ID_WIDTH.
- `PW`: Alias for AXIL_PROT_WIDTH.

## Ports

### Global Signals
- `aclk`: System clock.
- `aresetn`: Active-low reset signal.

### Master AXI-Lite Interface (Input Side)

#### Write Address Channel (AW)
- `fub_awaddr [AXIL_ADDR_WIDTH-1:0]`: Address for the write transaction (output).
- `fub_awprot [AXIL_PROT_WIDTH-1:0]`: Protection type for the write transaction (output).
- Handshake signals: `fub_awvalid` (output), `fub_awready` (input).

#### Write Data Channel (W)
- `fub_wdata [AXIL_DATA_WIDTH-1:0]`: Write data (output).
- `fub_wstrb [AXIL_DATA_WIDTH/8-1:0]`: Write strobes (output).
- Handshake signals: `fub_wvalid` (output), `fub_wready` (input).

#### Write Response Channel (B)
- `fub_bresp [1:0]`: Write response (input).
- Handshake signals: `fub_bvalid` (input), `fub_bready` (output).

### Slave AXI-Lite Interface (Output Side to memory or backend)

#### Write Address Channel (AW)
- `s_axil_awaddr [AXIL_ADDR_WIDTH-1:0]`: Address for the write transaction (input).
- `s_axil_awprot [AXIL_PROT_WIDTH-1:0]`: Protection type for the write transaction (input).
- Handshake signals: `s_axil_awvalid` (input), `s_axil_awready` (output).

#### Write Data Channel (W)
- `s_axil_wdata [AXIL_DATA_WIDTH-1:0]`: Write data (input).
- `s_axil_wstrb [AXIL_DATA_WIDTH/8-1:0]`: Write strobes (input).
- Handshake signals: `s_axil_wvalid` (input), `s_axil_wready` (output).

#### Write Response Channel (B)
- `s_axil_bresp [1:0]`: Write response (output).
- Handshake signals: `s_axil_bvalid` (output), `s_axil_bready` (input).

### Error FIFO Interface
- `fub_error_type [3:0]`: Type of error detected.
- `fub_error_addr [AXIL_ADDR_WIDTH-1:0]`: Address associated with the error.
- `fub_error_id [AXI_ID_WIDTH-1:0]`: ID associated with the error.
- Handshake signals: `fub_error_valid`, `fub_error_ready`.

## Functionality

The module provides an AXI4-Lite slave write path with the following key functions:

### Data Transfer Direction

The `axil_slave_wr` module transfers data in the following directions:

1. **Write Address**: From slave-side input (`s_axil_aw*`) to master-side output (`fub_aw*`).
2. **Write Data**: From slave-side input (`s_axil_w*`) to master-side output (`fub_w*`).
3. **Write Response**: From master-side input (`fub_b*`) to slave-side output (`s_axil_b*`).

This reflects the typical flow in a slave interface where addresses and data come from the requester (slave side) and responses go back to the requester.

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

1. **Backpressure Handling**: Properly handles backpressure from both sides.
2. **Error-Based Flow Control**: Can block new transactions when errors are detected.

## Implementation Details

### Internal Structure

The module consists of four main components:

1. **Error Monitor**: `axi_errmon_base` instance that monitors AXI-Lite write transactions for errors.
2. **AW Skid Buffer**: `gaxi_skid_buffer` instance for the AW channel.
3. **W Skid Buffer**: `gaxi_skid_buffer` instance for the W channel.
4. **B Skid Buffer**: `gaxi_skid_buffer` instance for the B channel.

### Error Monitoring

The error monitor tracks the following types of errors:

1. **AW Channel Timeout**: Timeout on the write address channel.
2. **W Channel Timeout**: Timeout on the write data channel.
3. **B Channel Timeout**: Timeout on the write response channel.
4. **Error Response**: SLVERR or DECERR response on the B channel.

When an error is detected, it is reported through the error FIFO interface.

### Skid Buffers

The skid buffers provide several benefits:

1. **Timing Improvement**: Break timing paths between input and output interfaces.
2. **Throughput Enhancement**: Allow full throughput even with backpressure.
3. **Buffering**: Store multiple transactions when needed.

### Signal Connections

The module connects signals as follows:

1. **AW Channel**: Connects `s_axil_aw*` signals to `fub_aw*` signals through the AW skid buffer.
2. **W Channel**: Connects `s_axil_w*` signals to `fub_w*` signals through the W skid buffer.
3. **B Channel**: Connects `fub_b*` signals to `s_axil_b*` signals through the B skid buffer.
4. **Error Signals**: Connects error monitor outputs to the error FIFO interface.

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
axil_slave_wr #(
    .AXIL_DATA_WIDTH(64),           // 64-bit data bus
    .SKID_DEPTH_AW(4),              // Deeper AW skid buffer
    .TIMEOUT_AW(2000)               // Longer AW timeout
) i_axil_slave_wr (
    .aclk(system_clock),
    .aresetn(system_reset_n),
    
    // Connect master interface
    .fub_awaddr(m_axil_awaddr),
    .fub_awprot(m_axil_awprot),
    .fub_awvalid(m_axil_awvalid),
    .fub_awready(m_axil_awready),
    
    .fub_wdata(m_axil_wdata),
    .fub_wstrb(m_axil_wstrb),
    .fub_wvalid(m_axil_wvalid),
    .fub_wready(m_axil_wready),
    
    .fub_bresp(m_axil_bresp),
    .fub_bvalid(m_axil_bvalid),
    .fub_bready(m_axil_bready),
    
    // Connect slave interface
    .s_axil_awaddr(mem_awaddr),
    .s_axil_awprot(mem_awprot),
    .s_axil_awvalid(mem_awvalid),
    .s_axil_awready(mem_awready),
    
    .s_axil_wdata(mem_wdata),
    .s_axil_wstrb(mem_wstrb),
    .s_axil_wvalid(mem_wvalid),
    .s_axil_wready(mem_wready),
    
    .s_axil_bresp(mem_bresp),
    .s_axil_bvalid(mem_bvalid),
    .s_axil_bready(mem_bready),
    
    // Connect error interface
    .fub_error_type(wr_error_type),
    .fub_error_addr(wr_error_addr),
    .fub_error_id(wr_error_id),
    .fub_error_valid(wr_error_valid),
    .fub_error_ready(wr_error_ready)
);
```

---

[Return to Index](index.md)

---