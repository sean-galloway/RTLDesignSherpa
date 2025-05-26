# axil_slave

This SystemVerilog module implements a top-level AXI-Lite slave interface that provides comprehensive support for AXI4-Lite transactions. It integrates separate read and write channels with error monitoring and configurable buffering capabilities, designed to interface with a memory or backend block.

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

## Ports

### Global Signals
- `aclk`: System clock.
- `aresetn`: Active-low reset signal.

### Master AXI-Lite Interface (Input Side)

The module provides a complete AXI4-Lite master interface (incoming side):

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

### Slave AXI-Lite Interface (Output Side to memory/backend)

The module provides a complete AXI4-Lite slave interface to connect to memory or other backend:

#### Write Address Channel (AW)
- `s_axil_awaddr [AXIL_ADDR_WIDTH-1:0]`: Address for the write transaction.
- `s_axil_awprot [AXIL_PROT_WIDTH-1:0]`: Protection type for the write transaction.
- Handshake signals: `s_axil_awvalid`, `s_axil_awready`.

#### Write Data Channel (W)
- `s_axil_wdata [AXIL_DATA_WIDTH-1:0]`: Write data.
- `s_axil_wstrb [AXIL_DATA_WIDTH/8-1:0]`: Write strobes.
- Handshake signals: `s_axil_wvalid`, `s_axil_wready`.

#### Write Response Channel (B)
- `s_axil_bresp [1:0]`: Write response.
- Handshake signals: `s_axil_bvalid`, `s_axil_bready`.

#### Read Address Channel (AR)
- `s_axil_araddr [AXIL_ADDR_WIDTH-1:0]`: Address for the read transaction.
- `s_axil_arprot [AXIL_PROT_WIDTH-1:0]`: Protection type for the read transaction.
- Handshake signals: `s_axil_arvalid`, `s_axil_arready`.

#### Read Data Channel (R)
- `s_axil_rdata [AXIL_DATA_WIDTH-1:0]`: Read data.
- `s_axil_rresp [1:0]`: Read response.
- Handshake signals: `s_axil_rvalid`, `s_axil_rready`.

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

## Functionality

The module provides a comprehensive AXI4-Lite slave interface with the following key functions:

### Transaction Management

The `axil_slave` module serves as a top-level container that integrates and orchestrates:

1. **Read Path**: Managed by the `axil_slave_rd` submodule.
2. **Write Path**: Managed by the `axil_slave_wr` submodule.

Each path operates independently but shares the same clock and reset.

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

The buffer depths are configurable to adapt to different performance requirements.

## Implementation Details

### Top-Level Structure

The module instantiates two major submodules:

1. **axil_slave_wr**: Manages the complete write path (AW, W, and B channels).
2. **axil_slave_rd**: Manages the complete read path (AR and R channels).

Each submodule has its own error monitoring capabilities.

### Internal Connections

The top-level module provides direct pass-through of all I/O signals to the appropriate submodules. The connections include:

1. **Clock and Reset**: Shared across all submodules.
2. **All AXI Channel Signals**: Connected to the corresponding submodule.
3. **Error Information**: Separate interfaces for read and write paths.

### Write Path Architecture

The write path implemented by `axil_slave_wr` provides:

1. Error monitoring for AW, W, and B channels.
2. Buffering for improved performance.
3. Management of write data and response correlation.

### Read Path Architecture

The read path implemented by `axil_slave_rd` provides:

1. Error monitoring for AR and R channels.
2. Buffering for improved performance.
3. Management of read data correlation.

## Usage Considerations

1. **Buffer Sizing**:
   - Adjust skid buffer depths based on expected traffic patterns.
   - Larger depths improve performance but consume more resources.

2. **Timeout Configuration**:
   - Set timeout values based on expected system latencies.
   - Longer timeouts avoid false detection but delay error notification.

3. **Error Handling**:
   - Implement proper handling for errors reported through the error FIFOs.
   - Consider implementing retry mechanisms for recoverable errors.

## Integration Example

```systemverilog
axil_slave #(
    .AXIL_DATA_WIDTH(64),           // 64-bit data bus
    .SKID_DEPTH_AR(4),              // Deeper AR skid buffer
    .TIMEOUT_AR(2000)               // Longer AR timeout
) i_axil_slave (
    .aclk(system_clock),
    .aresetn(system_reset_n),
    
    // Connect master interface
    .fub_awaddr(m_axil_awaddr),
    .fub_awprot(m_axil_awprot),
    .fub_awvalid(m_axil_awvalid),
    .fub_awready(m_axil_awready),
    // ... (other master interface signals) ...
    
    // Connect slave interface
    .s_axil_awaddr(mem_awaddr),
    .s_axil_awprot(mem_awprot),
    .s_axil_awvalid(mem_awvalid),
    .s_axil_awready(mem_awready),
    // ... (other slave interface signals) ...
    
    // Connect error interface
    .fub_rd_error_valid(rd_error_valid),
    .fub_rd_error_ready(rd_error_ready),
    // ... (other error signals) ...
);
```

---

[Return to Index](index.md)

---