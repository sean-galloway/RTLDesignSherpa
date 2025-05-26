# axi_master

This SystemVerilog module implements a top-level AXI master interface that provides comprehensive support for AXI4 transactions. It integrates separate read and write channels with advanced features including transaction splitting, error monitoring, and parameterizable buffering capabilities.

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
- `SPLIT_FIFO_DEPTH`: Depth of the split information FIFO (default: 2).
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

### Alignment Masks
- `rd_alignment_mask [11:0]`: 12-bit mask defining memory alignment boundaries for read operations.
- `wr_alignment_mask [11:0]`: 12-bit mask defining memory alignment boundaries for write operations.

### Slave AXI Interface (Input Side)

The module provides a complete AXI4 slave interface with all five channels:

#### Read Address Channel (AR)
- Complete set of AR channel signals including ID, address, burst information, protection, QoS, etc.
- Handshake signals: `fub_arvalid`, `fub_arready`.

#### Read Data Channel (R)
- Complete set of R channel signals including ID, data, response, last indicator, etc.
- Handshake signals: `fub_rvalid`, `fub_rready`.

#### Write Address Channel (AW)
- Complete set of AW channel signals including ID, address, burst information, protection, QoS, etc.
- Handshake signals: `fub_awvalid`, `fub_awready`.

#### Write Data Channel (W)
- Complete set of W channel signals including data, strobe, last indicator, etc.
- Handshake signals: `fub_wvalid`, `fub_wready`.

#### Write Response Channel (B)
- Complete set of B channel signals including ID, response, etc.
- Handshake signals: `fub_bvalid`, `fub_bready`.

### Master AXI Interface (Output Side)

The module provides a complete AXI4 master interface mirroring the slave interface:

- All five channels (AR, R, AW, W, B) with identical signal sets as on the slave side.
- Each channel has proper handshaking signals.

### Split Information FIFOs

#### Read Channel Split Information
- `fub_rd_split_addr [AXI_ADDR_WIDTH-1:0]`: Original address of the split read transaction.
- `fub_rd_split_id [AXI_ID_WIDTH-1:0]`: ID of the split read transaction.
- `fub_rd_split_cnt [7:0]`: Count of splits performed for read transaction.
- Handshake signals: `fub_rd_split_valid`, `fub_rd_split_ready`.

#### Write Channel Split Information
- `fub_wr_split_addr [AXI_ADDR_WIDTH-1:0]`: Original address of the split write transaction.
- `fub_wr_split_id [AXI_ID_WIDTH-1:0]`: ID of the split write transaction.
- `fub_wr_split_cnt [7:0]`: Count of splits performed for write transaction.
- Handshake signals: `fub_wr_split_valid`, `fub_wr_split_ready`.

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

## Functionality

The module provides a comprehensive AXI4 master interface with the following key functions:

### Transaction Management

The `axi_master` module serves as a top-level container that integrates and orchestrates:

1. **Read Path**: Managed by the `axi_master_rd` submodule.
2. **Write Path**: Managed by the `axi_master_wr` submodule.

Each path operates independently but shares the same clock and reset.

### Transaction Splitting

For both read and write operations, the module can split transactions that cross alignment boundaries:

1. **Read Splitting**: Divides read transactions that cross alignment boundaries into multiple smaller transactions.
2. **Write Splitting**: Divides write transactions that cross alignment boundaries into multiple smaller transactions.

The alignment boundaries can be configured separately for read and write operations using the `rd_alignment_mask` and `wr_alignment_mask` inputs.

### Error Monitoring

The module integrates comprehensive error monitoring for both read and write paths:

1. **Timeout Detection**: Detects timeouts on all AXI channels.
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

1. **axi_master_rd**: Manages the complete read path (AR and R channels).
2. **axi_master_wr**: Manages the complete write path (AW, W, and B channels).

Each submodule has its own error monitoring and transaction splitting capabilities.

### Internal Connections

The top-level module provides direct pass-through of all I/O signals to the appropriate submodules. The connections include:

1. **Clock and Reset**: Shared across all submodules.
2. **Alignment Masks**: Separate masks for read and write paths.
3. **All AXI Channel Signals**: Connected to the corresponding submodule.
4. **Split Information**: Separate interfaces for read and write paths.
5. **Error Information**: Separate interfaces for read and write paths.

### Write Path Architecture

The write path implemented by `axi_master_wr` provides:

1. Transaction splitting based on alignment boundaries.
2. Error monitoring for AW, W, and B channels.
3. Buffering for improved performance.
4. Management of write data and response correlation.

### Read Path Architecture

The read path implemented by `axi_master_rd` provides:

1. Transaction splitting based on alignment boundaries.
2. Error monitoring for AR and R channels.
3. Buffering for improved performance.
4. Management of read data correlation.

## Usage Considerations

1. **Alignment Configuration**:
   - Configure `rd_alignment_mask` and `wr_alignment_mask` based on memory system requirements.
   - Typical values include 0xFFF for 4KB page alignment.

2. **Buffer Sizing**:
   - Adjust skid buffer depths based on expected traffic patterns.
   - Larger depths improve performance but consume more resources.

3. **Timeout Configuration**:
   - Set timeout values based on expected system latencies.
   - Longer timeouts avoid false detection but delay error notification.

4. **Error Handling**:
   - Implement proper handling for errors reported through the error FIFOs.
   - Consider implementing retry mechanisms for recoverable errors.

5. **Split Information Utilization**:
   - The split information FIFOs provide visibility into transaction splitting.
   - This information can be useful for debugging and performance analysis.

## Integration Example

```systemverilog
axi_master #(
    .AXI_DATA_WIDTH(64),            // 64-bit data bus
    .SKID_DEPTH_AR(4),              // Deeper AR skid buffer
    .TIMEOUT_AR(2000)               // Longer AR timeout
) i_axi_master (
    .aclk(system_clock),
    .aresetn(system_reset_n),
    
    // Alignment masks for 4KB boundaries
    .rd_alignment_mask(12'hFFF),
    .wr_alignment_mask(12'hFFF),
    
    // Connect all AXI interfaces
    // ... (connection of all AXI signals) ...
    
    // Split information handling
    .fub_rd_split_valid(rd_split_valid),
    .fub_rd_split_ready(rd_split_ready),
    // ... (other split signals) ...
    
    // Error handling
    .fub_rd_error_valid(rd_error_valid),
    .fub_rd_error_ready(rd_error_ready),
    // ... (other error signals) ...
);
```

---

[Return to Index](index.md)

---