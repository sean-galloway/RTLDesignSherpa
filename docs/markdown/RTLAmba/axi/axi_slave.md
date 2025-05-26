# axi_slave

This SystemVerilog module implements a top-level AXI slave interface that provides comprehensive support for AXI4 transactions. It integrates separate read and write channels with error monitoring and parameterizable buffering capabilities to act as a bridge between an AXI master and backend memory or peripheral logic.

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

## Ports

### Global Signals
- `aclk`: System clock.
- `aresetn`: Active-low reset signal.

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

### READ CHANNEL - Slave AXI Interface (Output Side to memory or backend)

#### Read Address Channel (AR)
- Complete set of AR channel signals mirroring the master interface.
- Handshake signals: `s_axi_arvalid`, `s_axi_arready`.

#### Read Data Channel (R)
- Complete set of R channel signals mirroring the master interface.
- Handshake signals: `s_axi_rvalid`, `s_axi_rready`.

### WRITE CHANNEL - Slave AXI Interface (Output Side to memory or backend)

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

## Functionality

The module provides a comprehensive AXI4 slave interface with the following key functions:

### Transaction Management

The `axi_slave` module serves as a top-level container that integrates and orchestrates:

1. **Read Path**: Managed by the `axi_slave_rd` submodule.
2. **Write Path**: Managed by the `axi_slave_wr` submodule.

Each path operates independently but shares the same clock and reset.

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

1. **axi_slave_rd**: Manages the complete read path (AR and R channels).
2. **axi_slave_wr**: Manages the complete write path (AW, W, and B channels).

Each submodule has its own error monitoring capabilities.

### Internal Connections

The top-level module provides direct pass-through of all I/O signals to the appropriate submodules. The connections include:

1. **Clock and Reset**: Shared across all submodules.
2. **All AXI Channel Signals**: Connected to the corresponding submodule.
3. **Error Information**: Separate interfaces for read and write paths.

### Write Path Architecture

The write path implemented by `axi_slave_wr` provides:

1. Error monitoring for AW, W, and B channels.
2. Buffering for improved performance.
3. Management of write data and response correlation.

### Read Path Architecture

The read path implemented by `axi_slave_rd` provides:

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

4. **Backend Integration**:
   - Connect the slave AXI interface to appropriate memory or peripheral logic.
   - Ensure the backend logic can handle the expected transaction patterns.

5. **QoS and Priority**:
   - Consider the QoS signals for transaction prioritization in complex systems.
   - Ensure proper handling of transaction ordering based on ID.

## Integration Example

```systemverilog
axi_slave #(
    .AXI_DATA_WIDTH(64),            // 64-bit data bus
    .SKID_DEPTH_R(8),               // Deeper R skid buffer
    .TIMEOUT_R(2000)                // Longer R timeout
) i_axi_slave (
    .aclk(system_clock),
    .aresetn(system_reset_n),
    
    // Connect master side (from AXI interconnect or master)
    // ... (connection of all master-side AXI signals) ...
    
    // Connect slave side (to memory controller or backend logic)
    // ... (connection of all slave-side AXI signals) ...
    
    // Error handling
    .fub_rd_error_valid(rd_error_valid),
    .fub_rd_error_ready(rd_error_ready),
    // ... (other error signals) ...
);
```

## Common Use Cases

1. **Memory Controller Interface**: Provides a standardized interface to DRAM or other memory controllers.

2. **Peripheral Controller Bridge**: Acts as a bridge between an AXI interconnect and peripheral-specific controllers.

3. **Protocol Bridge Front-End**: Serves as the front-end for bridges to other protocols (e.g., AXI to APB, AXI to AHB).

4. **Verification Harness**: Provides a standard interface for testing and verification of AXI masters.

5. **SoC Integration**: Enables standardized integration of IP cores within a System-on-Chip design.

## Performance Optimization

1. **Buffer Depth Tuning**:
   - Monitor transaction patterns in your application.
   - Increase buffer depths for channels with bursty traffic.

2. **Timeout Customization**:
   - Adjust timeout values based on observed system latencies.
   - Consider different timeout values for different channels.

3. **Error Handling Strategy**:
   - Develop a comprehensive error handling strategy for various error types.
   - Consider retry mechanisms for transient errors.

---

[Return to Index](index.md)

---