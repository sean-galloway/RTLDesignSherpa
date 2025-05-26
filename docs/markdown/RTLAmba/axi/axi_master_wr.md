# axi_master_wr

This SystemVerilog module implements an AXI master write controller that manages write transactions on an AMBA AXI interface. It handles address, data, and response phases, transaction splitting, error monitoring, and flow control for AXI write operations.

## Module Parameters

### AXI Parameters
- `AXI_ID_WIDTH`: Width of the AXI ID field (default: 8).
- `AXI_ADDR_WIDTH`: Width of the AXI address bus (default: 32).
- `AXI_DATA_WIDTH`: Width of the AXI data bus (default: 32).
- `AXI_USER_WIDTH`: Width of the AXI user field (default: 1).

### Channel Parameters
- `CHANNELS`: Number of channels to monitor (default: 16). Typically ≤ 2^AXI_ID_WIDTH.

### Skid Buffer Depths
- `SKID_DEPTH_AW`: Depth of the AW channel skid buffer (default: 2).
- `SKID_DEPTH_W`: Depth of the W channel skid buffer (default: 4).
- `SKID_DEPTH_B`: Depth of the B channel skid buffer (default: 2).

### FIFO Parameters
- `SPLIT_FIFO_DEPTH`: Depth of the split information FIFO (default: 2).
- `ERROR_FIFO_DEPTH`: Depth of the error reporting FIFO (default: 2).
- `ADDR_FIFO_DEPTH`: Depth of the address tracking FIFO (default: 4).

### Timeout Parameters (in clock cycles)
- `TIMEOUT_AW`: Write address channel timeout (default: 1000).
- `TIMEOUT_W`: Write data channel timeout (default: 1000).
- `TIMEOUT_B`: Write response channel timeout (default: 1000).

### Derived Parameters
- Various shorthands for parameter names (`AW`, `DW`, `IW`, `UW`) and calculated signal widths for packet formats.

## Ports

### Global Signals
- `aclk`: System clock.
- `aresetn`: Active-low reset signal.

### Alignment Information
- `alignment_mask [11:0]`: 12-bit mask defining memory alignment boundaries.

### Slave AXI Interface (Input Side)

#### Write Address Channel (AW)
- Standard AW channel signals: `fub_awid`, `fub_awaddr`, `fub_awlen`, `fub_awsize`, `fub_awburst`, etc.
- Handshake signals: `fub_awvalid`/`fub_awready`.

#### Write Data Channel (W)
- Standard W channel signals: `fub_wdata`, `fub_wstrb`, `fub_wlast`, `fub_wuser`.
- Handshake signals: `fub_wvalid`/`fub_wready`.

#### Write Response Channel (B)
- Standard B channel signals: `fub_bid`, `fub_bresp`, `fub_buser`.
- Handshake signals: `fub_bvalid`/`fub_bready`.

### Master AXI Interface (Output Side)

#### Write Address Channel (AW)
- Standard AW channel signals: `m_axi_awid`, `m_axi_awaddr`, `m_axi_awlen`, etc.
- Handshake signals: `m_axi_awvalid`/`m_axi_awready`.

#### Write Data Channel (W)
- Standard W channel signals: `m_axi_wdata`, `m_axi_wstrb`, `m_axi_wlast`, `m_axi_wuser`.
- Handshake signals: `m_axi_wvalid`/`m_axi_wready`.

#### Write Response Channel (B)
- Standard B channel signals: `m_axi_bid`, `m_axi_bresp`, `m_axi_buser`.
- Handshake signals: `m_axi_bvalid`/`m_axi_bready`.

### Split Information FIFO Interface
- `fub_split_addr [AW-1:0]`: The address that was split.
- `fub_split_id [IW-1:0]`: The ID of the split transaction.
- `fub_split_cnt [7:0]`: The count of splits performed.
- Handshake signals: `fub_split_valid`/`fub_split_ready`.

### Error Output FIFO Interface
- `fub_error_type [3:0]`: The type of error detected.
- `fub_error_addr [AW-1:0]`: The address associated with the error.
- `fub_error_id [IW-1:0]`: The ID associated with the error.
- Handshake signals: `fub_error_valid`/`fub_error_ready`.

## Functionality

The module provides the following key functionalities:

### Transaction Splitting

The module includes a write transaction splitter (`axi_master_wr_splitter`) that divides large AXI transactions into smaller ones when they would cross specified alignment boundaries. This enables:
- Compliance with address alignment requirements.
- Optimized burst transfers that don't cross specific boundaries (e.g., 4KB pages).
- Enhanced performance by breaking up large transactions.

### Error Monitoring

An error monitoring subsystem (`axi_errmon_base`) tracks:
- Address timeouts: When AW channel transactions don't complete within the specified timeout.
- Data timeouts: When W channel transactions don't complete within the specified timeout.
- Response timeouts: When B channel transactions don't complete within the specified timeout.
- Response errors: When write responses indicate an error condition (SLVERR or DECERR).

### Data Buffering

Skid buffers are implemented for all channels:
- The AW channel buffer stores outgoing write address commands.
- The W channel buffer stores outgoing write data.
- The B channel buffer stores incoming write responses.
- These buffers help maintain performance by decoupling the handshaking on both sides of the interface.

### Flow Control

The module implements flow control mechanisms:
- Monitoring of FIFO fill levels to prevent overflow.
- Backpressure signaling through `int_block_ready` when FIFOs are full.
- Proper tracking of write bursts and their completion.

## Internal Components

The module instantiates the following key components:

1. **axi_master_wr_splitter**: Handles the splitting of write transactions based on alignment requirements.

2. **axi_errmon_base**: Monitors the AXI write channels for timeout conditions and response errors.

3. **gaxi_skid_buffer** (AW Channel): Buffers write address transactions, improving timing and throughput.

4. **gaxi_skid_buffer** (W Channel): Buffers write data, improving timing and throughput.

5. **gaxi_skid_buffer** (B Channel): Buffers write responses, improving timing and throughput.

## Implementation Details

### AXI Write Flow

1. Write requests arrive on the slave interface's AW and W channels.
2. The splitter checks if the request crosses alignment boundaries.
3. If splitting is needed, the transaction is divided into multiple smaller transactions.
4. The error monitor tracks each transaction for timeouts and errors.
5. Skid buffers temporarily store intermediate transactions and responses.
6. Write responses are collected and forwarded through the slave interface's B channel.

### Signal Packing and Unpacking

The module implements efficient signal packing and unpacking for AXI channels:
- AW channel signals are packed into a single `int_aw_pkt` signal for internal processing.
- W channel signals are similarly packed into `int_w_pkt` for efficient handling.
- B channel signals are packed into `int_b_pkt` for processing.
- Unpacking logic distributes these signals back to the appropriate output ports.

### Error Handling

Errors are signaled through the error FIFO interface with:
- Error type identification (timeout vs. response error).
- Address and ID information for debugging.
- Valid/ready handshaking for proper synchronization with error handling logic.

## Usage Considerations

1. **Alignment Mask Configuration**: The 12-bit `alignment_mask` should be configured based on system requirements, typically for 4KB page alignment (0xFFF).

2. **FIFO Depths**: FIFO depths should be tuned based on expected traffic patterns:
   - Larger depths improve performance with bursty traffic but consume more resources.
   - Smaller depths save resources but may limit performance under heavy loads.

3. **Timeout Values**: Timeout parameters should be set based on expected system latencies:
   - Too short: False positive timeouts during normal operation.
   - Too long: Delayed detection of real errors.

4. **ID Handling**: The module supports multiple outstanding transactions with different IDs. Ensure proper ID management in the system design.

5. **Reset Sequence**: Proper reset sequence should be followed to initialize all internal components before operation.

## Integration Example

```systemverilog
axi_master_wr #(
    .AXI_DATA_WIDTH(64),            // 64-bit data bus
    .SKID_DEPTH_W(8),               // Deeper W skid buffer
    .TIMEOUT_B(2000)                // Longer B timeout
) i_axi_master_wr (
    .aclk(system_clock),
    .aresetn(system_reset_n),
    
    // Alignment mask for 4KB boundaries
    .alignment_mask(12'hFFF),
    
    // Connect slave side (from user logic)
    // ... (connection of all slave-side AXI signals) ...
    
    // Connect master side (to AXI interconnect)
    // ... (connection of all master-side AXI signals) ...
    
    // Split and error information
    .fub_split_valid(split_valid),
    .fub_split_ready(split_ready),
    // ... (other related signals) ...
    
    .fub_error_valid(error_valid),
    .fub_error_ready(error_ready),
    // ... (other related signals) ...
);
```

## Performance Optimization

1. **Buffer Depth Tuning**:
   - Monitor transaction patterns in your application.
   - Increase buffer depths for channels with bursty traffic.
   - Consider different depths for different channels based on traffic patterns.

2. **Timeout Customization**:
   - Adjust timeout values based on observed system latencies.
   - Different channels may benefit from different timeout values.

3. **Alignment Considerations**:
   - Choose alignment boundaries based on memory system architecture.
   - Consider performance trade-offs of different alignment settings.

---

[Return to Index](index.md)

---