# axi_master_rd

This SystemVerilog module implements an AXI master read controller that manages read transactions on an AMBA AXI interface. It handles transaction splitting, address generation, error monitoring, and flow control for AXI read operations.

## Module Parameters

### AXI Parameters
- `AXI_ADDR_WIDTH`: Width of the address bus (default: 32).
- `AXI_DATA_WIDTH`: Width of the data bus (default: 32).
- `AXI_ID_WIDTH`: Width of the ID bus (default: 8).
- `AXI_USER_WIDTH`: Width of the user signals (default: 1).

### Channel Parameters
- `CHANNELS`: Number of channels to monitor (default: 16). Typically ≤ 2^AXI_ID_WIDTH.

### SKID Buffer Depths
- `SKID_DEPTH_AR`: Depth of the AR channel skid buffer (default: 2).
- `SKID_DEPTH_R`: Depth of the R channel skid buffer (default: 4).

### FIFO Parameters
- `SPLIT_FIFO_DEPTH`: Depth of the split information FIFO (default: 2).
- `ERROR_FIFO_DEPTH`: Depth of the error reporting FIFO (default: 2).
- `ADDR_FIFO_DEPTH`: Depth of the address tracking FIFO (default: 4).

### Timeout Parameters (in clock cycles)
- `TIMEOUT_AR`: Address read channel timeout (default: 1000).
- `TIMEOUT_R`: Read data channel timeout (default: 1000).

### Derived Parameters
- Various shorthands for parameter names (`AW`, `DW`, `IW`, `UW`) and calculated signal widths for packet formats.

## Ports

### Clock and Reset
- `aclk`: The system clock signal.
- `aresetn`: The active-low reset signal.

### Alignment Mask
- `alignment_mask [11:0]`: A 12-bit mask defining the alignment restrictions for AXI transactions.

### Slave AXI Interface (Input Side)

#### Read Address Channel (AR)
- Standard AR channel signals: `fub_arid`, `fub_araddr`, `fub_arlen`, `fub_arsize`, `fub_arburst`, etc.
- `fub_arvalid`/`fub_arready`: Handshake signals for AR channel.

#### Read Data Channel (R)
- Standard R channel signals: `fub_rid`, `fub_rdata`, `fub_rresp`, `fub_rlast`, etc.
- `fub_rvalid`/`fub_rready`: Handshake signals for R channel.

### Master AXI Interface (Output Side)

#### Read Address Channel (AR)
- Standard AR channel signals: `m_axi_arid`, `m_axi_araddr`, `m_axi_arlen`, etc. 
- `m_axi_arvalid`/`m_axi_arready`: Handshake signals for AR channel.

#### Read Data Channel (R)
- Standard R channel signals: `m_axi_rid`, `m_axi_rdata`, `m_axi_rresp`, etc.
- `m_axi_rvalid`/`m_axi_rready`: Handshake signals for R channel.

### Split Information FIFO Interface
- `fub_split_addr [AW-1:0]`: The address that was split.
- `fub_split_id [IW-1:0]`: The ID of the split transaction.
- `fub_split_cnt [7:0]`: The count of splits performed.
- `fub_split_valid`/`fub_split_ready`: Handshake signals for split information output.

### Error Output FIFO Interface
- `fub_error_type [3:0]`: The type of error detected.
- `fub_error_addr [AW-1:0]`: The address associated with the error.
- `fub_error_id [IW-1:0]`: The ID associated with the error.
- `fub_error_valid`/`fub_error_ready`: Handshake signals for error information output.

## Functionality

The module provides the following key functionalities:

### 1. Transaction Splitting

The module includes a read transaction splitter (`axi_master_rd_splitter`) that divides large AXI transactions into smaller ones when they would cross specified alignment boundaries. This enables:
- Compliance with address alignment requirements.
- Optimized burst transfers that don't cross specific boundaries (e.g., 4KB pages).
- Enhanced performance by breaking up large transactions.

### 2. Error Monitoring

An error monitoring subsystem (`axi_errmon_base`) tracks:
- Address timeouts: When AR channel transactions don't complete within the specified timeout.
- Data timeouts: When R channel transactions don't complete within the specified timeout.
- Response errors: When read responses indicate an error condition (SLVERR or DECERR).

### 3. Data Buffering

Skid buffers are implemented for both AR and R channels:
- The AR channel buffer stores outgoing read address commands.
- The R channel buffer stores incoming read data responses.
- These buffers help maintain performance by decoupling the handshaking on both sides of the interface.

### 4. Flow Control

The module implements flow control mechanisms:
- Monitoring of FIFO fill levels to prevent overflow.
- Backpressure signaling through `int_block_ready` when FIFOs are full.
- Proper tracking of read bursts and their completion.

## Internal Components

The module instantiates the following key components:

1. **axi_master_rd_splitter**: Handles the splitting of read transactions based on alignment requirements.

2. **axi_errmon_base**: Monitors the AXI read channels for timeout conditions and response errors.

3. **gaxi_skid_buffer** (AR Channel): Buffers read address transactions, improving timing and throughput.

4. **gaxi_skid_buffer** (R Channel): Buffers read data responses, improving timing and throughput.

## Implementation Details

### AXI Read Flow

1. Read requests arrive on the slave interface's AR channel.
2. The splitter checks if the request crosses alignment boundaries.
3. If splitting is needed, the transaction is divided into multiple smaller transactions.
4. The error monitor tracks each transaction for timeouts and errors.
5. Skid buffers temporarily store intermediate transactions and responses.
6. Read responses are collected and forwarded through the slave interface's R channel.

### Signal Packing and Unpacking

The module implements efficient signal packing and unpacking for AXI channels:
- AR channel signals are packed into a single `int_ar_pkt` signal for internal processing.
- R channel signals are similarly packed into `int_r_pkt` for efficient handling.
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

---

[Return to Index](index.md)

---