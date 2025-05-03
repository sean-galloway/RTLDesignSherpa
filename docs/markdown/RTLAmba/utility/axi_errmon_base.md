# axi_errmon_base

This SystemVerilog module serves as a comprehensive error monitoring system for AXI and AXI-Lite interfaces. It detects various protocol violations and timeout conditions in both read and write channels, providing an essential debugging mechanism for complex AXI-based designs.

## Module Parameters

### General Parameters

- `CHANNELS`: Number of channels to monitor (typically <= 2^AXI_ID_WIDTH), default is 1.
- `ADDR_WIDTH`: Width of the address bus (default: 32).
- `ID_WIDTH`: Width of the ID bus (default: 8, set to 0 for AXI-Lite).

### Timeout Parameters

- `TIMER_WIDTH`: Width of the timeout counters (default: 20).
- `TIMEOUT_ADDR`: Address channel timeout value in clock cycles (default: 1000).
- `TIMEOUT_DATA`: Data channel timeout value in clock cycles (default: 1000).
- `TIMEOUT_RESP`: Response channel timeout value for write transactions (default: 1000).

### FIFO Parameters

- `ERROR_FIFO_DEPTH`: Depth of the error reporting FIFO (default: 4).
- `ADDR_FIFO_DEPTH`: Depth of the address tracking FIFO (default: 4).

### Configuration Options

- `IS_READ`: Set to 1 for read channel monitoring, 0 for write channel monitoring.
- `IS_AXI`: Set to 1 for AXI, 0 for AXI-Lite protocol.

## Ports

### Clock and Reset

- `aclk`: AXI clock signal.
- `aresetn`: Active-low reset signal.

### Address Channel (AW/AR)

- `i_addr [ADDR_WIDTH-1:0]`: Address value for the transaction.
- `i_id [ID_WIDTH-1:0]`: Transaction ID.
- `i_valid`: Valid signal for the address channel.
- `i_ready`: Ready signal for the address channel.

### Data Channel (W/R)

- `i_data_id [ID_WIDTH-1:0]`: Data ID (read transactions only).
- `i_data_valid`: Valid signal for the data channel.
- `i_data_ready`: Ready signal for the data channel.
- `i_data_last`: Last data indicator for burst transactions.
- `i_data_resp [1:0]`: Response code (read transactions only).

### Response Channel (B)

- `i_resp_id [ID_WIDTH-1:0]`: Response ID (write transactions only).
- `i_resp [1:0]`: Response code.
- `i_resp_valid`: Valid signal for the response channel.
- `i_resp_ready`: Ready signal for the response channel.

### Error Output FIFO Interface

- `o_error_valid`: Valid signal for the error FIFO output.
- `i_error_ready`: Ready signal for the error FIFO input.
- `o_error_type [3:0]`: Error type indicator (one-hot encoded).
- `o_error_addr [ADDR_WIDTH-1:0]`: Address associated with the error.
- `o_error_id [ID_WIDTH-1:0]`: ID associated with the error.

### Flow Control

- `o_block_ready`: Signal to block new transactions when FIFOs are full.

## Functionality

### Error Detection

The module detects four primary types of errors (one-hot encoded):

1. **Address Timeout (0001)**: The address phase of a transaction doesn't complete within the specified timeout.
2. **Data Timeout (0010)**: The data phase of a transaction doesn't complete within the specified timeout.
3. **Response Timeout (0100)**: The response phase of a write transaction doesn't complete within the specified timeout.
4. **Response Error (1000)**: A transaction receives an error response (SLVERR or DECERR).

### Channel Monitoring

The module maintains separate monitors for each channel:

- **Address Channel Monitor**: Tracks the address phase of transactions for timeout violations.
- **Data Channel Monitor**: Monitors the data phase of transactions for timeout violations.
- **Response Channel Monitor**: (Write transactions only) Tracks write responses for timeout violations.

### FIFO Systems

The module includes several FIFO systems:

1. **Address Tracking FIFOs**: One per channel, to track address information associated with ongoing transactions.
2. **Write Data FIFO**: For write transactions, tracks write data phase information.
3. **Error Reporting FIFO**: Outputs detected errors with type, ID, and address information.

### Error Prioritization

Errors are prioritized in the following order (highest to lowest):
1. Response errors (SLVERR/DECERR)
2. Address timeout errors
3. Data timeout errors
4. Response timeout errors

## Channel Management

The module supports multi-channel operation by:

1. Using transaction IDs to determine the corresponding channel index.
2. Maintaining separate timeout counters and error flags for each channel.
3. Processing errors on a channel-by-channel basis with proper prioritization.

## Usage Notes

1. **Proper Reset Handling**: Ensure proper initialization by applying an active-low reset before use.
2. **FIFO Depths**: Adjust FIFO depths based on expected transaction loads. Shallow FIFOs may lead to backpressure.
3. **Timeout Values**: Set timeouts appropriately based on your system's latency characteristics.
4. **AXI vs. AXI-Lite**: Configure the `IS_AXI` parameter accordingly for your interface type.
5. **Error Handling**: Connect the error output FIFO to an appropriate error handling system.

## Implementation Details

### Timer Architecture

The module uses an optimized timer architecture to track transaction timeouts:
- Timers are started when a transaction phase begins (valid without ready).
- Timers increment each cycle until timeout occurs or transaction completes.
- Upon timeout, error information is stored or reported.

### Error Reporting Process

1. Errors are detected in each channel.
2. Error priority is determined for each channel.
3. The highest priority error is reported via the error FIFO.
4. If the error FIFO is full, errors are stored for later reporting.
5. Stored errors are processed when the error FIFO becomes available.

## Error Type Encoding

The 4-bit `o_error_type` signal is one-hot encoded:
- Bit 0: Address Timeout Error (`ErrorAddrTimeout` - 4'b0001)
- Bit 1: Data Timeout Error (`ErrorDataTimeout` - 4'b0010)
- Bit 2: Response Timeout Error (`ErrorRespTimeout` - 4'b0100)
- Bit 3: Response Error (`ErrorRespError` - 4'b1000)

---

[Return to Index](index.md)

---