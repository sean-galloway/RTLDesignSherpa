# axi2apb_convert

This SystemVerilog module implements a protocol converter that bridges between AXI and APB interfaces. It translates AXI transactions into corresponding APB transactions, handling the protocol differences and ensuring proper transaction ordering and data integrity.

## Module Parameters

### Interface Width Parameters
- `AXI_ID_WIDTH`: Width of the AXI ID field (default: 8).
- `AXI_ADDR_WIDTH`: Width of the AXI address bus (default: 32).
- `AXI_DATA_WIDTH`: Width of the AXI data bus (default: 32).
- `AXI_USER_WIDTH`: Width of the AXI user field (default: 1).
- `APB_ADDR_WIDTH`: Width of the APB address bus (default: 32).
- `APB_DATA_WIDTH`: Width of the APB data bus (default: 32).

### Buffer Depth Parameters
- `SIDE_DEPTH`: Depth of the side queue used for transaction tracking (default: 6).

### Derived Parameters
- Various shorthands (AW, DW, IW, UW, etc.) for more concise references.
- `AXI2APBRATIO`: Ratio of AXI data width to APB data width, determining how many APB transactions are needed for one AXI transaction.
- Various packet widths for APB command and response formats.

## Ports

### Global Signals
- `aclk`: AXI clock domain clock.
- `aresetn`: Active-low reset signal.

### AXI Slave Stub Interface

#### Read Address Channel (AR)
- `r_s_axi_ar_pkt`: Packed AR channel signals.
- `r_s_axi_ar_count`: Count of AR channel transactions.
- Handshake signals: `r_s_axi_arvalid`, `w_s_axi_arready`.

#### Read Data Channel (R)
- `r_s_axi_r_pkt`: Packed R channel signals.
- Handshake signals: `w_s_axi_rvalid`, `r_s_axi_rready`.

#### Write Address Channel (AW)
- `r_s_axi_aw_pkt`: Packed AW channel signals.
- `r_s_axi_aw_count`: Count of AW channel transactions.
- Handshake signals: `r_s_axi_awvalid`, `w_s_axi_awready`.

#### Write Data Channel (W)
- `r_s_axi_w_pkt`: Packed W channel signals.
- Handshake signals: `r_s_axi_wvalid`, `w_s_axi_wready`.

#### Write Response Channel (B)
- `r_s_axi_b_pkt`: Packed B channel signals.
- Handshake signals: `w_s_axi_bvalid`, `r_s_axi_bready`.

### APB Master Interface

#### Command Channel
- `w_cmd_valid`: Command valid signal.
- `r_cmd_ready`: Command ready signal.
- `r_cmd_data`: Packed APB command data including address, data, strobes, and control flags.

#### Response Channel
- `r_rsp_valid`: Response valid signal.
- `w_rsp_ready`: Response ready signal.
- `r_rsp_data`: Packed APB response data including read data and status flags.

## Functionality

### Protocol Translation

The module translates between AXI and APB protocols, handling fundamental differences:

1. **AXI to APB Command Translation**:
   - Translates AXI read/write commands to APB PSEL/PENABLE/PWRITE sequences.
   - Handles address phase and data phase coordination.
   - Manages burst transactions by breaking them into individual APB transfers.

2. **Data Width Adaptation**:
   - Handles cases where AXI data width is larger than APB data width.
   - Divides wide AXI transactions into multiple narrower APB transactions.
   - Maintains proper data alignment and byte lane steering.

3. **Response Handling**:
   - Collects APB responses and translates them to AXI responses.
   - Aggregates multiple APB responses for wide AXI transactions.
   - Preserves error status and propagates it correctly.

### State Machine Control

The module implements a state machine to control protocol conversion:

1. **IDLE State**:
   - Initial state; waits for new AXI transactions.
   - Detects read or write commands and transitions to appropriate state.

2. **READ State**:
   - Handles AXI read transactions.
   - Manages address generation for sequential APB read transfers.
   - Tracks completion of reads based on burst length.

3. **WRITE State**:
   - Handles AXI write transactions.
   - Manages address generation for sequential APB write transfers.
   - Extracts appropriate data segments for each APB transfer.
   - Tracks completion of writes based on burst length.

### Transaction Tracking

The module maintains transaction information using a side queue:

1. **Transaction Metadata Storage**:
   - Records transaction type (read/write).
   - Preserves transaction ID for response correlation.
   - Tracks "last" status for proper burst termination.
   - Maintains user bits for round-trip preservation.

2. **Response Correlation**:
   - Matches APB responses with original AXI transactions.
   - Ensures proper ID, response code, and user bits in AXI responses.
   - Handles error propagation from APB to AXI.

## Implementation Details

### Data Path Management

The module includes sophisticated data path handling:

1. **Address Generation**:
   - Uses `axi_gen_addr` module to calculate sequential addresses for burst transactions.
   - Preserves proper alignment based on transaction size.
   - Manages both read and write address generation.

2. **Data Steering and Packing**:
   - For wide AXI to narrow APB: Extracts appropriate data segments.
   - For narrow APB to wide AXI: Accumulates data in shift register.
   - Handles proper byte lane steering based on address alignment.

3. **Response Assembly**:
   - Aggregates multiple APB responses for wide AXI transactions.
   - Preserves error status across multiple APB transfers.
   - Ensures correct data alignment in responses.

### APB Command and Response Formatting

The module uses packed formats for APB commands and responses:

1. **APB Command Format** (`r_cmd_data`):
   - `last`: Indicates the last transfer in a sequence.
   - `first`: Indicates the first transfer in a sequence.
   - `pwrite`: Indicates read (0) or write (1) operation.
   - `pprot`: Protection attributes.
   - `pstrb`: Write strobes.
   - `paddr`: APB address.
   - `pwdata`: Write data (for write operations).

2. **APB Response Format** (`r_rsp_data`):
   - `last`: Indicates the last response in a sequence.
   - `first`: Indicates the first response in a sequence.
   - `pslverr`: Error status from APB slave.
   - `prdata`: Read data (for read operations).

## Usage Considerations

1. **Data Width Ratio**:
   - For optimal performance, AXI_DATA_WIDTH should be a multiple of APB_DATA_WIDTH.
   - Common configurations: 32-bit APB with 32/64/128-bit AXI.

2. **Burst Handling**:
   - AXI bursts are broken into individual APB transfers.
   - Performance is optimal when burst addresses are sequential.

3. **Error Handling**:
   - PSLVERR on any APB transfer within a burst will cause the entire AXI burst to return an error.
   - Error status is preserved and propagated to the AXI master.

4. **Transaction Ordering**:
   - The module preserves AXI transaction ordering semantics.
   - Multiple outstanding transactions are handled properly.

5. **Timing Considerations**:
   - AXI transactions typically complete much slower when translated to APB.
   - Consider the performance impact in time-critical applications.

## Integration Example

```systemverilog
axi2apb_convert #(
    .AXI_DATA_WIDTH(64),           // 64-bit AXI data bus
    .APB_DATA_WIDTH(32),           // 32-bit APB data bus
    .SIDE_DEPTH(8)                 // Deeper side queue for more outstanding transactions
) i_axi2apb_convert (
    .aclk(axi_clock),
    .aresetn(reset_n),
    
    // Connect AXI interface from AXI slave stub
    // ... (connection of all AXI stub signals) ...
    
    // Connect APB command and response channels
    .w_cmd_valid(apb_cmd_valid),
    .r_cmd_ready(apb_cmd_ready),
    .r_cmd_data(apb_cmd_data),
    .r_rsp_valid(apb_rsp_valid),
    .w_rsp_ready(apb_rsp_ready),
    .r_rsp_data(apb_rsp_data)
);
```

## Performance Optimization

1. **Side Queue Depth**:
   - Adjust SIDE_DEPTH to support the expected number of outstanding transactions.
   - Deeper queue allows more parallelism but consumes more resources.

2. **Data Width Selection**:
   - Choose AXI and APB data widths to minimize the conversion ratio for better performance.
   - A 1:1 ratio (same width) provides the best performance.

3. **Burst Transaction Use**:
   - Despite the internal conversion, using AXI bursts is still more efficient than individual transactions.
   - The module optimizes address generation for sequential bursts.

---

[Return to Index](index.md)

---