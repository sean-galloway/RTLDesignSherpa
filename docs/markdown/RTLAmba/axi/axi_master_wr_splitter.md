# axi_master_wr_splitter

This SystemVerilog module implements an AXI transaction splitter for write operations. It divides AXI write transactions that cross memory alignment boundaries into multiple smaller transactions, ensuring memory access alignment requirements are met while maintaining proper transaction ordering and data integrity.

## Module Parameters

### AXI Parameters
- `AXI_ID_WIDTH`: Width of the AXI ID field (default: 8).
- `AXI_ADDR_WIDTH`: Width of the AXI address bus (default: 32).
- `AXI_DATA_WIDTH`: Width of the AXI data bus (default: 32).
- `AXI_USER_WIDTH`: Width of the AXI user field (default: 1).

### FIFO Parameters
- `SPLIT_FIFO_DEPTH`: Depth of the split information FIFO (default: 4).

### Short Parameter Names
- Various shorthands (`IW`, `AW`, `DW`, `UW`) for more concise references within the module.

## Ports

### Global Signals
- `aclk`: System clock.
- `aresetn`: Active-low reset signal.

### Alignment Information
- `alignment_mask [11:0]`: 12-bit mask defining memory alignment boundaries.

### Master AXI Interface
#### Write Address Channel (AW)
- `m_axi_awid [IW-1:0]`: Write address ID.
- `m_axi_awaddr [AW-1:0]`: Write address.
- `m_axi_awlen [7:0]`: Burst length.
- `m_axi_awsize [2:0]`: Burst size.
- `m_axi_awburst [1:0]`: Burst type.
- Various control signals: `m_axi_awlock`, `m_axi_awcache`, `m_axi_awprot`, etc.
- Handshake signals: `m_axi_awvalid`, `m_axi_awready`.

#### Write Data Channel (W)
- `m_axi_wdata [DW-1:0]`: Write data.
- `m_axi_wstrb [DW/8-1:0]`: Write strobe.
- `m_axi_wlast`: Last write data indicator.
- `m_axi_wuser [UW-1:0]`: User-defined write data extension.
- Handshake signals: `m_axi_wvalid`, `m_axi_wready`.

#### Write Response Channel (B)
- `m_axi_bid [IW-1:0]`: Write response ID.
- `m_axi_bresp [1:0]`: Write response.
- `m_axi_buser [UW-1:0]`: User-defined response extension.
- Handshake signals: `m_axi_bvalid`, `m_axi_bready`.

### Flow Control
- `block_ready`: Signal from error monitor to block new transactions.

### Slave AXI Interface
#### Write Address Channel (AW)
- Complete AW channel signals mirroring the master interface.

#### Write Data Channel (W)
- Complete W channel signals mirroring the master interface.

#### Write Response Channel (B)
- Complete B channel signals mirroring the master interface.

### Split Information Output
- `fub_split_addr [AW-1:0]`: Original address of the split transaction.
- `fub_split_id [IW-1:0]`: ID of the split transaction.
- `fub_split_cnt [7:0]`: Count of splits performed.
- Handshake signals: `fub_split_valid`, `fub_split_ready`.

## Functionality

### State Machine

The module implements a three-state finite state machine to control transaction splitting:

1. **IDLE (3'b001)**:
   - Initial state; waits for new transactions.
   - Detects if incoming transactions cross boundaries.
   - Passes through transactions that don't require splitting.
   - Initiates splitting for transactions that cross boundaries.

2. **SPLITTING (3'b010)**:
   - Actively splits transactions into multiple subtransactions.
   - Calculates proper burst lengths for each split.
   - Tracks remaining transfers and next addresses.
   - Adjusts burst length for each subtransaction.

3. **LAST_SPLIT (3'b100)**:
   - Handles the final subtransaction of a split operation.
   - Completes the splitting process and returns to IDLE.

### Boundary Detection

The module performs these calculations for boundary detection:

1. Applies the `alignment_mask` to detect page or alignment boundaries.
2. Calculates transaction end address based on address, burst length, and size.
3. Determines if the transaction crosses a boundary by comparing masked start and end addresses.
4. Computes the distance to the next boundary for optimal splitting points.

### Split Transaction Management

For transactions requiring splitting, the module:

1. Divides the transaction into multiple smaller transactions with adjusted addresses and burst lengths.
2. Maintains proper order of all subtransactions.
3. Tracks the original transaction's information for later correlation.
4. Reports split information via the split information FIFO interface.

### Data Path

The write data path handling includes unique considerations:

1. Maintaining the correct correlation between address and data phases.
2. Generating proper `WLAST` signals for each split transaction.
3. Managing write data and strobes across split boundaries.
4. Tracking data beats with `r_data_counter` to properly mark the end of each split.

### Write-Specific Handling

The write splitter includes additional logic compared to the read splitter:

1. **WLAST Generation**: 
   - The module generates WLAST signals based on data counter tracking.
   - Original WLAST signals are used for non-split transactions.
   - Generated WLAST signals are created for split transactions.

2. **Data Alignment**:
   - Ensures proper data alignment across split boundaries.
   - Maintains byte strobe (`WSTRB`) coherence across splits.

3. **Response Correlation**:
   - Manages proper correlation of write responses to original transactions.
   - The original transaction ID is preserved for response matching.

## Implementation Details

### Transaction Splitting Algorithm

1. **Boundary Calculation**:
   ```
   w_boundary_mask = {{(AW-12){1'b0}}, alignment_mask};
   w_curr_boundary = (w_current_addr & ~w_boundary_mask) + (w_boundary_mask + 1);
   ```

2. **Crossing Detection**:
   ```
   w_split_required = ((w_current_addr & ~w_boundary_mask) != (w_end_addr & ~w_boundary_mask));
   ```

3. **Split Length Calculation**:
   ```
   w_dist_to_boundary = w_curr_boundary - w_current_addr;
   w_split_awlen = w_split_required ? 
                   8'(((w_dist_to_boundary >> fub_awsize) - 1)) : w_current_len;
   ```

### WLAST Generation

The module implements custom WLAST generation logic:

```systemverilog
// WLAST is generated for split bursts
assign w_modified_wlast = r_need_wlast ? (r_data_counter == 1) : fub_wlast;
```

This ensures proper burst termination for each split segment, while using original WLAST signals for non-split transactions.

### Data Counter Management

For tracking data beats within splits:

```systemverilog
// Manage data counter for WLAST generation
if (m_axi_wvalid && m_axi_wready && r_need_wlast) begin
    if (r_data_counter > 0) begin
        r_data_counter <= r_data_counter - 1;
    end
end
```

This counter is initialized with the burst length for each split and decremented with each data transfer until it reaches 1, triggering WLAST assertion.

## Usage Considerations

1. **Alignment Mask Configuration**:
   - The 12-bit `alignment_mask` is typically configured for 4KB boundaries (0xFFF).
   - Different alignment requirements can be set based on system needs.

2. **Performance Trade-offs**:
   - Transaction splitting adds latency but ensures correct memory access patterns.
   - The FIFO depth parameters should be sized based on expected traffic patterns.

3. **Integration with Error Monitoring**:
   - The `block_ready` signal allows an external error monitor to pause new transactions.
   - This is essential for robust error handling in complex systems.

4. **WSTRB Handling**:
   - The module preserves write strobe signals across splits.
   - This maintains proper byte-level write enable semantics.

5. **ID Management**:
   - The module preserves transaction IDs across splits.
   - System design should ensure proper ID management for out-of-order handling.

## Example Applications

1. **Cache Line Alignment**: Ensuring transfers don't cross cache line boundaries.
2. **Page Boundary Enforcement**: Preventing transactions from crossing DRAM page boundaries.
3. **Peripheral Alignment Requirements**: Meeting alignment requirements of specific peripherals.
4. **DMA Transfer Optimization**: Optimizing DMA transfers for better memory efficiency.

---

[Return to Index](index.md)

---