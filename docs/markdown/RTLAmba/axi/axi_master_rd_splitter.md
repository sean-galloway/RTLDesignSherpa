# axi_master_rd_splitter

This SystemVerilog module implements an AXI transaction splitter for read operations. It divides AXI read transactions that cross memory alignment boundaries into multiple smaller transactions, ensuring memory access alignment requirements are met while maintaining proper transaction ordering and data integrity.

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
#### Read Address Channel (AR)
- `m_axi_arid [IW-1:0]`: Read address ID.
- `m_axi_araddr [AW-1:0]`: Read address.
- `m_axi_arlen [7:0]`: Burst length.
- `m_axi_arsize [2:0]`: Burst size.
- `m_axi_arburst [1:0]`: Burst type.
- Various control signals: `m_axi_arlock`, `m_axi_arcache`, `m_axi_arprot`, etc.
- Handshake signals: `m_axi_arvalid`, `m_axi_arready`.

#### Read Data Channel (R)
- `m_axi_rid [IW-1:0]`: Read data ID.
- `m_axi_rdata [DW-1:0]`: Read data.
- `m_axi_rresp [1:0]`: Read response.
- `m_axi_rlast`: Last read data indicator.
- `m_axi_ruser [UW-1:0]`: User-defined read data extension.
- Handshake signals: `m_axi_rvalid`, `m_axi_rready`.

### Flow Control
- `block_ready`: Signal from error monitor to block new transactions.

### Slave AXI Interface
#### Read Address Channel (AR)
- Complete AR channel signals mirroring the master interface.

#### Read Data Channel (R)
- Complete R channel signals mirroring the master interface.

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

The data path handling includes:

1. Maintaining the correct correlation between address and data phases.
2. Preserving AXI transaction attributes (size, burst type, etc.) across splits.
3. Ensuring proper handshaking on both master and slave sides.

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
   w_split_arlen = w_split_required ? 
                   8'(((w_dist_to_boundary >> fub_arsize) - 1)) : w_current_len;
   ```

### Split Information Tracking

The module maintains important transaction information for debugging and monitoring:

1. **Split Counter**: Tracks the number of splits performed for a transaction.
2. **Original Address and ID**: Recorded for later reference and correlation.
3. **FIFO Interface**: Provides this information to higher-level modules for monitoring.

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

4. **ID Management**:
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