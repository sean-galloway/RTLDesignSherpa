# axi_slave_stub

This SystemVerilog module implements a complete AXI slave stub interface that handles all five channels of the AXI4 protocol: write address (AW), write data (W), write response (B), read address (AR), and read data (R). It combines separate read and write stub modules to provide a unified stub interface for testing AXI slave components.

## Module Parameters

### Skid Buffer Depths
- `DEPTH_AW`: Depth of the AW channel skid buffer (default: 2).
- `DEPTH_W`: Depth of the W channel skid buffer (default: 4).
- `DEPTH_B`: Depth of the B channel skid buffer (default: 2).
- `DEPTH_AR`: Depth of the AR channel skid buffer (default: 2).
- `DEPTH_R`: Depth of the R channel skid buffer (default: 4).

### AXI Parameters
- `AXI_ID_WIDTH`: Width of the AXI ID field (default: 8).
- `AXI_ADDR_WIDTH`: Width of the AXI address bus (default: 32).
- `AXI_DATA_WIDTH`: Width of the AXI data bus (default: 32).
- `AXI_USER_WIDTH`: Width of the AXI user field (default: 1).
- `AXI_WSTRB_WIDTH`: Width of the write strobe field, calculated as AXI_DATA_WIDTH / 8.

### Derived Parameters
- `AW`: Shorthand for AXI_ADDR_WIDTH.
- `DW`: Shorthand for AXI_DATA_WIDTH.
- `IW`: Shorthand for AXI_ID_WIDTH.
- `SW`: Shorthand for AXI_WSTRB_WIDTH.
- `UW`: Shorthand for AXI_USER_WIDTH.
- `AWSize`: Calculated size of the AW packet (IW+AW+8+3+2+1+4+3+4+4+UW).
- `WSize`: Calculated size of the W packet (DW+SW+1+UW).
- `BSize`: Calculated size of the B packet (IW+2+UW).
- `ARSize`: Calculated size of the AR packet (IW+AW+8+3+2+1+4+3+4+4+UW).
- `RSize`: Calculated size of the R packet (IW+DW+2+1+UW).

## Ports

### Global Signals
- `aclk`: System clock.
- `aresetn`: Active-low reset signal.

### Write Address Channel (AW)
- `s_axi_awid [AXI_ID_WIDTH-1:0]`: ID for write transactions.
- `s_axi_awaddr [AXI_ADDR_WIDTH-1:0]`: Write address.
- `s_axi_awlen [7:0]`: Burst length.
- `s_axi_awsize [2:0]`: Burst size.
- `s_axi_awburst [1:0]`: Burst type.
- `s_axi_awlock`: Lock type.
- `s_axi_awcache [3:0]`: Cache type.
- `s_axi_awprot [2:0]`: Protection type.
- `s_axi_awqos [3:0]`: Quality of service.
- `s_axi_awregion [3:0]`: Region identifier.
- `s_axi_awuser [AXI_USER_WIDTH-1:0]`: User signal.
- Handshake signals: `s_axi_awvalid`, `s_axi_awready`.

### Write Data Channel (W)
- `s_axi_wdata [AXI_DATA_WIDTH-1:0]`: Write data.
- `s_axi_wstrb [AXI_WSTRB_WIDTH-1:0]`: Write strobe.
- `s_axi_wlast`: Last transfer in a burst.
- `s_axi_wuser [AXI_USER_WIDTH-1:0]`: User signal.
- Handshake signals: `s_axi_wvalid`, `s_axi_wready`.

### Write Response Channel (B)
- `s_axi_bid [AXI_ID_WIDTH-1:0]`: ID for write response.
- `s_axi_bresp [1:0]`: Write response.
- `s_axi_buser [AXI_USER_WIDTH-1:0]`: User signal.
- Handshake signals: `s_axi_bvalid`, `s_axi_bready`.

### Read Address Channel (AR)
- `s_axi_arid [AXI_ID_WIDTH-1:0]`: ID for read transactions.
- `s_axi_araddr [AXI_ADDR_WIDTH-1:0]`: Read address.
- `s_axi_arlen [7:0]`: Burst length.
- `s_axi_arsize [2:0]`: Burst size.
- `s_axi_arburst [1:0]`: Burst type.
- `s_axi_arlock`: Lock type.
- `s_axi_arcache [3:0]`: Cache type.
- `s_axi_arprot [2:0]`: Protection type.
- `s_axi_arqos [3:0]`: Quality of service.
- `s_axi_arregion [3:0]`: Region identifier.
- `s_axi_aruser [AXI_USER_WIDTH-1:0]`: User signal.
- Handshake signals: `s_axi_arvalid`, `s_axi_arready`.

### Read Data Channel (R)
- `s_axi_rid [AXI_ID_WIDTH-1:0]`: ID for read response.
- `s_axi_rdata [AXI_DATA_WIDTH-1:0]`: Read data.
- `s_axi_rresp [1:0]`: Read response.
- `s_axi_rlast`: Last transfer in a burst.
- `s_axi_ruser [AXI_USER_WIDTH-1:0]`: User signal.
- Handshake signals: `s_axi_rvalid`, `s_axi_rready`.

### Stub Interface

#### AW Stub Interface
- `r_s_axi_awvalid`: Valid signal for AW packet to stub.
- `r_s_axi_awready`: Ready signal for AW packet from stub.
- `r_s_axi_aw_count [3:0]`: Count of AW packets in skid buffer.
- `r_s_axi_aw_pkt [AWSize-1:0]`: Packed AW channel signals.

#### W Stub Interface
- `r_s_axi_wvalid`: Valid signal for W packet to stub.
- `r_s_axi_wready`: Ready signal for W packet from stub.
- `r_s_axi_w_pkt [WSize-1:0]`: Packed W channel signals.

#### B Stub Interface
- `r_s_axi_bvalid`: Valid signal for B packet from stub.
- `r_s_axi_bready`: Ready signal for B packet to stub.
- `r_s_axi_b_pkt [BSize-1:0]`: Packed B channel signals.

#### AR Stub Interface
- `r_s_axi_arvalid`: Valid signal for AR packet to stub.
- `r_s_axi_arready`: Ready signal for AR packet from stub.
- `r_s_axi_ar_count [3:0]`: Count of AR packets in skid buffer.
- `r_s_axi_ar_pkt [ARSize-1:0]`: Packed AR channel signals.

#### R Stub Interface
- `r_s_axi_rvalid`: Valid signal for R packet from stub.
- `r_s_axi_rready`: Ready signal for R packet to stub.
- `r_s_axi_r_pkt [RSize-1:0]`: Packed R channel signals.

## Functionality

The `axi_slave_stub` module provides a comprehensive stub interface for AXI slave components with the following key functions:

### Integration of Read and Write Paths

The module integrates two sub-modules:
1. **axi_slave_wr_stub**: Handles the write path (AW, W, and B channels).
2. **axi_slave_rd_stub**: Handles the read path (AR and R channels).

Each sub-module operates independently but shares the same clock and reset domains.

### Channel Management

The module manages all five AXI channels:
1. **Write Address (AW)**: Handled by the write stub sub-module.
2. **Write Data (W)**: Handled by the write stub sub-module.
3. **Write Response (B)**: Handled by the write stub sub-module.
4. **Read Address (AR)**: Handled by the read stub sub-module.
5. **Read Data (R)**: Handled by the read stub sub-module.

### Signal Packetization

Each channel's signals are packetized to provide a clean and simplified interface to the test environment:
1. **AW Packet**: All AW channel signals combined into a single packet.
2. **W Packet**: All W channel signals combined into a single packet.
3. **B Packet**: All B channel signals combined into a single packet.
4. **AR Packet**: All AR channel signals combined into a single packet.
5. **R Packet**: All R channel signals combined into a single packet.

## Implementation Details

### Module Structure

The module instantiates two main sub-modules:

1. **axi_slave_wr_stub**:
   - Manages the write path (AW, W, and B channels).
   - Uses `gaxi_skid_buffer` for each channel with depths configured by DEPTH_AW, DEPTH_W, and DEPTH_B.
   - Handles signal packetization for all write-related channels.
   - The parameters use the naming convention DEPTH_* rather than SKID_DEPTH_*.

2. **axi_slave_rd_stub**:
   - Manages the read path (AR and R channels).
   - Uses `gaxi_skid_buffer` for each channel with depths configured by DEPTH_AR and DEPTH_R.
   - Handles signal packetization for all read-related channels.
   - The parameters use the naming convention DEPTH_* rather than SKID_DEPTH_*.

### Parameters Propagation

The module passes all relevant parameters to its sub-modules:
1. **Skid Buffer Depths**: DEPTH_* parameters are passed to the appropriate sub-module.
2. **AXI Parameters**: All AXI_* parameters are passed to both sub-modules.
3. **Derived Parameters**: All derived parameters (AW, DW, IW, SW, UW, *Size) are passed to the appropriate sub-module.

### Signal Connections

All AXI interface signals are passed directly to the appropriate sub-module:
1. **Global Signals**: Clock and reset are shared across all sub-modules.
2. **Write Path Signals**: All AW, W, and B channel signals are connected to the write stub sub-module.
3. **Read Path Signals**: All AR and R channel signals are connected to the read stub sub-module.
4. **Stub Interface Signals**: All stub interface signals are passed directly to/from the appropriate sub-module.

## Usage Considerations

1. **Buffer Depth Configuration**:
   - Adjust skid buffer depths based on expected traffic patterns.
   - Larger depths improve throughput but consume more resources.
   - Data channels (W and R) typically need deeper buffers than address and response channels.

2. **Parameter Consistency**:
   - Ensure consistent parameter values across all interconnected modules.
   - The AXI parameter values should match those of the AXI component being tested.

3. **Channel Coordination**:
   - Although the read and write paths operate independently, coordinated testing may be required for comprehensive verification.
   - Ensure proper sequencing of transactions across all channels.

4. **Integration with Test Environment**:
   - Connect the stub interface to the test infrastructure for generating and receiving transactions.
   - Use the count signals to monitor buffer utilization during testing.

5. **Skid Buffer Types**:
   - The module uses `gaxi_skid_buffer` for all channels, which provides additional features compared to standard skid buffers.
   - The gaxi_skid_buffer provides count information for monitoring buffer utilization.
   - Note that slave stubs use parameters named `DEPTH_*` that are passed to the `gaxi_skid_buffer` module parameter named `DEPTH`, while the o_rd_count and optional ow_count outputs provide buffer occupancy information.

## Integration Example

```systemverilog
axi_slave_stub #(
    .DEPTH_AW(4),                  // Deeper AW skid buffer for burst operations
    .DEPTH_W(8),                   // Deeper W skid buffer for burst operations
    .DEPTH_B(4),                   // Deeper B skid buffer for burst operations
    .DEPTH_AR(4),                  // Deeper AR skid buffer for burst operations
    .DEPTH_R(8),                   // Deeper R skid buffer for burst operations
    .AXI_DATA_WIDTH(64)            // 64-bit data bus
) i_axi_slave_stub (
    .aclk(system_clock),
    .aresetn(system_reset_n),
    
    // Connect AXI interface signals
    // ... (connection of all AXI signals) ...
    
    // Connect to test infrastructure
    // Write path
    .r_s_axi_awvalid(test_aw_valid),
    .r_s_axi_awready(test_aw_ready),
    .r_s_axi_aw_count(test_aw_count),
    .r_s_axi_aw_pkt(test_aw_pkt),
    
    .r_s_axi_wvalid(test_w_valid),
    .r_s_axi_wready(test_w_ready),
    .r_s_axi_w_pkt(test_w_pkt),
    
    .r_s_axi_bvalid(test_b_valid),
    .r_s_axi_bready(test_b_ready),
    .r_s_axi_b_pkt(test_b_pkt),
    
    // Read path
    .r_s_axi_arvalid(test_ar_valid),
    .r_s_axi_arready(test_ar_ready),
    .r_s_axi_ar_count(test_ar_count),
    .r_s_axi_ar_pkt(test_ar_pkt),
    
    .r_s_axi_rvalid(test_r_valid),
    .r_s_axi_rready(test_r_ready),
    .r_s_axi_r_pkt(test_r_pkt)
);
```

---

[Return to Index](index.md)

---