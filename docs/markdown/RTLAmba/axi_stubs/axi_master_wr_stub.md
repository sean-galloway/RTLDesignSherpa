# axi_master_wr_stub

This SystemVerilog module implements an AXI master write interface stub that handles the write address (AW), write data (W), and write response (B) channels of the AXI protocol. It is designed to provide a clean interface for testing AXI write operations by using skid buffers to manage data flow and packetizing signals.

## Module Parameters

### Skid Buffer Depths
- `SKID_DEPTH_AW`: Depth of the AW channel skid buffer (default: 2).
- `SKID_DEPTH_W`: Depth of the W channel skid buffer (default: 4).
- `SKID_DEPTH_B`: Depth of the B channel skid buffer (default: 2).

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

## Ports

### Global Signals
- `aclk`: System clock.
- `aresetn`: Active-low reset signal.

### Write Address Channel (AW)
- `m_axi_awid [AXI_ID_WIDTH-1:0]`: ID for write transactions.
- `m_axi_awaddr [AXI_ADDR_WIDTH-1:0]`: Write address.
- `m_axi_awlen [7:0]`: Burst length.
- `m_axi_awsize [2:0]`: Burst size.
- `m_axi_awburst [1:0]`: Burst type.
- `m_axi_awlock`: Lock type.
- `m_axi_awcache [3:0]`: Cache type.
- `m_axi_awprot [2:0]`: Protection type.
- `m_axi_awqos [3:0]`: Quality of service.
- `m_axi_awregion [3:0]`: Region identifier.
- `m_axi_awuser [AXI_USER_WIDTH-1:0]`: User signal.
- Handshake signals: `m_axi_awvalid`, `m_axi_awready`.

### Write Data Channel (W)
- `m_axi_wdata [AXI_DATA_WIDTH-1:0]`: Write data.
- `m_axi_wstrb [AXI_WSTRB_WIDTH-1:0]`: Write strobe.
- `m_axi_wlast`: Last transfer in a burst.
- `m_axi_wuser [AXI_USER_WIDTH-1:0]`: User signal.
- Handshake signals: `m_axi_wvalid`, `m_axi_wready`.

### Write Response Channel (B)
- `m_axi_bid [AXI_ID_WIDTH-1:0]`: ID for write response.
- `m_axi_bresp [1:0]`: Write response.
- `m_axi_buser [AXI_USER_WIDTH-1:0]`: User signal.
- Handshake signals: `m_axi_bvalid`, `m_axi_bready`.

### Stub Interface

#### AW Stub Interface
- `r_m_axi_awvalid`: Valid signal for AW packet from stub.
- `r_m_axi_awready`: Ready signal for AW packet to stub.
- `r_m_axi_aw_count [2:0]`: Count of AW packets in skid buffer.
- `r_m_axi_aw_pkt [AWSize-1:0]`: Packed AW channel signals.

#### W Stub Interface
- `r_m_axi_wvalid`: Valid signal for W packet from stub.
- `r_m_axi_wready`: Ready signal for W packet to stub.
- `r_m_axi_w_pkt [WSize-1:0]`: Packed W channel signals.

#### B Stub Interface
- `r_m_axi_bvalid`: Valid signal for B packet to stub.
- `r_m_axi_bready`: Ready signal for B packet from stub.
- `r_m_axi_b_pkt [BSize-1:0]`: Packed B channel signals.

## Functionality

The `axi_master_wr_stub` module provides a streamlined interface for AXI write operations with the following key functions:

### AW Channel Management

1. **Signal Packetization**: Takes a packed AW channel packet (`r_m_axi_aw_pkt`) and unpacks it into individual AXI signals.
2. **Flow Control**: Manages handshaking between the AXI interface and the stub.
3. **Buffering**: Uses a skid buffer to handle timing variations and improve throughput.

### W Channel Management

1. **Signal Packetization**: Takes a packed W channel packet (`r_m_axi_w_pkt`) and unpacks it into individual AXI signals.
2. **Flow Control**: Manages handshaking between the AXI interface and the stub.
3. **Buffering**: Uses a skid buffer to handle timing variations and improve throughput.

### B Channel Management

1. **Signal Packetization**: Combines all B channel signals into a single packet (`r_m_axi_b_pkt`).
2. **Flow Control**: Manages handshaking between the AXI interface and the stub.
3. **Buffering**: Uses a skid buffer to handle timing variations and improve throughput.

## Implementation Details

### Module Structure

The module consists of three main components:

1. **AW Channel Skid Buffer**:
   - Uses `gaxi_skid_buffer` with depth parameter `SKID_DEPTH_AW`
   - Handles AW channel signals from the stub to the AXI interface.
   - Unpacks the data packet into individual AXI signals.
   - Provides buffering capabilities configured by SKID_DEPTH_AW.
   - The output signal `r_m_axi_aw_count` indicates the number of transactions in the AW buffer.

2. **W Channel Skid Buffer**:
   - Uses `gaxi_skid_buffer` with depth parameter `SKID_DEPTH_W`
   - Handles W channel signals from the stub to the AXI interface.
   - Unpacks the data packet into individual AXI signals.
   - Provides buffering capabilities configured by SKID_DEPTH_W.

3. **B Channel Skid Buffer**:
   - Uses `gaxi_skid_buffer` with depth parameter `SKID_DEPTH_B`
   - Handles B channel signals from the AXI interface to the stub.
   - Packs multiple AXI signals into a single data packet.
   - Provides buffering capabilities configured by SKID_DEPTH_B.

### Signal Connections

Each skid buffer instance connects to the relevant AXI channel signals and provides the necessary handshaking and buffering:

1. **inst_aw_phase**: Connects the packed r_m_axi_aw_pkt signal to all AW channel signals.
2. **inst_w_phase**: Connects the packed r_m_axi_w_pkt signal to all W channel signals.
3. **inst_b_phase**: Connects all B channel signals to the packed r_m_axi_b_pkt signal.

## Usage Considerations

1. **Buffer Depth Configuration**:
   - Adjust skid buffer depths based on expected traffic patterns.
   - Larger depths improve throughput but consume more resources.
   - The W channel typically needs a deeper buffer (default: 4) than the AW and B channels (default: 2).

2. **Packet Format**:
   - The packet format for AW, W, and B channels is determined by the order of signals in the concatenation.
   - Ensure the packing and unpacking logic matches between interconnected modules.

3. **Channel Coordination**:
   - The AW, W, and B channels must be coordinated for proper operation.
   - Ensure proper sequencing of transactions across channels.

4. **Integration with Test Environment**:
   - This stub is designed to be used in test environments for AXI masters.
   - Connect the stub interface to the test infrastructure for generating and receiving transactions.

## Integration Example

```systemverilog
axi_master_wr_stub #(
    .SKID_DEPTH_AW(4),             // Deeper AW skid buffer for burst operations
    .SKID_DEPTH_W(8),              // Deeper W skid buffer for burst operations
    .SKID_DEPTH_B(4),              // Deeper B skid buffer for burst operations
    .AXI_DATA_WIDTH(64)            // 64-bit data bus
) i_axi_master_wr_stub (
    .aclk(system_clock),
    .aresetn(system_reset_n),
    
    // Connect AXI interface signals
    // ... (connection of all AXI signals) ...
    
    // Connect to test infrastructure
    .r_m_axi_awvalid(test_aw_valid),
    .r_m_axi_awready(test_aw_ready),
    .r_m_axi_aw_count(test_aw_count),
    .r_m_axi_aw_pkt(test_aw_pkt),
    
    .r_m_axi_wvalid(test_w_valid),
    .r_m_axi_wready(test_w_ready),
    .r_m_axi_w_pkt(test_w_pkt),
    
    .r_m_axi_bvalid(test_b_valid),
    .r_m_axi_bready(test_b_ready),
    .r_m_axi_b_pkt(test_b_pkt)
);
```

---

[Return to Index](index.md)

---