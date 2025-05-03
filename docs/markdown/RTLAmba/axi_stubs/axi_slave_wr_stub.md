# axi_slave_wr_stub

This SystemVerilog module implements an AXI slave write interface stub that handles the write address (AW), write data (W), and write response (B) channels of the AXI protocol. It is designed to provide a clean interface for testing AXI slave write operations by using skid buffers to manage data flow and packetizing signals.

## Module Parameters

### Skid Buffer Depths
- `DEPTH_AW`: Depth of the AW channel skid buffer (default: 2).
- `DEPTH_W`: Depth of the W channel skid buffer (default: 4).
- `DEPTH_B`: Depth of the B channel skid buffer (default: 2).

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

## Functionality

The `axi_slave_wr_stub` module provides a streamlined interface for AXI slave write operations with the following key functions:

### AW Channel Management

1. **Signal Packetization**: Combines all AW channel signals into a single packet (`r_s_axi_aw_pkt`).
2. **Flow Control**: Manages handshaking between the AXI interface and the stub.
3. **Buffering**: Uses a skid buffer to handle timing variations and improve throughput.
4. **Count Monitoring**: Provides a count of AW transactions in the buffer.

### W Channel Management

1. **Signal Packetization**: Combines all W channel signals into a single packet (`r_s_axi_w_pkt`).
2. **Flow Control**: Manages handshaking between the AXI interface and the stub.
3. **Buffering**: Uses a skid buffer to handle timing variations and improve throughput.
4. **Count Monitoring**: Provides a count of W transactions in the buffer (not exposed in interface).

### B Channel Management

1. **Signal Packetization**: Takes a packed B channel signal (`r_s_axi_b_pkt`) and unpacks it into individual AXI signals.
2. **Flow Control**: Manages handshaking between the AXI interface and the stub.
3. **Buffering**: Uses a skid buffer to handle timing variations and improve throughput.
4. **Count Monitoring**: Provides a count of B transactions in the buffer (not exposed in interface).

## Implementation Details

### Module Structure

The module consists of three main components:

1. **AW Channel Skid Buffer**:
   - Uses `gaxi_skid_buffer` with depth parameter `DEPTH_AW`
   - Handles AW channel signals from the AXI interface to the stub.
   - Packs multiple AXI signals into a single data packet.
   - Provides buffering capabilities configured by DEPTH_AW.
   - The output signal `r_s_axi_aw_count` indicates the number of transactions in the AW buffer.
   - The `ow_count` output is available but not connected externally.

2. **W Channel Skid Buffer**:
   - Uses `gaxi_skid_buffer` with depth parameter `DEPTH_W`
   - Handles W channel signals from the AXI interface to the stub.
   - Packs multiple AXI signals into a single data packet.
   - Provides buffering capabilities configured by DEPTH_W.
   - The buffer count outputs `o_rd_count` and `ow_count` are available but not connected externally.

3. **B Channel Skid Buffer**:
   - Uses `gaxi_skid_buffer` with depth parameter `DEPTH_B`
   - Handles B channel signals from the stub to the AXI interface.
   - Unpacks the data packet into individual AXI signals.
   - Provides buffering capabilities configured by DEPTH_B.
   - The buffer count outputs `o_rd_count` and `ow_count` are available but not connected externally.

### Skid Buffer Implementation

The module uses a specialized skid buffer implementation (`gaxi_skid_buffer`) that provides:
1. **Flow Control**: Manages handshaking between input and output interfaces.
2. **Data Buffering**: Stores data for later processing.
3. **Count Information**: Tracks the number of transactions in the buffer.
4. **Clock Domain Support**: Operates within the AXI clock domain.
5. **Parameter Name**: The parameter for buffer depth in gaxi_skid_buffer is named `DEPTH` in this module.

### Signal Connections

Each skid buffer instance connects to the relevant AXI channel signals and provides the necessary handshaking and buffering:

1. **inst_aw_phase**: Connects all AW channel signals to the packed r_s_axi_aw_pkt signal.
2. **inst_w_phase**: Connects all W channel signals to the packed r_s_axi_w_pkt signal.
3. **inst_b_phase**: Connects the packed r_s_axi_b_pkt signal to all B channel signals.

## Usage Considerations

1. **Buffer Depth Configuration**:
   - Adjust skid buffer depths based on expected traffic patterns.
   - Larger depths improve throughput but consume more resources.
   - The W channel typically needs a deeper buffer (default: 4) than the AW and B channels (default: 2).

2. **Packet Format**:
   - The packet format for AW, W, and B channels is determined by the order of signals in the concatenation.
   - Ensure the packing and unpacking logic matches between interconnected modules.

3. **Integration with Test Environment**:
   - This stub is designed to be used in test environments for AXI slaves.
   - Connect the stub interface to the test infrastructure for generating and receiving transactions.
   - Use the count signals to monitor buffer utilization during testing.

4. **AXI Signal Ordering**:
   - The order of signals in the packet concatenation is critical for proper operation.
   - The AW packet format is `{s_axi_awid, s_axi_awaddr, s_axi_awlen, ...}`.
   - The W packet format is `{s_axi_wdata, s_axi_wstrb, s_axi_wlast, s_axi_wuser}`.
   - The B packet format is `{s_axi_bid, s_axi_bresp, s_axi_buser}`.

5. **Channel Coordination**:
   - The AW, W, and B channels must be coordinated for proper operation.
   - Ensure proper sequencing of transactions across channels according to AXI protocol requirements.

## Integration Example

```systemverilog
axi_slave_wr_stub #(
    .DEPTH_AW(4),                  // Deeper AW skid buffer for burst operations
    .DEPTH_W(8),                   // Deeper W skid buffer for burst operations
    .DEPTH_B(4),                   // Deeper B skid buffer for burst operations
    .AXI_DATA_WIDTH(64)            // 64-bit data bus
) i_axi_slave_wr_stub (
    .aclk(system_clock),
    .aresetn(system_reset_n),
    
    // Connect AXI interface signals
    // ... (connection of all AXI signals) ...
    
    // Connect to test infrastructure
    .r_s_axi_awvalid(test_aw_valid),
    .r_s_axi_awready(test_aw_ready),
    .r_s_axi_aw_count(test_aw_count),
    .r_s_axi_aw_pkt(test_aw_pkt),
    
    .r_s_axi_wvalid(test_w_valid),
    .r_s_axi_wready(test_w_ready),
    .r_s_axi_w_pkt(test_w_pkt),
    
    .r_s_axi_bvalid(test_b_valid),
    .r_s_axi_bready(test_b_ready),
    .r_s_axi_b_pkt(test_b_pkt)
);
```

---

[Return to Index](index.md)

---