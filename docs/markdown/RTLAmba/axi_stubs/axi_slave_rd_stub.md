# axi_slave_rd_stub

This SystemVerilog module implements an AXI slave read interface stub that handles the read address (AR) and read data (R) channels of the AXI protocol. It is designed to provide a clean interface for testing AXI slave read operations by using skid buffers to manage data flow and packetizing signals.

## Module Parameters

### Skid Buffer Depths
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
- `ARSize`: Calculated size of the AR packet (IW+AW+8+3+2+1+4+3+4+4+UW).
- `RSize`: Calculated size of the R packet (IW+DW+2+1+UW).

## Ports

### Global Signals
- `aclk`: System clock.
- `aresetn`: Active-low reset signal.

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

The `axi_slave_rd_stub` module provides a streamlined interface for AXI slave read operations with the following key functions:

### AR Channel Management

1. **Signal Packetization**: Combines all AR channel signals into a single packet (`r_s_axi_ar_pkt`).
2. **Flow Control**: Manages handshaking between the AXI interface and the stub.
3. **Buffering**: Uses a skid buffer to handle timing variations and improve throughput.
4. **Count Monitoring**: Provides a count of AR transactions in the buffer.

### R Channel Management

1. **Signal Packetization**: Takes a packed R channel signal (`r_s_axi_r_pkt`) and unpacks it into individual AXI signals.
2. **Flow Control**: Manages handshaking between the AXI interface and the stub.
3. **Buffering**: Uses a skid buffer to handle timing variations and improve throughput.

## Implementation Details

### Module Structure

The module consists of two main components:

1. **AR Channel Skid Buffer**:
   - Uses `gaxi_skid_buffer` with depth parameter `DEPTH_AR`
   - Handles AR channel signals from the AXI interface to the stub.
   - Packs multiple AXI signals into a single data packet.
   - Provides buffering capabilities configured by DEPTH_AR.
   - The output signal `r_s_axi_ar_count` indicates the number of transactions in the AR buffer.
   - The `ow_count` output is available but not connected externally.

2. **R Channel Skid Buffer**:
   - Uses `gaxi_skid_buffer` with depth parameter `DEPTH_R`
   - Handles R channel signals from the stub to the AXI interface.
   - Unpacks the data packet into individual AXI signals.
   - Provides buffering capabilities configured by DEPTH_R.
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

1. **inst_ar_phase**: Connects all AR channel signals to the packed r_s_axi_ar_pkt signal.
2. **inst_r_phase**: Connects the packed r_s_axi_r_pkt signal to all R channel signals.

## Usage Considerations

1. **Buffer Depth Configuration**:
   - Adjust DEPTH_AR and DEPTH_R based on expected traffic patterns.
   - Larger depths improve throughput but consume more resources.
   - The R channel typically needs a deeper buffer (default: 4) than the AR channel (default: 2).

2. **Packet Format**:
   - The packet format for AR and R channels is determined by the order of signals in the concatenation.
   - Ensure the packing and unpacking logic matches between interconnected modules.

3. **Integration with Test Environment**:
   - This stub is designed to be used in test environments for AXI slaves.
   - Connect the stub interface to the test infrastructure for generating and receiving transactions.
   - Use the count signals to monitor buffer utilization during testing.

4. **AXI Signal Ordering**:
   - The order of signals in the packet concatenation is critical for proper operation.
   - The AR packet format is `{s_axi_arid, s_axi_araddr, s_axi_arlen, ...}`.
   - The R packet format is `{s_axi_rid, s_axi_rdata, s_axi_rresp, s_axi_rlast, s_axi_ruser}`.

## Integration Example

```systemverilog
axi_slave_rd_stub #(
    .DEPTH_AR(4),                  // Deeper AR skid buffer for burst operations
    .DEPTH_R(8),                   // Deeper R skid buffer for burst operations
    .AXI_DATA_WIDTH(64)            // 64-bit data bus
) i_axi_slave_rd_stub (
    .aclk(system_clock),
    .aresetn(system_reset_n),
    
    // Connect AXI interface signals
    // ... (connection of all AXI signals) ...
    
    // Connect to test infrastructure
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