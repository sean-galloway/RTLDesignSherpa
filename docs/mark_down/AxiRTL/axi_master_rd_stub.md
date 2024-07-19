# axi_master_rd_stub

The `axi_master_rd_stub` module is a read channel stub for an AXI master interface, which utilizes skid-buffers to interface with the actual read address (`AR`) and read data (`R`) channels. Skid-buffers help alleviate back-pressure issues in pipelined designs. Below is the detailed documentation of the module:

### Parameters

- `SKID_DEPTH_AR`: Skid buffer depth for the read address channel, defaulting to 2.
- `SKID_DEPTH_R`: Skid buffer depth for the read data channel, defaulting to 4.
- `AXI_ID_WIDTH`: Width of the AXI ID signal, defaulting to 8 bits.
- `AXI_ADDR_WIDTH`: Width of the AXI address, defaulting to 32 bits.
- `AXI_DATA_WIDTH`: Width of the AXI data, defaulting to 32 bits.
- `AXI_USER_WIDTH`: Width of the AXI user signal, defaulting to 1 bit.
- `AXI_WSTRB_WIDTH`: The width of the write strobe signal, typically derived as `AXI_DATA_WIDTH / 8`.
- Additional calculated parameter width definitions used internally.

### Ports

#### Global Clock and Reset

- `aclk`: The global clock signal.
- `aresetn`: Active-low reset signal.

#### Read Address Channel (AR)

- `m_axi_ar*`: Master-side AR channel interface signals (id, addr, len, size, burst, lock, cache, prot, qos, region, user, valid).
- `m_axi_arready`: Read address channel ready signal.

#### Read Data Channel (R)

- `m_axi_r*`: Master-side R channel interface signals (id, data, resp, last, user, valid).
- `m_axi_rready`: Read data channel ready signal.

#### Stub Outputs/Inputs

- `r_m_axi_ar*`: Stub-side signals mirroring the master AR channel interface, along with the counter and packet signals.
- `r_m_axf_r*`: Stub-side signals mirroring the master R channel interface, including packet signals.

### Internal Functionality

- Two instances of `axi_skid_buffer`: one for the read address channel (`ARSize` wide data) and one for the read data channel (`RSize` wide data).
- The skid buffers help in storing the data temporarily when the master is not ready to accept new data, thus preventing data loss and providing flow control.

### Usage

The `axi_master_rd_stub` module is used to interface with AXI master read channels where the actual logic might not be present or where a stub is needed for simulation purposes. The module can also act as a placeholder during the development stage of an AXI master interface.

To use this module, instantiate it in your Verilog/SystemVerilog design and connect its ports to the respective master interface signals and the stub logic as needed.

---

## Block Hierarchy and Links

- [AXI Master Read Stub](axi_master_rd_stub.md)
- [AXI Master Write Stub](axi_master_wr_stub.md)
- [AXI Master Stub](axi_master_stub.md)

---

[Return to Index](index.md)

---
