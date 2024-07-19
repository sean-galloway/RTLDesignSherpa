# axi_slave_rd_stub

## Module: `axi_slave_rd_stub`

The `axi_slave_rd_stub` module is a generic slave stub for sampling the read address and read data channels of an AXI4-compatible slave interface.

### Parameters

The module can be configured by the following parameters:

- `SKID_DEPTH_AR`: Skid buffer depth for the read address channel (AR).
- `SKID_DEPTH_R`: Skid buffer depth for the read data channel (R).
- `AXI_ID_WIDTH`: Width of the AXI ID signals.
- `AXI_ADDR_WIDTH`: Width of the AXI address bus.
- `AXI_DATA_WIDTH`: Width of the AXI data bus.
- `AXI_USER_WIDTH`: Width of the AXI user-defined signals.
- `AXI_WSTRB_WIDTH`: Width of the AXI write strobes, calculated as `AXI_DATA_WIDTH / 8`.

Shortened parameter names and additional internal calculations are also provided to simplify the interface (e.g., `AW`, `DW`, `IW`, `SW`, `UW`, `ARSize`, `RSize`).

### Ports

The module's interface includes standard AXI4 read address and data channel signals:

#### Read Address Channel (AR)

- `s_axi_arid` (Input): Read address ID. Width defined by `AXI_ID_WIDTH`.
- `s_axi_araddr` (Input): Read address. Width defined by `AXI_ADDR_WIDTH`.
- `s_axi_arlen` (Input): Burst length.
- `s_axi_arsize` (Input): Burst size.
- `s_axi_arburst` (Input): Burst type.
- `s_axi_arlock` (Input): Lock type.
- `s_axi_arcache` (Input): Cache type.
- `s_axi_arprot` (Input): Protection type.
- `s_axi_arqos` (Input): Quality of service.
- `s_axi_arregion` (Input): Region identifier.
- `s_axi_aruser` (Input): User-defined signal. Width defined by `AXI_USER_WIDTH`.
- `s_axi_arvalid` (Input): Read address valid.
- `s_axi_arready` (Output): Read address ready.

#### Read Data Channel (R)

- `s_axi_rid` (Output): Read data ID. Width defined by `AXI_ID_WIDTH`.
- `s_axi_rdata` (Output): Read data. Width defined by `AXI_DATA_WIDTH`.
- `s_axi_rresp` (Output): Read response.
- `s_axi_rlast` (Output): Read last.
- `s_axi_ruser` (Output): User-defined signal. Width defined by `AXI_USER_WIDTH`.
- `s_axi_rvalid` (Output): Read data valid.
- `s_axi_rready` (Input): Read data ready.

#### Stub Outputs/Inputs

- `r_s_axi_arvalid` (Output): Stub signal indicating the read address is valid.
- `r_s_axi_arready` (Input): Stub signal indicating the stub is ready for a read address.
- `r_s_axi_ar_count` (Output): Counter for the number of read addresses buffered.
- `r_s_axi_ar_pkt` (Output): Read address packet data. Width defined by `ARSize`.
  
- `r_s_axi_rvalid` (Input): Stub signal indicating the read data is valid.
- `r_s_axi_rready` (Output): Stub signal indicating the stub is ready for read data.
- `r_s_axi_r_pkt` (Input): Read data packet data. Width defined by `RSize`.

### Internal Functionality

The module internally leverages `axi_skid_buffer` instances to provide skid buffering capability. This buffering helps mitigate the effects of backpressure in a system by temporarily storing information during peak loads.

Each AXI channel (AR for the read address and R for read data) has a corresponding `axi_skid_buffer` instance with the following functionality:

#### Read Address Channel Skid Buffer

- Stores the read address transactions when the slave is not ready to accept them.
- Ensures that no transactions are lost due to backpressure.

#### Read Data Channel Skid Buffer

- Stores the read data transactions when the master is not ready to accept them.
- Guarantees reliable data transfer even when the system is under stress.

### Notes

The `axi_slave_rd_stub` is often used in testbenches for simulation purposes, where it can be inserted in place of a full AXI slave implementation to observe interaction on the AXI interface without the overhead of a complete design.

---

## Block Hierarchy and Links

- [AXI Slave Read Stub](axi_slave_rd_stub.md)
- [AXI Slave Write Stub](axi_slave_wr_stub.md)
- [AXI Slave Stub](axi_slave_stub.md)

---

[Return to Index](index.md)

---
