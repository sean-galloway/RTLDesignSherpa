# axi_slave_wr_stub

The Verilog module `axi_slave_wr_stub` acts as a generic slave stub for handling the write channels of an AXI interface. It includes skid buffers for write address (AW), write data (W), and write response (B) channels to deal with backpressure scenarios in an AXI transaction. Below is a breakdown of the module's parameters, ports, and functionality.

### Parameters

- `SKID_DEPTH_AW`: Depth of the skid buffer for the AW channel.
- `SKID_DEPTH_W`: Depth of the skid buffer for the W channel.
- `SKID_DEPTH_B`: Depth of the skid buffer for the B channel.
- `AXI_ID_WIDTH`: Width of the AXI ID signals.
- `AXI_ADDR_WIDTH`: Width of the AXI address signals.
- `AXI_DATA_WIDTH`: Width of the AXI data signals.
- `AXI_USER_WIDTH`: Width of the additional user signals in the AXI protocol.
- `AXI_WSTRB_WIDTH`: Width of the AXI write strobe signals (typically `AXI_DATA_WIDTH / 8`).

Derived parameters (`AW`, `DW`, `IW`, `SW`, `UW`, `AWSize`, `WSize`, and `BSize`) are based on these primary parameters to specify the sizes of various packet fields and other interface-level requirements.

### Ports

#### Global Clock and Reset:

- `aclk`: The system clock signal.
- `aresetn`: Active-low reset signal.

#### Write Address Channel (AW):

- `s_axi_aw*`: Input signals corresponding to the AXI write address channel inputs (e.g., `awid`, `awaddr`, `awlen`, etc.).
- `s_axi_awvalid`: Indicates the valid transfer of write address information.
- `s_axi_awready`: Indicates slave's readiness to accept write address information.

#### Write Data Channel (W):

- `s_axi_w*`: Input signals corresponding to the AXI write data channel inputs (e.g., `wdata`, `wstrb`, `wlast`, etc.).
- `s_axi_wvalid`: Indicates the valid transfer of write data.
- `s_axi_wready`: Indicates slave's readiness to accept write data.

#### Write Response Channel (B):

- `s_axi_b*`: Output signals corresponding to the AXI write response channel (e.g., `bid`, `bresp`, `buser`).
- `s_axi_bvalid`: Indicates the valid transfer of a write response.
- `s_axi_bready`: Indicates master's readiness to accept a write response.

#### Stub Outputs/Inputs:

- `r_s_axi_aw*`, `r_s_axi_w*`, and `r_s_axi_b*`: Signals for internal stub connectivity and reflection of the current state, primarily for simulation or debugging purposes.

### Functionality

The module instantiates skid buffers (`axi_skid_buffer`) for each of the write transaction phases (AW, W, B), which help in managing data transfers despite variations in data availability and consumer readiness. This mechanism ensures that no data is lost when the consumer is not ready to accept data (backpressure condition). The skid buffer parameters such as `SKID_DEPTH`, `DATA_WIDTH` are set based on the AXI configuration.

The `axi_slave_wr_stub` module is used in design simulations to mimic an AXI slave device without implementing the actual slave logic. It is useful for early verification and system-level testing to check an AXi master's behavior.

**Please Note:** The actual implementation of the `axi_skid_buffer` used within this module is not provided within the given context, and it is expected to be available in the design library or included via the commented out `include "axi_params.svh"` line.

---

## Block Hierarchy and Links

- [AXI Slave Read Stub](axi_slave_rd_stub.md)
- [AXI Slave Write Stub](axi_slave_wr_stub.md)
- [AXI Slave Stub](axi_slave_stub.md)

---

[Return to Index](index.md)

---
