# axi_master_stub

The `axi_master_stub` is a module that stubs an AXI master interface. It is designed to work with the AXI protocol used for high-performance memory-mapped communication.

## Parameters

The module has various parameters that can be configured:

- `SKID_DEPTH_AW`, `SKID_DEPTH_W`, `SKID_DEPTH_B`, `SKID_DEPTH_AR`, `SKID_DEPTH_R`: These are the skid buffer depths for the various AXI channels.
- `AXI_ID_WIDTH`: The width of the ID signal, typically used to uniquely identify outstanding transactions.
- `AXI_ADDR_WIDTH`: The number of bits used for addressing.
- `AXI_DATA_WIDTH`: Data bus width. It is common to have 32, 64, or 128 bits.
- `AXI_USER_WIDTH`: Width of the user-defined signal in the AXI protocol.
- `AXI_WSTRB_WIDTH`: Width of the write strobe, determining which bytes of data are active.

There are also several calculated parameters based on the AXI configurations, such as `AWSize`, `WSize`, `BSize`, `ARSize`, and `RSize`, which define the sizes of various internal packet structures.

### Ports

The `axi_master_stub` consists of standard AXI interface ports:

- Global Clock (`aclk`) and Reset (`aresetn`)
- Write Address Channel ports (`m_axi_awid`, `m_axi_awaddr`, `m_axi_awlen`, etc.)
- Write Data Channel ports (`m_axi_wdata`, `m_axi_wstrb`, `m_axi_wlast`, etc.)
- Write Response Channel ports (`m_axi_bid`, `m_axi_bresp`, `m_axi_buser`, etc.)
- Read Address Channel ports (`m_axi_arid`, `m_axi_araddr`, `m_axi_arlen`, etc.)
- Read Data Channel ports (`m_axi_rid`, `m_axi_rdata`, `m_axi_rresp`, etc.)

It also includes additional ports for stub inputs/outputs related to each of the AXI channels, like `r_m_axi_awvalid` and `r_m_axi_awready` for the Write Address Channel.

### Instantiations

The `axi_master_stub` module instantiates two submodules, `axi_master_wr_stub` and `axi_master_rd_stub`, which handle the write and read channel logic respectively, and are parameterized with the same configurations passed to the `axi_master_stub`.

### Functionality

The `axi_master_stub` serves as a placeholder for an actual AXI master in a simulation or testing environment, where the full implementation of an AXI master is not needed or is under development.

The module doesn't include the actual logic for handling AXI transactions but forwards signals between the interfaces and submodules. This allows simulation of AXI signal behaviors and interactions with slave devices, making it a valuable tool for early testing of AXI-compliant hardware without requiring a fully implemented AXI master. 

The stub can be extended to include additional logic for specific testing scenarios, such as injecting errors, monitoring transactions, or providing feedback for coverage analysis.

This module's primary use cases are in testing and simulation environments where detailed modeling of actual AXI master behavior is not necessary or is being abstracted for higher-level verification tasks.

---

## Block Hierarchy and Links

- [AXI Master Read Stub](axi_master_rd_stub.md)
- [AXI Master Write Stub](axi_master_wr_stub.md)
- [AXI Master Stub](axi_master_stub.md)

---

[Return to Index](index.md)

---
