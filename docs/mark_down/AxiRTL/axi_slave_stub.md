# axi_slave_stub

The `axi_slave_stub` module is a generic AXI slave stub designed for use in an ASIC or FPGA design to model or stimulate an AXI slave. This does not perform any real data transactions but can be utilized for simulation purposes or as a placeholder during development. The module is parametrizable and incorporates skid buffers to handle back pressure in the AXI channels.

## Dependencies

This module may rely on AXI parameters defined in an external include file (`"axi_params.svh"`), although this line is commented out in the provided code.

## Parameters

- `SKID_DEPTH_*` : Define the depth of skid buffers for each channel.
- `AXI_ID_WIDTH` : Width of the ID fields.
- `AXi_ADDR_WIDTH` : Width of the address bus.
- `AXI_DATA_WIDTH` : Width of the data bus.
- `AXI_USER_WIDTH` : Width of the user-defined signals.
- `AXI_WSTRB_WIDTH` : Width of the write strobe signal, usually derived from the data width.
- Various calculated sizes for the AXI channel packets.

## Ports

- Global signals: `aclk` (clock) and `aresetn` (active-low reset).
- AXI Write Address Channel: Consists of several signals including `s_axi_awid`, `s_axi_awaddr`, `s_axi_awvalid`, etc., and `s_axi_awready`.
- AXI Write Data Channel: Consists of signals like `s_axi_wdata`, `s_axi_wstrb`, `s_axi_wvalid`, and `s_axi_wready`.
- AXI Write Response Channel: Consists of signals `s_axi_bid`, `s_axi_bresp`, `s_axi_bvalid`, and `s_axi_bready`.
- AXI Read Address Channel: Consists of signals such as `s_axi_arid`, `s_axi_araddr`, `s_axi_arvalid`, and `s_axi_arready`.
- AXI Read Data Channel: Consists of signals like `s_axi_rid`, `s_axi_rdata`, `s_axi_rvalid`, and `s_axi_rready`.
- Stub Outputs/Inputs: Additional signals to interface with the skid buffers and connect to other modules or stubs in the simulation environment.

## Design

This module instantiates two additional submodules:

- `axi_slave_wr_stub`: Handles the write address (`AW`), write data (`W`), and write response (`B`) channels.
- `axi_slave_rd_stub`: Handles the read address (`AR`) and read data (`R`) channels.

Each submodule has parameters passed down from `axi_slave_stub`, ensuring consistency across the AXI slave interface.

## Usage

The `axi_slave_stub` module is typically used in a verification environment where it is necessary to simulate the presence of an AXi slave without implementing the full functionality. Since it is a stub, the inner workings (like internal registers or memory) are not implemented, and actual data processing or storage does not occur.

---

To include this module in your project, ensure that you define the necessary parameters and connect the ports as per your requirements. For simulation purposes, you would typically drive the appropriate AXI signals and monitor the responses from this stub to validate your AXi master logic or to test the system integration.

In a real-world use case, this module would be replaced with a fully functional AXI slave module that can process incoming data and respond appropriately. This placeholder module ensures that the wider system can be developed and tested even if the final slave module is not yet available.

---

## Block Hierarchy and Links

- [AXI Slave Read Stub](axi_slave_rd_stub.md)
- [AXI Slave Write Stub](axi_slave_wr_stub.md)
- [AXI Slave Stub](axi_slave_stub.md)

---

[Return to Index](index.md)

---
