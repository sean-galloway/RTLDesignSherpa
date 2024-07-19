# axi2apb_shim

The `axi2apb_shim` module is a Verilog system interface that translates AXI transactions into APB transactions. This module serves as a bridge between AXI masters and APB slaves, allowing integration of APB-compliant peripherals into an AXI-based system.

## Parameters

- `SKID_DEPTH_AW`: Skid buffer depth for the AXI write address channel.
- `SKID_DEPTH_W`: Skid buffer depth for the AXI write data channel.
- `SKID_DEPTH_B`: Skid buffer depth for the AXI write response channel.
- `SKID_DEPTH_AR`: Skid buffer depth for the AXI read address channel.
- `SKID_DEPTH_R`: Skid buffer depth for the AXI read data channel.
- `SIDE_DEPTH`: Number of outstanding transactions that can be buffered on the AXI side.
- `APB_CMD_DEPTH`: Command queue depth for the APB command channel.
- `APBg_RSP_DEPTH`: Response queue depth for the APB response channel.
- `AXI_ID_WIDTH`: Width of the AXI ID signals.
- `AXI_ADDR_WIDTH`: Width of the AXI address bus.
- `AXI_DATA_WIDTH`: Width of the AXI data bus.
- `AXI_USER_WIDTH`: Width of the AXI user signal.
- `APB_ADDR_WIDTH`: Width of the APB address bus.
- `APB_DATA_WIDTH`: Width of the APB data bus.
- `AXI_WSTRB_WIDTH`: Width of the AXI write strobe signal.
- `APB_WSTRB_WIDTH`: Width of the APB write strobe signal.

Additional internal parameter calculations are used to define the size of various internal signals based on the widths of the input/output ports and parameters.

## Ports

### AXI Slave Interface

- Clock (`aclk`) and reset (`aresetn`) signals.
- AXI write address, data, and response channels: `s_axi_aw*`, `s_axi_w*`, and `s_axi_b*`.
- AXI read address and data channels: `s_axi_ar*` and `s_axi_r*`.

### APB Master Interface

- APB control signals: `m_apb_PSEL`, `m_apb_PENABLE`, `m_apb_PWRITE`.
- APB address and data signals: `m_apb_PADDR` and `m_apb_PWDATA`.
- APB response signals: `m_apb_PRDATA`, `m_apb_PREADY`, `m_apb_PSLVERR`.

## Functionality

The `axi2apb_shim` module instantiates the following components:

- `axi_slave_stub`: Skid buffer and control logic for AXI signals.
- `axi2apb_convert`: Logic for converting AXI protocol transactions to APB protocol transactions.
- `apb_master_stub`: Logic to drive the APB interface based on converted transactions.

The module interfaces with an AXI master, buffers incoming AXI transactions, translates them to the APB protocol, and then drives the corresponding APB transactions on the output APB master interface.

## Notes

- This module does not handle the actual APB transactions but sets up the protocol conversion to be handled by the instantiated submodules.
- Users must instantiate this module with the correct parameters matching their system's AXI and APB configurations.

This module is defined in the file `rtl/axi/axi2apb_shim.sv`.

## Block Hierarchy and Links

- [AXI to APB Convert](axi2apb_convert.md)
- [AXI to APB Shim](axi2apb_shim.md)

---

[Return to Index](index.md)

---
