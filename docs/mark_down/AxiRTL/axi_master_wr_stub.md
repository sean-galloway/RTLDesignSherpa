# axi_master_wr_stub

This document provides details for the `axi_master_wr_stub` Verilog module located at: **rtl/axi/axi_master_wr_stub.sv**.

## Overview

The `axi_master_wr_stub` module acts as a placeholder for an AXI master write interface, integrating skid buffers to manage data flow. It is intended to be used in designs where an AXI master interface is necessary, but the actual master logic is not yet implemented or is abstracted away.

## Parameters

- `SKID_DEPTH_AW`: Skid buffer depth for the write address channel (AW).
- `SKID/pdf_DEPTH_W`: Skid buffer depth for the write data channel (W).
- `SKID_DEPTH_B`: Skid buffer depth for the write response channel (B).
- `AXI_ID_WIDTH`: Width of the AXI ID signal.
- `AXI_ADDR_WIDTH`: Width of the AXI address signals.
- `AXI_DATA_WIDTH`: Width of the AXI data and write data signals.
- `AXI_USER_WIDTH`: Width of the AXI user extension signals.
- `AXI_WSTRB_WIDTH`: Width of the write strobe (WSTRB) signal, calculated as AXI_DATA_WIDTH / 8.

Additional parameters such as `AW`, `DW`, `IW`, `SW`, `UW`, `AWSize`, `WSize`, and `BSize` are calculated based on the primary parameter widths to simplify interface vector sizes.

## Ports

### Stub Outputs/Inputs

Additional stub interfaces are provided to interact with the skid buffers and observe the states of the write channels. These include signals like `r_m_axi_awvalid`, `r_m_axi_awready`, `r_m_axi_aw_count`, and `r_m_axi_aw_pkt`.

## Internal Functionality

The `axi_master_wr_stub` module contains instances of `axi_skid_buffer` for the AW, W, and B channels, which are parametrized with corresponding skid depths and data widths. These skid buffers ensure reliable communication by temporarily storing data until the receiving component is ready to accept it.

Each `axi_skid_buffer` instance handles the synchronization of one of the AXI write channels, interfacing between the internal logic and external modules.

## Usage

This module should be instantiated in a design where AXI master write behavior is needed, providing a simple interface to manage write transactions. It can be used for simulation purposes or as a placeholder until the actual AXI master logic is developed.

This module does not require any specific command-line options, as it is intended to be synthesized or included in a larger Verilog/SystemVerilog design.

---

## Block Hierarchy and Links

- [AXI Master Read Stub](axi_master_rd_stub.md)
- [AXI Master Write Stub](axi_master_wr_stub.md)
- [AXI Master Stub](axi_master_stub.md)

---

[Return to Index](index.md)

---
