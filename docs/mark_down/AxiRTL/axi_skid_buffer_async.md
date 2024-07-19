# axi_skid_buffer_async

This markdown documentation describes the `axi_skid_buffer_async` module, which serves as an AXI skid buffer that ensures safe data transfer between asynchronous clock domains, specifically targeting AXI write and read channels. The module uses skid buffer and asynchronous FIFO techniques to accommodate the flow control and buffering required for axi transactions.

## Module Path

rtl/axi/axi_skid_buffer_async.sv

## Inputs/Outputs

- Global Clock and Reset:
  - `i_axi_wr_aclk`: Clock signal for the AXI write channel.
  - `i_axi_wr_aresetn`: Active low reset for the AXI write channel.
  - `i_axi_rd_aclk`: Clock signal for the AXI read channel.
  - `i_axi_rd_aresetn`: Active low reset for the AXI read channel.

- Input Side:
  - `i_wr_valid`: Write valid signal from AXI master.
  - `o_wr_ready`: Write ready signal to AXI master.
  - `i_wr_data`: Data to be written, coming from the master, of width `DW` (Data Width).

- Output Side:
  - `o_rd_valid`: Read valid signal to AXI slave.
  - `i_rd_ready`: Read ready signal from AXI slave.
  - `o_rd_data`: Data to be read by the slave, of width `DW` (Data Width).

## Internal Functionality

Internally, this module instantiates two primary sub-modules:

1. `axi_skid_buffer`: This handles the initial capture of data and control signals on the AXI write clock domain.
2. `axi_fifo_async`: This asynchronous FIFO handles the transfer of data from the write clock domain to the read clock domain, utilizing a configurable depth and also managing almost full/empty conditions.

## Parameters

- `DATA_WIDTH`: Width of the data to be buffered (default: 32).
- `DEPTH`: Depth of the asynchronous FIFO (default: 2).
- `N_FLOP_CROSS`: Number of flip-flops used in the clock domain crossing (default: 2).
- `INSTANCE_NAME`: Unique identification for this instance (default: "DEADF1F0").
- `DW`: Short alias for `DATA_WIDTH`.

This module should be incorporated into a design with caution, and clock domain crossing (CDC) must be verified to ensure that metastability and data coherency are managed correctly.
  
## External Dependencies

To use `axi_skid_buffer_async`, the codebase must include definitions for the `axi_skid_buffer` and `axi_fifo_async` modules which are instantiated within. Parameters and port mappings for these instantiated modules must align with their respective module definitions.

## Conclusion

The `axi_skid_buffer_async` module is crucial for synchronizing data transfers across different clock domains in an AXI interface. By detailing its interface, parameters, and integrated sub-modules, designers can effectively integrate this module into their AXI-based systems.

---

[Return to Index](index.md)

---
