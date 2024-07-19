# APB_SLAVE_STUB

The `apb_slave_stub` module is a stub that interfaces a generic peripheral bus (APB) with an Advanced eXtensible Interface (AXI) command/response protocol. The module uses skid buffers to handle backpressure and ensure smooth data transmission between the APB and AXI domains.

## Description

The `apb_slave_stub` acts as an APB slave device, accepting APB transactions, converting them into an AXI command packet format, and sending them onward. When a response packet is received, it is converted back to the APB response format.

## Parameters

- `SKID_DEPTH`: The depth of the skid buffer, implying how many outstanding transactions can be queued.
- `DATA_WIDTH`: Width of the data bus.
- `ADDR_WIDTH`: Width of the address bus.
- `STRB_WIDTH`: Width of the strobe signal.
- `CMD_PACKET_WIDTH`: Width of the command packet (combined width of address, data, strobe, and additional control bits).
- `RESP_PACKET_WIDTH`: Width of the response packet (combined width of data and response bit).

## Ports

- **Clock and Reset**
  - `aclk`: Clock signal.
  - `aresetn`: Reset signal, active low.

- **APB Interface**
  - `s_apb_PSEL`: APB select signal.
  - `s_apb_PENABLE`: APB enable signal.
  - `s_apb_PADDR`: APB address bus.
  - `s_apb_PWRITE`: APB write enable signal.
  - `s_apb_PWDATA`: APB write data bus.
  - `s_apb_PSTRB`: APB write strobe.
  - `s_apb_PPROT`: APB protection type.
  - `s_apb_PRDATA`: APB read data bus.
  - `s_apb_PSLVERR`: APB slave error signal.
  - `s_apb_PREADY`: APB ready signal.

- **Command Packet Interface**
  - `o_cmd_valid`: Output signal to indicate that the command packet is valid.
  - `i_cmd_ready`: Input signal to indicate that the downstream component is ready to accept the command packet.
  - `o_cmd_data`: Output command packet data.

- **Response Packet Interface**
  - `i_rsp_valid`: Input signal to indicate that the response packet is valid.
  - `o_rsp_ready`: Output signal to indicate that this module is ready to accept the response packet.
  - `i_rsp_data`: Input response packet data.

## Functional Description

- Skid buffers are used for both the command and response interfaces to manage flow control.
- An internal finite state machine (FSM) handles the states `IDLE` and `XFER_DATA`. In the `IDLE` state, the module waits for an active APB transaction. Upon receiving it, the transaction data is packed into a command packet format and sent out. The module then transitions to the `XRFER_DATA` state where it waits for the appropriate response from the AXI domain. Once received, it unpacks the response packet and presents the data on the APB interface.

## Code Usage

The following dependencies must be included to successfully use `apb_slave_stub`:

- Skid buffer module: `axi_skid_buffer`, which is instantiated twice inside `apb_slave_stub` for both command and response buffering.
- APB and AXI related constants and definitions.

This module does not have any specific command-line options for usage, as it is a hardware description meant for synthesis into an FPGA or ASIC.

---

[Return to Index](index.md)

---
