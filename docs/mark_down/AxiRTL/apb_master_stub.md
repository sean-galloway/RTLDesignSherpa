# APB Master Stub

The `apb_master_stub` module is an APB (Advanced Peripheral Bus) master protocol stub that interfaces with APB slave devices. This module is responsible for sending commands and reading responses between the APB interface and its master.

## Parameters

- `CMD_DEPTH`: Depth of the command FIFO queue.
- `RSP_DEPTH`: Depth of the response FIFO queue.
- `DATA_WIDTH`: Bit width of the data bus.
- `ADDR_WIDTH`: Bit width of the address bus.
- `STRB_WIDTH`: Bit width of the strobe signal, typically `DATA_WIDTH / 8`.
- `CMD_PACKET_WIDTH`: Total bit width of the command packet.
- `RESP_PACKET_WIDTH`: Total bit width of the response packet.

These parameters are customizable to fit the user's needs and can be changed during module instantiation.

## Ports

### Clock and Reset

- `aclk`: Clock input for the module.
- `aresetn`: Active-low asynchronous reset signal for the module.

### APB interface signals

- `m_apb_PSEL`: APB Selection signal, active high.
- `m_apb_PENABLE`: APB Enable signal, active high to indicate the second and subsequent cycles of an APB transfer.
- `m_apb_PADDR`: APB Address bus.
- `m_apb_PWRITE`: APB Write control signal, active high indicates write operation.
- `m_apb_PWDATA`: APB Write data bus.
- `m_apb_PSTRB`: Strobe signal for byte enable.
- `m_apb_PPROT`: Protection control signal.
- `m_apb_PRDATA`: APB Read data bus.
- `m_apb_PSLVERR`: Error indicator from the slave.
- `m_apb_PREADY`: Ready signal from the slave, indicating completion of an APB transfer.

### Command packet signals

- `i_cmd_valid`: Input signal indicating the command packet is valid.
- `o_cmd_ready`: Output signal indicating the APB master stub is ready to accept a command.
- `i_cmd_data`: Command data input comprising of address, data, strobe, protection, write control, first and last markers.

### Response packet signals

- `o_rsp_valid`: Output signal indicating the response packet is valid and available.
- `i_rsp_ready`: Input signal indicating the recipient of the response data is ready to receive it.
- `o_rsp_data`: Output data for the response packet containing the read data, error indicator, first, and last markers.

## Internal Logic

- Command packets are read into a FIFO buffer and processed by the APB protocol state machine.
- The state machine manages the APB transfers according to the commands.
- Read responses from APB slaves are also buffered in a FIFO to synchronize with the master's receiving interface.
- The module includes an APB FSM (finite state machine) with two states: `IDLE` and `ACTIVE`.
- `axi_skid_buffer` is used to maintain the pipeline flow control.

## Usage

This stub can be instantiated in a testbench or a synthesis top module to simulate or handle APB transactions without the need for a full APB master implementation. It is useful for initial design verification or when the full APB master interface is not required for the specific use case.

## Conclusion

The `apb_master_stub` module offers a simplified interface to conduct APB transactions with customizable parameters to match a variety of APB slaves. It is an essential component for a system that requires interaction with the APB bus protocol without a complex master implementation.

---

[Return to Index](index.md)

---
