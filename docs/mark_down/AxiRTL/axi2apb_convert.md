# axi2apb_convert

The `axi2apb_convert` module performs conversion between the AXI and APB protocols, serving as a bridge that allows AXI master devices to communicate with APB slave peripherals. The module handles attribute remapping, handshake synchronization, and burst splitting to ensure compatibility between the two interfaces.

## Module Parameters

- `SIDE_DEPTH`: Depth of side FIFO.
- `AXI_ID_WIDTH`: Width of the AXI ID.
- `AXI_ADDR_WIDTH`: Width of the AXI address.
- `AXI_DATA_WIDTH`: Width of the AXI data bus.
- `AXI_USER_WIDTH`: Width of the AXI user bus.
- `APB_ADDR_WIDTH`: Width of the APB address.
- `APB_DATA_WIDTH`: Width of the APB data bus.
- `AXI_WSTRB_WIDTH`: Width of AXI write strobe, calculated based on AXI data width.
- `APB_WSTRB_WIDTH`: Width of APB write strobe, calculated based on APB data width.
- Various parameters for bus widths and array sizes derived from the above values.

## Module Ports

### Clock and Reset

- `aclk`: Input AXI clock.
- `aresetn`: Active low asynchronous reset signal.

### AXI Slave Interface

- `r_s_axi_*`: Input read channel handshake signals for the AXI slave interface.
- `w_s_axi_*`: Output write channel handshake signals for the AXI slave interface.
- Packets contain ID, address, control and user-defined signals.

### APB Master Interface

- `w_cmd_valid`: Output signal indicating the APB command is valid.
- `r_cmd_ready`: Input signal indicating the APB slave is ready for a command.
- `r_cmd_data`: Output APB command data.
- `r_rsp_valid`: Input signal indicating that read response data is available from the APB slave.
- `w_rsp_ready`: Output signal indicating that the AXI master is ready to receive read response data.
- `r_rsp_data`: Input APB response data.

## Internal Functionality

- Parsing and extracting individual signals from AXI packets.
- Handling of APB command and response packet generation.
- Utilization of a side FIFO to manage read and write operations and maintain ordering.
- State machines to manage APB interfacing (reads and writes) and to keep track of the current operation.
- Modules instantiated inside:
  - `axi_gen_addr`: Used to generate the APB address for sequential accesses.
  - `axi_fifo_sync`: A synchronous FIFO to buffer data and control paths independently.

## Functionality in Detail

- The AXI inputs are parsed and decomposed into their component signals.
- The module includes skid buffers to support backpressure between the AXI and APB side.
- Command packets for APB are assembled based on the AXI requests and include address, protection control, write enable, and data.
- APB response packets are processed and appropriately mapped onto the AXI response channels.
- A generic address generator (`axi_gen_addr`) is used to create addresses for bursts.
- Two finite state machines control the module operation:
  - One FSM for the APB command generation and data transmission phase.
  - Another FSM for the response phase, handling read and write acknowledgements.

## Usage

The `axi2apb_convert` module can be integrated into a larger system where translation between AXI master devices and APB peripherals is required. Proper initialization of all parameters is necessary to match the specific widths of the buses used in the system. Instantiate the module and connect it to the AXI and APB interfaces, ensuring accurate clock and reset connections.

## Clocking and Reset Considerations

The module operates synchronously with the AXI clock (`aclk`) and requires an active low reset signal (`aresetn`) to initialize its internal state.

## Notes

- Ensure that the data width ratios between AXI and APB are properly accounted for.
- Any buffering or additional latency introduced due to the side FIFO may need to be considered when integrating into a larger design.

## Conclusion

The `axi2apb_convert` module is vital for systems that require seamless communication between AXI and APB protocols. By encapsulating the protocol conversion logic, it simplifies the design process for system integrators.

## Block Hierarchy and Links

- [AXI to APB Convert](axi2apb_convert.md)
- [AXI to APB Shim](axi2apb_shim.md)

---

[Return to Index](index.md)

---
