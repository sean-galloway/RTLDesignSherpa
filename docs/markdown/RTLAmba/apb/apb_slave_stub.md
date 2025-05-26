# apb_slave_stub

This SystemVerilog module implements a stub version of an APB (Advanced Peripheral Bus) slave interface. It provides a simpler interface with packed command and response data formats, often used in testing or interconnect scenarios.

## Module Parameters

- `DEPTH`: FIFO buffer depth (default: 4)
- `DATA_WIDTH`: Data width in bits (default: 32)
- `ADDR_WIDTH`: Address width in bits (default: 32)
- `STRB_WIDTH`: Byte strobes width, calculated as DATA_WIDTH/8
- `CMD_PACKET_WIDTH`: Width of the packed command data (calculated from component parts)
- `RESP_PACKET_WIDTH`: Width of the packed response data (calculated from component parts)
- Short parameter aliases for convenience: `DW`, `AW`, `SW`, `CPW`, `RPW`

## Ports

### Clock and Reset:
- `pclk`: APB clock signal
- `presetn`: APB active-low reset

### APB Interface:
- `s_apb_PSEL`: APB select signal (input)
- `s_apb_PENABLE`: APB enable signal (input)
- `s_apb_PADDR`: APB address (input, width: AW)
- `s_apb_PWRITE`: APB write signal (input)
- `s_apb_PWDATA`: APB write data (input, width: DW)
- `s_apb_PSTRB`: APB write strobes (input, width: SW)
- `s_apb_PPROT`: APB protection attributes (input, width: 3)
- `s_apb_PRDATA`: APB read data (output, width: DW)
- `s_apb_PSLVERR`: APB slave error response (output)
- `s_apb_PREADY`: APB ready signal (output)

### Command Interface (Packed):
- `o_cmd_valid`: Command valid signal (output)
- `i_cmd_ready`: Command ready signal (input)
- `o_cmd_data`: Packed command data (output, width: CPW)

### Response Interface (Packed):
- `i_rsp_valid`: Response valid signal (input)
- `o_rsp_ready`: Response ready signal (output)
- `i_rsp_data`: Packed response data (input, width: RPW)

## Functionality

1. **Command FIFO**:
   - Captures APB transaction requests
   - Packs APB signals into a command data format
   - Uses a skid buffer implementation

2. **Response FIFO**:
   - Receives response data from the user logic
   - Unpacks response data for APB signals
   - Uses a skid buffer implementation

3. **APB State Machine**:
   - Implements a simplified state machine with IDLE and XFER_DATA states
   - IDLE: Waits for a valid APB transaction request
   - XFER_DATA: Waits for a response

4. **Signal Handling**:
   - Maps packed command and response data formats to APB interface signals
   - Manages APB protocol timing requirements

This stub module is typically used in interconnect blocks like crossbars, where multiple masters and slaves are connected and the packed data format simplifies routing.

---

[Return to Index](index.md)

---