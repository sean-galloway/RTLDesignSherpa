# apb_master_stub

This SystemVerilog module implements a stub version of an APB (Advanced Peripheral Bus) master. It provides a simpler interface with packed command and response data formats, often used in testing or interconnect scenarios.

## Module Parameters

- `CMD_DEPTH`: Command FIFO depth (default: 6)
- `RSP_DEPTH`: Response FIFO depth (default: 6)
- `DATA_WIDTH`: Data width in bits (default: 32)
- `ADDR_WIDTH`: Address width in bits (default: 32)
- `STRB_WIDTH`: Byte strobes width, calculated as DATA_WIDTH/8
- `CMD_PACKET_WIDTH`: Width of the packed command data (calculated from component parts)
- `RESP_PACKET_WIDTH`: Width of the packed response data (calculated from component parts)
- Short parameter aliases for convenience: `DW`, `AW`, `SW`, `CPW`, `RPW`, `CAW`

## Ports

### Clock and Reset:
- `pclk`: APB clock signal
- `presetn`: APB active-low reset

### APB Interface:
- `m_apb_PSEL`: APB select signal (output)
- `m_apb_PENABLE`: APB enable signal (output)
- `m_apb_PADDR`: APB address (output, width: ADDR_WIDTH)
- `m_apb_PWRITE`: APB write signal (output)
- `m_apb_PWDATA`: APB write data (output, width: DATA_WIDTH)
- `m_apb_PSTRB`: APB write strobes (output, width: STRB_WIDTH)
- `m_apb_PPROT`: APB protection attributes (output, width: 3)
- `m_apb_PRDATA`: APB read data (input, width: DATA_WIDTH)
- `m_apb_PSLVERR`: APB slave error response (input)
- `m_apb_PREADY`: APB ready signal (input)

### Command Interface (Packed):
- `i_cmd_valid`: Command valid signal (input)
- `o_cmd_ready`: Command ready signal (output)
- `i_cmd_data`: Packed command data (input, width: CMD_PACKET_WIDTH)

### Response Interface (Packed):
- `o_rsp_valid`: Response valid signal (output)
- `i_rsp_ready`: Response ready signal (input)
- `o_rsp_data`: Packed response data (output, width: RESP_PACKET_WIDTH)

## Functionality

1. **Command FIFO**:
   - Stores incoming commands using a skid buffer
   - Works with the packed command format that includes additional flags
   - Unpacks command data into component signals for APB interface

2. **Response FIFO**:
   - Stores responses from APB slave
   - Packs response data, including first/last flags

3. **APB State Machine**:
   - Uses a simplified state machine with IDLE and ACTIVE states
   - IDLE: Waits for valid commands
   - ACTIVE: Processes APB transactions

4. **Transaction Handling**:
   - Drives the APB interface signals based on command packet content
   - Collects responses and packages them for the response interface
   - All transactions (both read and write) generate a response

This module is typically used in interconnect blocks like crossbars, where multiple masters and slaves are connected and the packed data format simplifies routing.

---

[Return to Index](index.md)

---