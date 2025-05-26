# apb_master

This SystemVerilog module implements an APB (Advanced Peripheral Bus) master interface that converts a simple command/response interface into standard APB protocol transactions.

## Module Parameters

- `ADDR_WIDTH`: Address width in bits (default: 32)
- `DATA_WIDTH`: Data width in bits (default: 32)
- `PROT_WIDTH`: Protection information width (default: 3)
- `CMD_DEPTH`: Command FIFO depth (default: 6)
- `RSP_DEPTH`: Response FIFO depth (default: 6)
- `STRB_WIDTH`: Byte strobes width, calculated as DATA_WIDTH/8
- Short parameter aliases for convenience: `AW`, `DW`, `SW`, `PW`, `CPW`, `RPW`

## Ports

### Clock and Reset:
- `pclk`: APB clock signal
- `presetn`: APB active-low reset

### APB Interface:
- `m_apb_PSEL`: APB select signal (output)
- `m_apb_PENABLE`: APB enable signal (output)
- `m_apb_PADDR`: APB address (output, width: AW)
- `m_apb_PWRITE`: APB write signal (output)
- `m_apb_PWDATA`: APB write data (output, width: DW)
- `m_apb_PSTRB`: APB write strobes (output, width: SW)
- `m_apb_PPROT`: APB protection attributes (output, width: PW)
- `m_apb_PRDATA`: APB read data (input, width: DW)
- `m_apb_PSLVERR`: APB slave error response (input)
- `m_apb_PREADY`: APB ready signal (input)

### Command Interface:
- `i_cmd_valid`: Command valid signal (input)
- `o_cmd_ready`: Command ready signal (output)
- `i_cmd_pwrite`: Write/read command indicator (input)
- `i_cmd_paddr`: Command address (input, width: AW)
- `i_cmd_pwdata`: Write data (input, width: DW)
- `i_cmd_pstrb`: Write strobes (input, width: SW)
- `i_cmd_pprot`: Protection attributes (input, width: PW)

### Response Interface:
- `o_rsp_valid`: Response valid signal (output)
- `i_rsp_ready`: Response ready signal (input)
- `o_rsp_prdata`: Response read data (output, width: DW)
- `o_rsp_pslverr`: Response error signal (output)

## Functionality

1. **Command FIFO**:
   - Stores incoming commands using a skid buffer
   - Packs command input signals into a single data word
   - Unpacks data for use in the APB interface

2. **Response FIFO**:
   - Stores responses for read operations
   - Includes error signals and read data
   - Uses a skid buffer implementation

3. **APB State Machine**:
   - Implements the APB protocol with three states: IDLE, SETUP, ACCESS
   - IDLE: Waits for valid commands
   - SETUP: Asserts PSEL without PENABLE for one cycle (APB protocol requirement)
   - ACCESS: Asserts both PSEL and PENABLE and waits for PREADY

4. **Transaction Handling**:
   - For read operations: Stores response data in the response FIFO
   - For write operations: Completes transactions without storing response data
   - Optimizes back-to-back transfers when multiple commands are queued

The module adheres to the APB protocol specification while providing buffering and a simplified command/response interface for the client logic.

---

[Return to Index](index.md)

---