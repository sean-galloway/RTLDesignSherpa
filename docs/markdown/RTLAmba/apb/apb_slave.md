# apb_slave

This SystemVerilog module implements an APB (Advanced Peripheral Bus) slave interface that converts the standard APB protocol signals to a simple command/response interface.

## Module Parameters

- `ADDR_WIDTH`: Address width in bits (default: 32)
- `DATA_WIDTH`: Data width in bits (default: 32)
- `STRB_WIDTH`: Byte strobes width (default: 32/8 = 4)
- `PROT_WIDTH`: Protection information width (default: 3)
- `DEPTH`: FIFO buffer depth (default: 2)
- Short parameter aliases for convenience: `DW`, `AW`, `SW`, `PW`, `CPW`, `RPW`

## Ports

### Clock and Reset:
- `pclk`: APB clock signal
- `presetn`: APB active-low reset

### APB Interface:
- `s_apb_PSEL`: APB select signal (input)
- `s_apb_PENABLE`: APB enable signal (input)
- `s_apb_PREADY`: APB ready signal (output)
- `s_apb_PADDR`: APB address (input, width: AW)
- `s_apb_PWRITE`: APB write signal (input)
- `s_apb_PWDATA`: APB write data (input, width: DW)
- `s_apb_PSTRB`: APB write strobes (input, width: SW)
- `s_apb_PPROT`: APB protection attributes (input, width: PW)
- `s_apb_PRDATA`: APB read data (output, width: DW)
- `s_apb_PSLVERR`: APB slave error response (output)

### Command Interface:
- `o_cmd_valid`: Command valid signal (output)
- `i_cmd_ready`: Command ready signal (input)
- `o_cmd_pwrite`: Write/read command indicator (output)
- `o_cmd_paddr`: Command address (output, width: AW)
- `o_cmd_pwdata`: Write data (output, width: DW)
- `o_cmd_pstrb`: Write strobes (output, width: SW)
- `o_cmd_pprot`: Protection attributes (output, width: PW)

### Response Interface:
- `i_rsp_valid`: Response valid signal (input)
- `o_rsp_ready`: Response ready signal (output)
- `i_rsp_prdata`: Response read data (input, width: DW)
- `i_rsp_pslverr`: Response error signal (input)

## Functionality

1. **Command Handling**:
   - Captures APB transaction requests when PSEL and PENABLE are active
   - Packs APB signals into a command data format
   - Uses a skid buffer to store commands

2. **Response Handling**:
   - Receives response data from the user logic
   - Uses a skid buffer to store responses
   - Drives the APB response signals when responses are received

3. **APB State Machine**:
   - Implements a three-state machine: IDLE, BUSY, WAIT
   - IDLE: Waits for a valid APB transaction request (PSEL and PENABLE)
   - BUSY: Waits for a response from the user logic
   - WAIT: Completes the transaction by asserting PREADY for one cycle

4. **Error Handling**:
   - Forwards the error signal (PSLVERR) from the response interface

The module provides a clean interface abstraction, allowing user logic to work with a simple command/response protocol instead of implementing the full APB timing.

---

[Return to Index](index.md)

---