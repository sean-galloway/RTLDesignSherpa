# apb_slave_cdc

This SystemVerilog module implements an APB (Advanced Peripheral Bus) slave interface with clock domain crossing (CDC) capability, allowing APB transactions to safely cross between different clock domains.

## Module Parameters

- `ADDR_WIDTH`: Address width in bits (default: 32)
- `DATA_WIDTH`: Data width in bits (default: 32)
- `STRB_WIDTH`: Byte strobes width, calculated as DATA_WIDTH/8
- `PROT_WIDTH`: Protection information width (default: 3)
- `DEPTH`: FIFO buffer depth (default: 2)
- Short parameter aliases for convenience: `DW`, `AW`, `SW`, `PW`, `CPW`, `RPW`

## Ports

### Clock and Reset:
- `aclk`: Destination domain clock signal
- `aresetn`: Destination domain active-low reset
- `pclk`: APB domain clock signal
- `presetn`: APB domain active-low reset

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

### Command Interface (Destination Clock Domain):
- `o_cmd_valid`: Command valid signal (output)
- `i_cmd_ready`: Command ready signal (input)
- `o_cmd_pwrite`: Write/read command indicator (output)
- `o_cmd_paddr`: Command address (output, width: AW)
- `o_cmd_pwdata`: Write data (output, width: DW)
- `o_cmd_pstrb`: Write strobes (output, width: SW)
- `o_cmd_pprot`: Protection attributes (output, width: PW)

### Response Interface (Destination Clock Domain):
- `i_rsp_valid`: Response valid signal (input)
- `o_rsp_ready`: Response ready signal (output)
- `i_rsp_prdata`: Response read data (input, width: DW)
- `i_rsp_pslverr`: Response error signal (input)

## Functionality

1. **Local Parameters**:
   - Defines width parameters for APB command and response data

2. **APB Slave Interface**:
   - Instantiates a standard APB slave module
   - Operates in the APB (pclk) clock domain
   - Converts APB transactions to command/response protocol

3. **Command CDC Handshake**:
   - Uses the `cdc_handshake` module to safely transfer command data from pclk to aclk domain
   - Packages command signals into a single data word for the handshake
   - Unpacks data on the destination side
   - Implements a complete four-phase handshake protocol with proper synchronization

4. **Response CDC Handshake**:
   - Uses the `cdc_handshake` module to safely transfer response data from aclk to pclk domain
   - Packages response signals into a single data word for the handshake
   - Unpacks data on the destination side
   - Provides metastability protection through multi-stage synchronizers

The module ensures safe clock domain crossing for APB transactions, allowing peripheral logic to operate in a different clock domain while still being accessible via the APB interface. It maintains protocol correctness and data integrity across the domain boundary.

---

[Return to Index](index.md)

---