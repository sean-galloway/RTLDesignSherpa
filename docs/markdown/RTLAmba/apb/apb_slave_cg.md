# apb_slave_cg

This SystemVerilog module implements a clock-gated APB (Advanced Peripheral Bus) slave interface. It wraps the standard `apb_slave` module with clock gating functionality to reduce power consumption during periods of inactivity.

## Module Parameters

- `ADDR_WIDTH`: Address width in bits (default: 32)
- `DATA_WIDTH`: Data width in bits (default: 32)
- `STRB_WIDTH`: Byte strobes width (default: 32/8 = 4)
- `PPROT_WIDTH`: Protection information width (default: 3)
- `DEPTH`: FIFO buffer depth (default: 2)
- `CG_IDLE_COUNT_WIDTH`: Default width of idle counter (default: 4)
- Short parameter aliases for convenience: `DW`, `AW`, `SW`, `PW`, `ICW`, `CPW`, `RPW`

## Ports

### Clock and Reset:
- `pclk`: APB clock signal
- `presetn`: APB active-low reset

### Configuration:
- `i_cfg_cg_enable`: Global clock gate enable
- `i_cfg_cg_idle_count`: Idle countdown value (width: ICW)

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

### Clock Gating Status:
- `o_apb_clock_gating`: Clock gating indicator (output)

## Functionality

1. **Activity Detection**:
   - Monitors command and response activity along with the APB state
   - Registers the wakeup signal to control clock gating
   - Detects when the interface is idle for clock gating

2. **Clock Gating Control**:
   - Uses the `amba_clock_gate_ctrl` module to manage clock gating
   - Provides configuration for enable and idle count
   - Generates a gated clock for the APB slave

3. **APB Slave**:
   - Instantiates the standard `apb_slave` module using the gated clock
   - Forwards all interface signals between the module ports and the slave instance

The module provides power-efficient operation by gating the clock to the APB slave when there is no activity, while maintaining transparent APB protocol handling to connected modules.

---

[Return to Index](index.md)

---