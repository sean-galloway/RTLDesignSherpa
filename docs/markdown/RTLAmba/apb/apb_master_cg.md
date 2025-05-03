# apb_master_cg

This SystemVerilog module implements a clock-gated APB (Advanced Peripheral Bus) master interface. It wraps the standard `apb_master` module with clock gating functionality to reduce power consumption during periods of inactivity.

## Module Parameters

- `ADDR_WIDTH`: Address width in bits (default: 32)
- `DATA_WIDTH`: Data width in bits (default: 32)
- `PROT_WIDTH`: Protection information width (default: 3)
- `CMD_DEPTH`: Command FIFO depth (default: 6)
- `RSP_DEPTH`: Response FIFO depth (default: 6)
- `STRB_WIDTH`: Byte strobes width, calculated as DATA_WIDTH/8
- `CG_IDLE_COUNT_WIDTH`: Default width of idle counter (default: 4)
- Short parameter aliases for convenience: `AW`, `DW`, `SW`, `PW`, `ICW`, `CPW`, `RPW`

## Ports

### Clock and Reset:
- `pclk`: APB clock signal
- `presetn`: APB active-low reset

### Configuration:
- `i_cfg_cg_enable`: Global clock gate enable
- `i_cfg_cg_idle_count`: Idle countdown value (width: ICW)

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

### Clock Gating Status:
- `o_apb_clock_gating`: Clock gating indicator (output)

## Functionality

1. **Activity Detection**:
   - Monitors command, response, and transaction activity
   - Registers the wakeup signal to control clock gating

2. **Clock Gating Control**:
   - Uses the `amba_clock_gate_ctrl` module to manage clock gating
   - Provides configuration for enable and idle count
   - Generates a gated clock for the APB master

3. **APB Master**:
   - Instantiates the standard `apb_master` module using the gated clock
   - Forwards all interface signals between the module ports and the master instance

The module provides power-efficient operation by gating the clock to the APB master when there is no activity, while maintaining transparent APB protocol handling to connected modules.

---

[Return to Index](index.md)

---