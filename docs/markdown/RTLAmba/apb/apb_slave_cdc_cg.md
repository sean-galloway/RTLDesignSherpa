# apb_slave_cdc_cg

This SystemVerilog module implements an APB (Advanced Peripheral Bus) slave interface with both clock domain crossing (CDC) capability and clock gating (CG) for power optimization.

## Module Parameters

- `ADDR_WIDTH`: Address width in bits (default: 32)
- `DATA_WIDTH`: Data width in bits (default: 32)
- `STRB_WIDTH`: Byte strobes width, calculated as DATA_WIDTH/8
- `PROT_WIDTH`: Protection information width (default: 3)
- `DEPTH`: FIFO buffer depth (default: 2)
- `CG_IDLE_COUNT_WIDTH`: Width of idle counter for clock gating (default: 4)
- Short parameter aliases for convenience: `DW`, `AW`, `SW`, `PW`, `CPW`, `RPW`

## Ports

### Clock and Reset:
- `aclk`: Destination domain clock signal
- `aresetn`: Destination domain active-low reset
- `pclk`: APB domain clock signal
- `presetn`: APB domain active-low reset

### Clock Gating Configuration:
- `i_cfg_cg_enable`: Global clock gate enable
- `i_cfg_cg_idle_count`: Idle countdown value (width: CG_IDLE_COUNT_WIDTH)

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

### Clock Gating Status:
- `o_pclk_cg_gating`: PCLK domain gating indicator
- `o_pclk_cg_idle`: PCLK domain idle indicator
- `o_aclk_cg_gating`: ACLK domain gating indicator
- `o_aclk_cg_idle`: ACLK domain idle indicator

## Functionality

1. **Local Parameters**:
   - Defines width parameters for APB command and response data

2. **Clock Gating Control**:
   - Uses two instances of `amba_clock_gate_ctrl` for both clock domains
   - Monitors activity signals in each domain to control gating
   - Provides gated clocks to APB slave and CDC handshake modules

3. **Activity Monitoring**:
   - Monitors various valid/ready signals to determine when idle
   - Combines signals appropriately for each clock domain

4. **Ready Signal Control**:
   - Forces ready signals to zero during clock gating periods
   - Prevents protocol violations during gating transitions

5. **APB Slave Interface**:
   - Instantiates a standard APB slave module with gated clock
   - Forces PREADY to zero during clock gating periods

6. **CDC Handshake**:
   - Uses `cdc_handshake` modules with gated clocks for command and response paths
   - Ensures proper synchronization between clock domains with multi-stage synchronizers
   - Preserves protocol correctness during clock gating transitions
   - Implements four-phase handshaking with proper metastability protection
   - Safely manages data transfer across both clock and power domains

The module provides a complete solution for an APB slave interface that can operate across clock domains with power optimization through independent clock gating in each domain.

---

[Return to Index](index.md)

---