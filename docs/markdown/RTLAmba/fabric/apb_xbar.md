# apb_xbar

This SystemVerilog module implements an APB (Advanced Peripheral Bus) crossbar that connects multiple APB masters to multiple APB slaves, providing address-based routing.

## Module Parameters

- `M`: Number of APB masters (default: 3)
- `S`: Number of APB slaves (default: 6)
- `ADDR_WIDTH`: Address width in bits (default: 32)
- `DATA_WIDTH`: Data width in bits (default: 32)
- `STRB_WIDTH`: Byte strobes width, calculated as DATA_WIDTH/8
- `MAX_THRESH`: Maximum threshold for arbitration (default: 16)
- `DEPTH`: FIFO buffer depth (default: 4)
- Short parameter aliases and calculated widths

## Ports

### Clock and Reset:
- `pclk`: APB clock signal
- `presetn`: APB active-low reset

### Configuration:
- `SLAVE_ENABLE`: Enable bit for each slave (width: S)
- `SLAVE_ADDR_BASE`: Base address for each slave (width: S×ADDR_WIDTH)
- `SLAVE_ADDR_LIMIT`: Upper address limit for each slave (width: S×ADDR_WIDTH)
- `MST_THRESHOLDS`: Thresholds for master arbitration (width: M×MTW)
- `SLV_THRESHOLDS`: Thresholds for slave arbitration (width: S×MTW)

### Master Interfaces (from APB masters):
- `m_apb_psel`: APB select signals (width: M)
- `m_apb_penable`: APB enable signals (width: M)
- `m_apb_pwrite`: APB write signals (width: M)
- `m_apb_pprot`: APB protection attributes (width: M×3)
- `m_apb_paddr`: APB addresses (width: M×ADDR_WIDTH)
- `m_apb_pwdata`: APB write data (width: M×DATA_WIDTH)
- `m_apb_pstrb`: APB write strobes (width: M×STRB_WIDTH)
- `m_apb_pready`: APB ready signals (width: M)
- `m_apb_prdata`: APB read data (width: M×DATA_WIDTH)
- `m_apb_pslverr`: APB slave error responses (width: M)

### Slave Interfaces (to APB slaves):
- `s_apb_psel`: APB select signals (width: S)
- `s_apb_penable`: APB enable signals (width: S)
- `s_apb_pwrite`: APB write signals (width: S)
- `s_apb_pprot`: APB protection attributes (width: S×3)
- `s_apb_paddr`: APB addresses (width: S×ADDR_WIDTH)
- `s_apb_pwdata`: APB write data (width: S×DATA_WIDTH)
- `s_apb_pstrb`: APB write strobes (width: S×STRB_WIDTH)
- `s_apb_pready`: APB ready signals (width: S)
- `s_apb_prdata`: APB read data (width: S×DATA_WIDTH)
- `s_apb_pslverr`: APB slave error responses (width: S)

## Functionality

1. **Slave Stubs**:
   - Implements APB slave stubs for each master interface
   - Converts APB protocol to command/response format
   - Uses FIFOs to buffer commands and responses

2. **Master Stubs**:
   - Implements APB master stubs for each slave interface
   - Converts command/response format back to APB protocol
   - Uses FIFOs to buffer commands and responses

3. **Address Decoding**:
   - Decodes master addresses to determine target slaves
   - Uses configurable base and limit addresses for each slave
   - Enables address-based routing of transactions

4. **Command Routing**:
   - Routes command packets from masters to appropriate slaves
   - Uses side channel FIFOs to track master IDs for responses
   - Implements proper handshaking for data transfer

5. **Arbitration**:
   - Uses weighted round-robin arbitration for both master and slave sides
   - Provides fair access when multiple masters target the same slave
   - Grants access based on configurable thresholds

6. **Debugging Support**:
   - Contains optional debug logging (controlled by synthesis pragmas)
   - Outputs detailed signal information for verification

The module provides a complete APB interconnect solution with multiple master and slave connections, appropriate arbitration, and efficient data transfer.

---

[Return to Index](index.md)

---