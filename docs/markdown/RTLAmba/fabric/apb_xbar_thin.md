# apb_xbar_thin

This SystemVerilog module implements a lightweight APB (Advanced Peripheral Bus) crossbar that connects multiple APB masters to multiple APB slaves, providing address-based routing without the use of intermediate command/response buffers.

## Module Parameters

- `M`: Number of APB masters (default: 2)
- `S`: Number of APB slaves (default: 4)
- `ADDR_WIDTH`: Address width in bits (default: 32)
- `DATA_WIDTH`: Data width in bits (default: 32)
- `STRB_WIDTH`: Byte strobes width, calculated as DATA_WIDTH/8
- `MAX_THRESH`: Maximum threshold for arbitration (default: 16)
- Short parameter aliases and calculated widths

## Ports

### Clock and Reset:
- `pclk`: APB clock signal
- `presetn`: APB active-low reset

### Configuration:
- `SLAVE_ENABLE`: Enable bit for each slave (width: S)
- `SLAVE_ADDR_BASE`: Base address for each slave (width: S×ADDR_WIDTH)
- `SLAVE_ADDR_LIMIT`: Upper address limit for each slave (width: S×ADDR_WIDTH)
- `THRESHOLDS`: Thresholds for the weighted round-robin arbiters (width: M×MTW)

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

1. **Address Decoding**:
   - Decodes master addresses to determine target slaves
   - Uses configurable base and limit addresses for each slave
   - Creates a master selection matrix for each slave

2. **Arbitration**:
   - Implements weighted round-robin arbitration for each slave
   - Handles contention when multiple masters target the same slave
   - Acknowledges grants when APB transactions complete

3. **Slave Interface Multiplexing**:
   - Directs APB signals from the selected master to each slave
   - Muxes signals including PSEL, PENABLE, PWRITE, PPROT, PADDR, PWDATA, and PSTRB
   - Uses arbitration results to control multiplexing

4. **Master Interface Demultiplexing**:
   - Routes response signals from slaves back to masters
   - Demuxes signals including PREADY, PRDATA, and PSLVERR
   - Ensures each master receives responses from its targeted slave

5. **Debugging Support**:
   - Contains optional debug logging (controlled by synthesis pragmas)
   - Outputs detailed signal information for verification

This "thin" version of the APB crossbar provides a direct connection between masters and slaves without intermediate buffering, making it more lightweight but potentially less capable of handling complex traffic patterns compared to the full version.

---

[Return to Index](index.md)

---