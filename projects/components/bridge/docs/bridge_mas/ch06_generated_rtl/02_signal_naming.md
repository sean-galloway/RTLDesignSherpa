<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Signal Naming

## Naming Convention Overview

Bridge uses consistent signal naming to enable pattern-based verification and clear integration.

## External Port Naming

### Pattern

```
{prefix}_{channel}{signal}
```

### Components

| Component | Description | Example |
|-----------|-------------|---------|
| prefix | User-defined port prefix | cpu_m_axi, ddr_s_axi |
| channel | AXI4 channel code | aw, w, b, ar, r |
| signal | Signal within channel | valid, ready, addr, data |

### Master Port Examples

```systemverilog
// Master with prefix "cpu_m_axi"
input  logic        cpu_m_axi_awvalid,
output logic        cpu_m_axi_awready,
input  logic [31:0] cpu_m_axi_awaddr,
input  logic [3:0]  cpu_m_axi_awid,
input  logic [7:0]  cpu_m_axi_awlen,
input  logic [2:0]  cpu_m_axi_awsize,
input  logic [1:0]  cpu_m_axi_awburst,
input  logic        cpu_m_axi_awlock,
input  logic [3:0]  cpu_m_axi_awcache,
input  logic [2:0]  cpu_m_axi_awprot,
input  logic [3:0]  cpu_m_axi_awqos,
input  logic        cpu_m_axi_awuser,
```

### Slave Port Examples

```systemverilog
// Slave with prefix "ddr_s_axi"
output logic        ddr_s_axi_awvalid,
input  logic        ddr_s_axi_awready,
output logic [31:0] ddr_s_axi_awaddr,
output logic [5:0]  ddr_s_axi_awid,   // Extended ID
output logic [7:0]  ddr_s_axi_awlen,
output logic [2:0]  ddr_s_axi_awsize,
// ...
```

## APB Port Naming

### Pattern

```
{prefix}p{signal}
```

### APB Signal Examples

```systemverilog
// APB slave with prefix "uart_apb_"
output logic        uart_apb_psel,
output logic        uart_apb_penable,
output logic [11:0] uart_apb_paddr,
output logic        uart_apb_pwrite,
output logic [31:0] uart_apb_pwdata,
output logic [3:0]  uart_apb_pstrb,
output logic [2:0]  uart_apb_pprot,
input  logic [31:0] uart_apb_prdata,
input  logic        uart_apb_pslverr,
input  logic        uart_apb_pready,
```

## Internal Signal Naming

### Crossbar Signals

```systemverilog
// Master to crossbar
logic        xbar_m0_awvalid;
logic        xbar_m0_awready;
logic [31:0] xbar_m0_awaddr;

// Crossbar to slave
logic        xbar_s0_awvalid;
logic        xbar_s0_awready;
logic [31:0] xbar_s0_awaddr;
```

### Arbitration Signals

```systemverilog
// Request/grant matrices
logic [NUM_MASTERS-1:0] aw_request_s0;  // AW requests to slave 0
logic [NUM_MASTERS-1:0] aw_grant_s0;    // AW grants from slave 0

// Arbiter state
logic aw_grant_active_s0;               // Grant locked
logic [$clog2(NUM_MASTERS)-1:0] aw_last_grant_s0;  // Round-robin state
```

### ID Signals

```systemverilog
// Extended IDs (internal)
logic [TOTAL_ID_WIDTH-1:0] xbar_m0_awid;  // BID + external ID
logic [TOTAL_ID_WIDTH-1:0] xbar_s0_bid;   // Response with BID

// External IDs (to master)
logic [ID_WIDTH-1:0] cpu_m_axi_bid;       // Stripped ID
```

## Debug Signal Naming

### Pattern

```
dbg_{category}_{description}
```

### Debug Signal Examples

```systemverilog
// Arbitration debug
output logic [NUM_MASTERS-1:0] dbg_aw_grant_s0,
output logic [NUM_MASTERS-1:0] dbg_ar_grant_s0,

// Transaction debug
output logic [7:0] dbg_outstanding_m0,
output logic [7:0] dbg_outstanding_m1,

// State machine debug
output logic [1:0] dbg_aw_state_s0,
output logic [1:0] dbg_ar_state_s0,
```

## Verification Pattern Matching

### Factory Pattern Support

Signal naming enables automatic BFM connection:

```python
# CocoTB/GAXI pattern matching
master = AXI4Master(
    dut=dut,
    prefix="cpu_m_axi_",  # Matches all cpu_m_axi_* signals
    clock=dut.aclk
)
```

### Pattern Rules

1. Prefix must end with underscore or be directly followed by channel code
2. Channel codes are lowercase (aw, w, b, ar, r)
3. Signal names match AXI4 specification (valid, ready, addr, data, etc.)

## Related Documentation

- [Module Structure](01_module_structure.md) - Overall RTL organization
- [Verification](../ch07_verification/01_test_strategy.md) - Pattern-based testing
