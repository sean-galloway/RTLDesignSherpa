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

# Module Structure

## Generated RTL Overview

Bridge generator creates parameterized SystemVerilog modules from configuration files. The generated RTL follows a consistent structure for all topologies.

## Top-Level Module

### Module Declaration

```systemverilog
module bridge_4x3 #(
    parameter int NUM_MASTERS = 4,
    parameter int NUM_SLAVES = 3,
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 64,
    parameter int ID_WIDTH = 4
) (
    // Clock and reset
    input  logic aclk,
    input  logic aresetn,

    // Master interfaces (M0-M3)
    // ... master port signals ...

    // Slave interfaces (S0-S2)
    // ... slave port signals ...
);
```

### Port Organization

```
Module Ports:
├── Clock/Reset
│   ├── aclk
│   └── aresetn
├── Master Ports (per master)
│   ├── AW Channel (if rw or wr)
│   ├── W Channel (if rw or wr)
│   ├── B Channel (if rw or wr)
│   ├── AR Channel (if rw or rd)
│   └── R Channel (if rw or rd)
└── Slave Ports (per slave)
    ├── AW Channel
    ├── W Channel
    ├── B Channel
    ├── AR Channel
    └── R Channel
```

## Internal Structure

### Component Instantiation

```systemverilog
// Generated module internal structure

// Master adapters (per master)
master_adapter_rw u_m0_adapter (...);
master_adapter_wr u_m1_adapter (...);
master_adapter_rd u_m2_adapter (...);
master_adapter_rw u_m3_adapter (...);

// Address decoders (per master)
address_decoder u_m0_decoder (...);
address_decoder u_m1_decoder (...);
address_decoder u_m2_decoder (...);
address_decoder u_m3_decoder (...);

// Per-slave arbiters
arbiter_aw u_s0_aw_arb (...);
arbiter_ar u_s0_ar_arb (...);
arbiter_aw u_s1_aw_arb (...);
arbiter_ar u_s1_ar_arb (...);
arbiter_aw u_s2_aw_arb (...);
arbiter_ar u_s2_ar_arb (...);

// Width converters (as needed)
width_upsize_64_512 u_m0_s0_upsizer (...);

// Protocol converters (as needed)
axi4_to_apb u_s2_apb_conv (...);

// Response routing
response_router u_resp_router (...);
```

## Signal Naming Convention

### Master-Side Signals (External)

```
{prefix}_aw{signal}    - Write address channel
{prefix}_w{signal}     - Write data channel
{prefix}_b{signal}     - Write response channel
{prefix}_ar{signal}    - Read address channel
{prefix}_r{signal}     - Read data channel

Example (prefix = "cpu_m_axi"):
  cpu_m_axi_awvalid
  cpu_m_axi_awready
  cpu_m_axi_awaddr
  cpu_m_axi_wdata
  cpu_m_axi_bvalid
```

### Slave-Side Signals (External)

```
{prefix}_aw{signal}    - Write address channel
{prefix}_w{signal}     - Write data channel
{prefix}_b{signal}     - Write response channel
{prefix}_ar{signal}    - Read address channel
{prefix}_r{signal}     - Read data channel

Example (prefix = "ddr_s_axi"):
  ddr_s_axi_awvalid
  ddr_s_axi_awready
  ddr_s_axi_awaddr
  ddr_s_axi_wdata
  ddr_s_axi_bvalid
```

### Internal Signals

```
// Crossbar internal signals
xbar_m{N}_aw_{signal}  - Master N to crossbar AW
xbar_m{N}_ar_{signal}  - Master N to crossbar AR
xbar_s{N}_aw_{signal}  - Crossbar to slave N AW
xbar_s{N}_ar_{signal}  - Crossbar to slave N AR

// Arbitration signals
grant_aw_s{N}[M-1:0]   - AW grants for slave N
grant_ar_s{N}[M-1:0]   - AR grants for slave N

// ID tracking signals
id_table_s{N}[...]     - ID table for slave N
```

## Generated File Structure

### Single-File Output

```
bridge_{name}.sv
├── Module declaration
├── Parameter section
├── Port declarations
├── Internal signal declarations
├── Master adapter instances
├── Address decoder instances
├── Arbiter instances
├── Converter instances
├── Response router instance
└── Debug signals (optional)
```

### Multi-File Output (Optional)

```
bridge_{name}/
├── bridge_{name}.sv        - Top-level wrapper
├── master_adapter_m0.sv    - Master 0 adapter
├── master_adapter_m1.sv    - Master 1 adapter
├── address_decoder.sv      - Shared decoder
├── arbiter_aw.sv           - AW arbiter
├── arbiter_ar.sv           - AR arbiter
├── width_upsize_64_512.sv  - Width converter
├── axi4_to_apb.sv          - Protocol converter
└── response_router.sv      - Response routing
```

## Parameterization

### Compile-Time Parameters

```systemverilog
// Core parameters
parameter int NUM_MASTERS = 4;
parameter int NUM_SLAVES = 3;
parameter int ADDR_WIDTH = 32;
parameter int DATA_WIDTH = 64;
parameter int ID_WIDTH = 4;

// Derived parameters
localparam int BID_WIDTH = $clog2(NUM_MASTERS);
localparam int TOTAL_ID_WIDTH = ID_WIDTH + BID_WIDTH;
localparam int STRB_WIDTH = DATA_WIDTH / 8;
```

### Per-Port Parameters

```systemverilog
// Generated per-port widths
localparam int M0_DATA_WIDTH = 64;
localparam int M1_DATA_WIDTH = 256;
localparam int S0_DATA_WIDTH = 512;
localparam int S1_DATA_WIDTH = 32;  // APB
```

## Related Documentation

- [Signal Naming](02_signal_naming.md) - Detailed naming conventions
- [Generator Usage](../../CLAUDE.md) - How to run the generator
