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

The generator turns configuration files into parameterized SystemVerilog modules, and every topology gets the same internal structure. Once you've read one generated bridge, you can find your way around any of them.

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
axi4_to_apb4 u_s2_apb_conv (...);

// Response routing
response_router u_resp_router (...);

// Monitor system (when variants include "mon")
axi4_master_rd_mon u_m0_rd_mon (...);    // Per-port monitor wrappers
axi4_master_wr_mon u_m0_wr_mon (...);
axi4_slave_rd_mon  u_s0_rd_mon (...);
axi4_slave_wr_mon  u_s0_wr_mon (...);
// ... (repeat for remaining ports)

// Monitor aggregation tree (if multiple monitors)
monbus_arbiter u_mon_arb0 (...);         // Aggregate master-side streams
monbus_arbiter u_mon_arb1 (...);         // Aggregate slave-side streams

// Monitor AXIL group at bridge top
monbus_axil4_axil4_group #(
    .FIFO_DEPTH_ERR      (64),
    .FIFO_DEPTH_WRITE    (96),   // in BEATS, not packets
    .ADDR_WIDTH          (32),
    .FLUSH_TIMEOUT_CYCLES(1024),
    .NUM_PROTOCOLS       (3),
    .USE_COMPRESSION     (0)
) u_mon_axil_group (
    .axi_aclk         (aclk),
    .axi_aresetn      (aresetn),
    // the monbus_arbiter's output is the group's single input
    .monbus_valid     (mon_arb_monbus_valid),
    .monbus_ready     (mon_arb_monbus_ready),
    .monbus_packet    (mon_arb_monbus_packet),
    .monbus_timestamp (mon_arb_monbus_timestamp),
    // free-running time, fanned out to every wrapper's i_mon_time
    .mon_time_out     (mon_time_w),
    .s_axil_*         (s_mon_axil_*),   // slave read port (CPU access)
    .m_axil_*         (m_mon_axil_*),   // master write port (bulk DMA)
    .irq_out          (mon_irq_out)
);
```

## Reset Style and the Emitted Filelist

Every generated adapter, crossbar and slave adapter opens with

```systemverilog
`include "reset_defs.svh"
```

and writes its flops through the macro, never a raw `always_ff`:

```systemverilog
`ALWAYS_FF_RST(aclk, aresetn,
    if (`RST_ASSERTED(aresetn)) begin
        ...
    end else begin
        ...
    end
)
```

Reset is **asynchronous on assertion in every build**. `ALWAYS_FF_RST` used to
be conditional on `USE_ASYNC_RESET` and defaulted to synchronous, so `make
lint` (which set the define) and simulation/synthesis (which did not)
disagreed about what the design was. The define is now a no-op; passing it is
harmless and changes nothing. Deassertion must still be synchronised
externally.

Because the emitted RTL depends on that header, the generator also emits the
`-f` that supplies it, so a generated filelist resolves standalone:

```
# Include directories
+incdir+$REPO_ROOT/rtl/amba/includes

# Reset macro header (`ALWAYS_FF_RST / `RST_ASSERTED)
-f $REPO_ROOT/rtl/amba/filelists/reset_defs.f

# Monitor packages (must precede any module that references them)
-f $REPO_ROOT/rtl/amba/filelists/monitor_pkgs.f
```

The `-f` matters as much as the `+incdir`: the header must be *compiled*
ahead of the modules that expand the macro, not merely be findable. A
consumer that hand-lists the generated `.sv` files instead of taking this
filelist gets `Cannot find include file: 'reset_defs.svh'` — see
`/GLOBAL_REQUIREMENTS.md` on resolving sources through filelists.

## Generated Variants

When `variants` list in the bridge TOML includes multiple entries, the generator produces one complete `.sv` file per variant:

```
variants = ["no", "mon"]

Generated files:
  bridge_4x3.sv              (variants = "no", no monitor)
  bridge_4x3_mon.sv          (variants = "mon", with monitor)
```

Each variant is a complete, standalone bridge module. Both can coexist in the same design or be selected at compile time.

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
wr_fifo/rd_fifo[...]   - per-slave bridge_id FIFO (no ID table exists)
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
├── axi4_to_apb4.sv          - Protocol converter
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
