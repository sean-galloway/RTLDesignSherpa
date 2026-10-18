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

## Overview

The generator turns configuration files into parameterized SystemVerilog modules, and every topology gets the same internal structure. Parameterized at generation time, mind you — not at elaboration, as the next section makes clear. Once you've read one generated bridge, you can find your way around any of them.

## Parameters

### Compile-Time Parameters

The generated top has no parameter list. The shared constants live in the
per-bridge package `<bridge>_pkg.sv`; this is `bridge_2x2_rw_pkg.sv`:

```systemverilog
localparam int NUM_MASTERS     = 2;
localparam int BRIDGE_ID_WIDTH = 1;  // $clog2(NUM_MASTERS): sideband master index
localparam int MASTER_ID_WIDTH = 4;  // widest master-side ID
localparam int ID_PREFIX_WIDTH = 1;  // master-index bits prepended (0 for one master)
localparam int XBAR_ID_WIDTH   = 5;  // MASTER_ID_WIDTH + ID_PREFIX_WIDTH
```

`BRIDGE_ID_WIDTH` sizes the `bridge_id` sideband that the slave adapters
store; `XBAR_ID_WIDTH` is the AXI ID width inside the fabric and on every
AXI slave port, because each master adapter widens its IDs to
`{BRIDGE_ID, id}` (Section 2.5). The package also defines the AXI channel
structs used by the crossbar, one per data width present.

### Per-Port Parameters

Per-port widths are baked straight into the port declarations; there are no
`M0_DATA_WIDTH`-style localparams to override. Each adapter module does carry
a small parameter list (for example `BRIDGE_ID` on a master adapter, `ID_WIDTH`
on a slave adapter), set by the generated top.

## Ports

### Module Declaration

The generated top level has NO PARAMETER LIST. Every width is fixed for the
configuration at generation time and the only shared constants live in the
per-bridge package, so there is nothing to override at instantiation. This is
`bridge_2x2_rw.sv` as emitted:

```systemverilog
module bridge_2x2_rw
    import bridge_2x2_rw_pkg::*;
(
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

Note the conditional channels on the master side — a write-only master gets no AR/R, a read-only master gets no AW/W/B.

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

A CDC port (cdc = true; slave: bridge TASK-006, master: GitHub #119 L2) adds two clock pins:
  {name}_aclk            - the port's own clock
  {name}_aresetn         - its active-low reset

A watchdog slave (timeout_cycles > 0, GitHub #119 L3) adds one status pin:
  {name}_timeout         - axi4_slave_watchdog tripped, sticky until reset
```

A watchdog slave's adapter instantiates `axi4_slave_watchdog` between its
timing wrapper (driving `wdg_{name}_axi_*`) and the port, or the clock
crossing on a CDC port, on `aclk`; its `o_wdog_tripped` is the top's
`{name}_timeout`. Beside the RTL, every bridge also gets
`{bridge}_checkers.sv`, protocol-checker binds for simulation and formal
(HAS, Verification Strategy).

A `cdc = true` slave port's adapter takes `s_aclk`/`s_aresetn` beside
`aclk`/`aresetn`. Inside it the timing wrapper (and the monitor, when built)
stay on `aclk`, driving `cdc_{name}_axi_*` nets; `axi4_cdc_wr` and
`axi4_cdc_rd` carry those to the external port on `s_aclk`, one
`gaxi_fifo_async` per channel. Nothing upstream of the wrapper knows the
port is in another domain. `protocol = "axi4"` only (HAS 4.5a).

A `cdc = true` master port's adapter takes `ext_aclk`/`ext_aresetn` beside
`aclk`/`aresetn`, and the crossing sits on the other side of the wrapper:
`axi4_cdc_wr` / `axi4_cdc_rd` take the external port on `ext_aclk` and drive
`cdcx_axi_*` nets on `aclk`, which the timing wrapper takes as its external
side. Only the crossing for a direction the port has is built. Everything
from the wrapper on -- monitor, decode, per-ID target tracking, width paths
-- is the same-clock adapter (GitHub #119 L2).

## Functional Description

### Component Instantiation

Adapters are named after the port, not the index, and there is no standalone
address decoder, arbiter, width-converter or response-router module at the
top: address decode, arbitration and response muxing are inline in the
crossbar and the master adapters; width converters and protocol shims are
instantiated inside the adapter that needs them. The complete instance list
of `bridge_2x2_rw.sv`:

```systemverilog
axi4_subtractive_slave #(...) u_subtractive (...);   // unmapped-address default (DECERR)
cpu_adapter            u_cpu_adapter (...);          // per master, named for the port
dma_adapter            u_dma_adapter (...);
bridge_2x2_rw_xbar     u_xbar (...);                 // decode, per-slave AW/AR arbiters,
                                                     // W owner/destination FIFOs, B/R muxes
ddr_adapter            u_ddr_adapter (...);          // per slave, named for the port
sram_adapter           u_sram_adapter (...);         //   (by-ID counters inside, multi-master)
subtractive_adapter    u_subtractive_adapter (...);
```

What lives inside the adapters (from `bridge_mix_a_mon`):

```
<master>_adapter   axi4_dwidth_converter_{rd,wr}       width paths, where widths differ
                   axil_to_axi4_wide_align_{rd,wr}     AXI4-Lite master ports
                   axi4_slave_{rd,wr}_monlite          monitored variants only
<slave>_adapter    axi4_master_{rd,wr}[_monlite]       timing wrapper (+ monitor)
                   axi4_to_apb4_shim                   apb slave
                   axi4_to_axil4_{rd,wr}               axil slave
```

A monitored variant adds two instances at the top: one `monbus_arbiter`
merging every port's monitor stream, and the AXIL group behind it:

```systemverilog
monbus_arbiter #(.CLIENTS(10), ...) u_...;   // bridge_mix_a_mon: 10 monitor streams

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

### Internal Signals

```
// Top-level nets between crossbar and slave adapters
xbar_{slave}_axi_{aw,w,b,ar,r}{signal}   e.g. xbar_ddr_axi_awid (XBAR_ID_WIDTH bits)

// Inside the crossbar
{slave}_{aw,ar}_arb_gnt                  per-slave round-robin grant
{master}_{w}b_{aw,ar}_gnt_{slave}        master width-path granted to slave
{master}_{w}b_wdest_*                    W destination FIFO (per master width-path)
{slave}_wowner_*                         W owner FIFO (per slave)

// Response routing sideband (slave adapter -> crossbar)
{slave}_axi_bridge_id_{aw,ar}            granted master's index, into the tracker
{slave}_axi_{bid,rid}_bridge_id / _valid tracker output steering B / R

// ID tracking inside a slave adapter
wr_out_cnt / rd_out_cnt                  by-ID counters (multi-master AXI3/AXI4/AXI5 slave)
wr_fifo / rd_fifo                        in-order bridge_id FIFO (otherwise)
```

### Reset Style and the Emitted Filelist

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

### Generated Variants

The mandatory `variants` list in the `[bridge]` table picks which builds to
emit. Each variant is written to its own directory under `rtl/generated/`
and is a complete, standalone bridge:

```
variants = ["no", "mon"]   (bridge_mix_a)

rtl/generated/bridge_mix_a/bridge_mix_a.sv            no monitors
rtl/generated/bridge_mix_a_mon/bridge_mix_a_mon.sv    monitored
```

### Generated File Structure

The generator always writes one directory per bridge (and per variant), one
module per file. Regenerated listing of `rtl/generated/bridge_2x2_rw/`:

```
rtl/generated/bridge_2x2_rw/
├── bridge_2x2_rw.sv                  - top level (BridgeModuleGenerator)
├── bridge_2x2_rw_pkg.sv              - constants + channel structs (PackageGenerator)
├── bridge_2x2_rw_xbar.sv             - crossbar (CrossbarGenerator)
├── cpu_adapter.sv                    - master adapter, port "cpu" (AdapterGenerator)
├── dma_adapter.sv                    - master adapter, port "dma"
├── ddr_adapter.sv                    - slave adapter, port "ddr" (SlaveAdapterGenerator)
├── sram_adapter.sv                   - slave adapter, port "sram"
├── subtractive_adapter.sv            - adapter for the internal DECERR slave
├── bridge_2x2_rw.toml                - copy of the port configuration
└── bridge_2x2_rw_connectivity.csv    - copy of the connectivity matrix
```

A monitored variant has the same shape with the `_mon` name on the top,
package and crossbar (`bridge_2x3_apb_req_mon/bridge_2x3_apb_req_mon_xbar.sv`);
the adapter files keep the port names. The emitted filelist is
`rtl/filelists/<bridge>.f`. Shared modules (`axi4_subtractive_slave`, the converters, shims and monitor wrappers) are
not copied into the directory; the filelist pulls them from their home
areas.

## Related Modules

- [Signal Naming](02_signal_naming.md) - Detailed naming conventions
