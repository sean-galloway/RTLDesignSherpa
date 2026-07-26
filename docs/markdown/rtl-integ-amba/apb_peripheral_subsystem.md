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


# Monitored APB Peripheral Subsystem

**Module:** `apb_peripheral_subsystem.sv`
**Location:** `rtl/integ_amba/examples/`
**Status:** Integration example -- **does not currently elaborate**, see below

> **This module does not build.** It instantiates `apb_monitor` with the port
> list that module had in November 2025; `apb_monitor` has since moved to a
> `cmd_*`/`rsp_*` handshake. Fixing or retiring it is AMBA-INTEG-EXAMPLES. This
> page documents the intended design so the decision can be made from something
> other than 340 lines of stale RTL.

## Overview

One APB master fanned out to three peripherals -- a register file, a timer and a
GPIO block -- with a monitor per peripheral and the three monitor buses
arbitrated onto a single 64-bit monbus output.

The point of the example is the monitoring topology, not the peripherals: each
target gets its own `AGENT_ID` so a monbus consumer can attribute a transaction
or an error to the peripheral that produced it, and the per-peripheral buses are
merged by a round-robin arbiter rather than by priority, so a chatty peripheral
cannot starve a quiet one.

## Module Interface

```systemverilog
module apb_peripheral_subsystem #(
    parameter int ADDR_WIDTH = 16,   // 64KB address space
    parameter int DATA_WIDTH = 32,
    parameter int STRB_WIDTH = 4,
    parameter int MAX_TRANSACTIONS = 4,
    parameter int UNIT_ID = 0,
    parameter logic [7:0] AGENT_ID_REGFILE = 8'h50,
    parameter logic [7:0] AGENT_ID_TIMER   = 8'h51,
    parameter logic [7:0] AGENT_ID_GPIO    = 8'h52
) (
    input  logic pclk,
    input  logic presetn,

    // Single APB master interface (from CPU or bridge)
    input  logic                  apb_psel,
    input  logic                  apb_penable,
    input  logic                  apb_pwrite,
    input  logic [2:0]            apb_pprot,
    input  logic [ADDR_WIDTH-1:0] apb_paddr,
    input  logic [DATA_WIDTH-1:0] apb_pwdata,
    input  logic [STRB_WIDTH-1:0] apb_pstrb,
    output logic                  apb_pready,
    output logic [DATA_WIDTH-1:0] apb_prdata,
    output logic                  apb_pslverr,

    // Aggregated monitor output
    output logic        monbus_valid,
    input  logic        monbus_ready,
    output logic [63:0] monbus_data,

    // Configuration
    input logic cfg_error_enable,
    input logic cfg_compl_enable
);
```

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `ADDR_WIDTH` | 16 | APB address width; 16 gives the 64KB space the address decode assumes |
| `DATA_WIDTH` | 32 | APB data width |
| `STRB_WIDTH` | 4 | Write strobes, `DATA_WIDTH/8` |
| `MAX_TRANSACTIONS` | 4 | Per-monitor transaction table depth. Small is fine here: APB has no bursts and these peripherals are single-outstanding |
| `UNIT_ID` | 0 | Identifies this subsystem on the monbus |
| `AGENT_ID_REGFILE` | `8'h50` | Monbus agent ID for the register file |
| `AGENT_ID_TIMER` | `8'h51` | Monbus agent ID for the timer |
| `AGENT_ID_GPIO` | `8'h52` | Monbus agent ID for the GPIO block |

Agent IDs are sequential by intent -- a consumer decoding `0x50..0x52` knows it
is looking at this subsystem without a lookup table.

## Functional Description

Three things happen here, and only the third is interesting:

1. **Address decode.** The incoming APB transaction is routed to one of the
   three peripherals by address range.
2. **Peripheral access.** Each peripheral completes the transaction and drives
   `pready` / `prdata` / `pslverr` back.
3. **Monitoring.** Each peripheral's traffic is observed by its own
   `apb_monitor`, tagged with that peripheral's `AGENT_ID`, and the three
   resulting monbus streams are merged by `arbiter_round_robin` onto the single
   `monbus_valid` / `monbus_data` output.

`cfg_error_enable` and `cfg_compl_enable` gate which packet classes the monitors
emit. Enabling completion packets on every peripheral at once produces
considerably more monbus traffic than error packets alone -- see the monitor
configuration guidance in [rtl-amba](../rtl-amba/index.md).

## What is wrong with the RTL today

The monitors are instantiated with `pclk`, `presetn`, `psel`, `penable`,
`pwrite`, `paddr`, `pwdata`, `pready`, `prdata` and `pslverr`.
[apb_monitor](../rtl-amba/monitor/apb_monitor.md) now takes `aclk`, `aresetn`
and a handshake: `cmd_valid` / `cmd_ready` with `cmd_pwrite` / `cmd_paddr` /
`cmd_pwdata` / `cmd_pstrb` / `cmd_pprot`, then `rsp_valid` / `rsp_ready` with
`rsp_prdata` / `rsp_pslverr`.

A monitor observes the **translated** side of a bridge, never the wire. To make
this example work, each peripheral needs an [apb_slave](../rtl-amba/apb/apb_slave.md)
(or `apb_slave_cg`) between the APB pins and the peripheral logic, and the
monitor taps that bridge's `cmd_*`/`rsp_*` signals. See the pattern in
[overview.md](overview.md).

## Testing

None. There is no test for this module anywhere in `val/`, which is why the
interface drift went unnoticed for nine months. If it is rewritten rather than
retired, a smoke test under `val/integ_amba/` taking its sources from
`rtl/integ_amba/filelists/apb_peripheral_subsystem.f` is the minimum that keeps
it from rotting again.

## Related Modules

- [apb_monitor](../rtl-amba/monitor/apb_monitor.md) - the observer, one per peripheral
- [apb_slave](../rtl-amba/apb/apb_slave.md) - the bridge that produces the handshake a monitor needs
- [arbiter_round_robin](../rtl-common/arbiter_round_robin.md) - merges the three monitor buses
- [apb_xbar_monitored](apb_xbar_monitored.md) - the same idea at crossbar scale

## Navigation

- **[Back to rtl-integ-amba Index](index.md)**
- **[Back to Main Documentation Index](../index.md)**
