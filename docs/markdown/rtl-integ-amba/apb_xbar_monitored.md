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


# Monitored APB Crossbar

**Module:** `apb_xbar_monitored.sv`
**Location:** `rtl/integ_amba/examples/`
**Status:** Integration example -- **does not currently elaborate**, see below

> **This module does not build.** Like its sibling it instantiates `apb_monitor`
> with the November 2025 port list, and that module has since moved to a
> `cmd_*`/`rsp_*` handshake. Tracked as AMBA-INTEG-EXAMPLES. This page records
> the intended design and interface.

## Overview

`apb_xbar_thin` with full observability: a monitor on every master port and
every slave port, each tagged with its own agent ID so a monbus consumer can
attribute traffic to a specific port rather than to the crossbar as a whole.

The example exists because per-port monitoring is where the agent-ID scheme
earns its keep. With `NUM_MASTERS + NUM_SLAVES` monitors running, "the crossbar
reported an error" is useless; "agent 0x41 reported a slave error" is
actionable.

## Module Interface

```systemverilog
module apb_xbar_monitored #(
    parameter int NUM_MASTERS = 3,
    parameter int NUM_SLAVES  = 4,
    parameter int ADDR_WIDTH  = 32,
    parameter int DATA_WIDTH  = 32,
    parameter int STRB_WIDTH  = DATA_WIDTH/8,
    parameter int MAX_TRANSACTIONS = 8,
    parameter int UNIT_ID = 0,
    parameter logic [7:0] AGENT_ID_M0 = 8'h10,  // masters 0..2
    parameter logic [7:0] AGENT_ID_M1 = 8'h11,
    parameter logic [7:0] AGENT_ID_M2 = 8'h12,
    parameter logic [7:0] AGENT_ID_S0 = 8'h40,  // slaves 0..3
    parameter logic [7:0] AGENT_ID_S1 = 8'h41,
    parameter logic [7:0] AGENT_ID_S2 = 8'h42,
    parameter logic [7:0] AGENT_ID_S3 = 8'h43
) (
    input  logic pclk,
    input  logic presetn,

    // Per-master APB slave interfaces: m0_apb_*, m1_apb_*, m2_apb_*
    // Per-slave  APB master interfaces: s0_apb_*, s1_apb_*, ...
    // (psel, penable, pwrite, pprot, paddr, pwdata, pstrb,
    //  pready, prdata, pslverr on each)

    // Aggregated monitor output
    output logic        monbus_valid,
    input  logic        monbus_ready,
    output logic [63:0] monbus_data
);
```

The per-port APB signals are flattened rather than packed -- `m0_apb_psel`,
`m1_apb_psel`, and so on -- so `NUM_MASTERS` and `NUM_SLAVES` are not freely
parameterizable in the current source despite being parameters: the port list
names three masters and four slaves explicitly.

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `NUM_MASTERS` | 3 | Master ports. The flattened port list fixes this at 3 today |
| `NUM_SLAVES` | 4 | Slave ports. Likewise fixed at 4 |
| `ADDR_WIDTH` | 32 | APB address width |
| `DATA_WIDTH` | 32 | APB data width |
| `STRB_WIDTH` | `DATA_WIDTH/8` | Write strobes |
| `MAX_TRANSACTIONS` | 8 | Per-monitor transaction table depth |
| `UNIT_ID` | 0 | Identifies this crossbar on the monbus |
| `AGENT_ID_M0..M2` | `8'h10..0x12` | Agent ID per master port |
| `AGENT_ID_S0..S3` | `8'h40..0x43` | Agent ID per slave port |

The `0x10` / `0x40` split is a convention, not a requirement: masters in the
`0x1x` range, slaves in the `0x4x` range, so the range alone tells a consumer
which side of the fabric a packet came from.

## Functional Description

Traffic passes through `apb_xbar_thin` unchanged -- the crossbar is not modified
by being monitored. Around it:

- each master port's traffic is observed by an `apb_monitor` tagged `AGENT_ID_Mn`
- each slave port's traffic is observed by an `apb_monitor` tagged `AGENT_ID_Sn`
- all seven monitor buses are merged by `arbiter_round_robin` onto one 64-bit
  `monbus_data` output

Round-robin rather than priority matters here for the same reason as in the
peripheral subsystem: a master that errors continuously must not lock the other
ports out of the monitor bus, or you lose the evidence that would explain it.

## What is wrong with the RTL today

The monitors are wired with raw APB (`pclk`, `presetn`, `psel`, `penable`,
`pwrite`, `paddr`, `pwdata`, `pready`, `prdata`, `pslverr`).
[apb_monitor](../rtl-amba/monitor/apb_monitor.md) takes `aclk`/`aresetn` plus a
`cmd_*`/`rsp_*` handshake and nothing else.

This example has raw APB in hand -- `apb_xbar_thin` is raw APB on both sides
(`s_apb_psel` / `m_apb_psel`) -- so it needs a bridge per monitored port to
produce the handshake before a monitor can see anything. That is a structural
change, not a rename: see the pattern in [overview.md](overview.md).

## Design Considerations

- **Monitor count scales with ports.** Seven monitors at `MAX_TRANSACTIONS=8`
  is a real area cost. Monitor the ports you actually debug, not all of them by
  reflex.
- **Layering.** `apb_xbar_thin` lives in `projects/components/apb_xbar`, so this
  module under `rtl/` depends on a project area. That direction is backwards and
  is noted in `rtl/integ_amba/filelists/apb_xbar_monitored.f`.

## Testing

None, in `val/` or anywhere else. See the note on
[apb_peripheral_subsystem](apb_peripheral_subsystem.md#testing).

## Related Modules

- [apb_monitor](../rtl-amba/monitor/apb_monitor.md) - one per monitored port
- [apb_slave](../rtl-amba/apb/apb_slave.md) / [apb_master](../rtl-amba/apb/apb_master.md) - the bridges that produce the handshake
- [arbiter_round_robin](../rtl-common/arbiter_round_robin.md) - merges the monitor buses
- [apb_peripheral_subsystem](apb_peripheral_subsystem.md) - the same pattern, smaller

## Navigation

- **[Back to rtl-integ-amba Index](index.md)**
- **[Back to Main Documentation Index](../index.md)**
