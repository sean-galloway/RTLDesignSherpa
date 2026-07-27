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
**Status:** Integration example -- elaborates clean; no test yet

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
module apb_xbar_monitored
    import monitor_common_pkg::*;
#(
    parameter int NUM_MASTERS = 3,
    parameter int NUM_SLAVES  = 4,
    parameter int ADDR_WIDTH  = 32,
    parameter int DATA_WIDTH  = 32,
    parameter int STRB_WIDTH  = DATA_WIDTH/8,
    parameter int MAX_TRANSACTIONS = 8,
    parameter int UNIT_ID = 0,
    // Agent IDs are BASE + port index, so there are two bases rather than one
    // parameter per port.
    parameter logic [7:0] AGENT_ID_M_BASE = 8'h10,  // masters: 0x10, 0x11, 0x12
    parameter logic [7:0] AGENT_ID_S_BASE = 8'h40   // slaves:  0x40..0x43
) (
    input  logic pclk,
    input  logic presetn,

    // Per-master APB slave interfaces: m0_apb_*, m1_apb_*, m2_apb_*
    // Per-slave  APB master interfaces: s0_apb_*, s1_apb_*, ...

    // Aggregated monitor output
    output logic                                monbus_valid,
    input  logic                                monbus_ready,
    output monitor_common_pkg::monitor_packet_t monbus_packet,

    // Monitor configuration (applied to every port monitor)
    input  logic cfg_error_enable,    // error + slave-error packets
    input  logic cfg_timeout_enable,  // timeout detection
    input  logic cfg_perf_enable      // performance packets
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
| `AGENT_ID_M_BASE` | `8'h10` | Master 0's agent ID; master *n* gets base + n |
| `AGENT_ID_S_BASE` | `8'h40` | Slave 0's agent ID; slave *n* gets base + n |

There is deliberately no per-port agent-ID parameter. The generate loops compute
`BASE + index`, so earlier per-port parameters could be overridden with no
effect -- a parameter that cannot change behaviour reads as configurable and is
not.

The `0x10` / `0x40` split is a convention, not a requirement: masters in the
`0x1x` range, slaves in the `0x4x` range, so the range alone tells a consumer
which side of the fabric a packet came from.

## Functional Description

Traffic passes through `apb_xbar_thin` unchanged -- the crossbar is not modified
by being monitored. Around it:

- each master port's traffic is observed by an `apb_monitor` tagged `AGENT_ID_M_BASE + n`
- each slave port's traffic is observed by an `apb_monitor` tagged `AGENT_ID_S_BASE + n`
- all seven monitor buses are merged by `arbiter_round_robin` onto one
  `monbus_packet` output

Round-robin rather than priority matters here for the same reason as in the
peripheral subsystem: a master that errors continuously must not lock the other
ports out of the monitor bus, or you lose the evidence that would explain it.

## How the monitors are attached

`apb_xbar_thin` is raw APB on both sides, so each monitored port converts the
bus phases into the handshake `apb_monitor` takes:

```systemverilog
assign m_xfer[mi] = xbar_m_psel[mi] && xbar_m_penable[mi] && xbar_m_pready[mi];
assign s_xfer[si] = xbar_s_psel[si] && xbar_s_penable[si] && xbar_s_pready[si];
```

One strobe drives both `cmd_valid` and `rsp_valid` per port: APB is
single-outstanding and completes in the ACCESS phase, so command and response
are accepted together. The taps are combinational -- the crossbar's timing is
unchanged by being monitored.

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
