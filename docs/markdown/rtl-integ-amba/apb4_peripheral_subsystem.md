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

**Module:** `apb4_peripheral_subsystem.sv`
**Location:** `rtl/integ_amba/examples/`
**Status:** Integration example -- elaborates clean; no test yet

## Overview

One APB master fanned out to three peripherals -- a register file, a timer and a
GPIO block -- with a monitor per peripheral and the three monitor buses
arbitrated onto a single monitor-packet output.

The point of the example is the monitoring topology, not the peripherals: each
target gets its own `AGENT_ID` so a monbus consumer can attribute a transaction
or an error to the peripheral that produced it, and the per-peripheral buses are
merged by a round-robin arbiter rather than by priority, so a chatty peripheral
cannot starve a quiet one.

## Module Interface

```systemverilog
module apb4_peripheral_subsystem #(
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
    output logic                                monbus_valid,
    input  logic                                monbus_ready,
    output monitor_common_pkg::monitor_packet_t monbus_packet,

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
   `apb4_monitor`, tagged with that peripheral's `AGENT_ID`, and the three
   resulting monbus streams are merged by `arbiter_round_robin` onto the single
   `monbus_valid` / `monbus_packet` output.

`cfg_error_enable` drives each monitor's `cfg_error_enable` and
`cfg_slverr_enable`. `cfg_compl_enable` is wired to the monitor's
`cfg_perf_enable`, so despite the name it enables PERFORMANCE packets, not
completion packets -- `apb4_monitor` has no completion-packet control. Enabling
it on every peripheral at once produces considerably more monbus traffic than
errors alone. Every other monitor knob (timeout, protocol, latency, throughput,
debug, address-range checking) is tied off in this example to keep it readable;
see [apb4_monitor](../rtl-amba/apb4/apb4_monitor.md) for the full set.

## How the monitors are attached

Each peripheral's raw APB is converted to the handshake `apb4_monitor` expects:

```systemverilog
assign regfile_xfer = regfile_psel && regfile_penable && regfile_pready;
```

That single strobe drives both `cmd_valid` and `rsp_valid`, because APB carries
one outstanding transaction and completes in the ACCESS phase -- command and
response are accepted in the same cycle. `cmd_ready` and `rsp_ready` are tied
high here since none of these peripherals stall; a peripheral that can stall
would drive them from its own backpressure. Nothing is registered, so the tap
adds no cycle to the peripheral path.

## Testing

None. There is no test for this module anywhere in `val/`, which is why the
interface drift went unnoticed for nine months. If it is rewritten rather than
retired, a smoke test under `val/integ_amba/` taking its sources from
`rtl/integ_amba/filelists/apb4_peripheral_subsystem.f` is the minimum that keeps
it from rotting again.

## Related Modules

- [apb4_monitor](../rtl-amba/apb4/apb4_monitor.md) - the observer, one per peripheral
- [apb4_slave](../rtl-amba/apb4/apb4_slave.md) - the bridge that produces the handshake a monitor needs
- [arbiter_round_robin](../rtl-common/arbiter_round_robin.md) - merges the three monitor buses
- [apb4_xbar_monitored](apb4_xbar_monitored.md) - the same idea at crossbar scale

## Navigation

- **[Back to rtl-integ-amba Index](index.md)**
- **[Back to Main Documentation Index](../index.md)**
