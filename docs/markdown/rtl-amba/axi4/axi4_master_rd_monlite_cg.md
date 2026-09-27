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

# AXI4 Master Read with Lite Monitor, Clock-Gated

**Module:** `axi4_master_rd_monlite_cg.sv`
**Base Module:** [axi4_master_rd_monlite](axi4_master_rd_monlite.md)
**Location:** `rtl/amba/axi4/`
**Status:** Production Ready (amba/monitor-lite TASK-001, 2026-09-26)

---

## Overview

`axi4_master_rd_monlite_cg` is [`axi4_master_rd_monlite`](axi4_master_rd_monlite.md) behind one `amba_clock_gate_ctrl`: the
clock-gated sibling of the lite-monitor wrapper, built exactly as
[`axi4_master_rd_mon_cg`](axi4_master_rd_mon_cg.md) is built around `axi4_master_rd_mon`. The activity term, the
request-side ready masks and the monitor-bus liveness terms are the `axi4_master_rd_mon_cg`
ones verbatim, so the six-phase structural test that gates the full-monitor
wrappers gates this one too.

Everything the lite wrapper offers is here, passed through by name: the same
core, the same taps, the same 128-bit packets on the same monbus with the same
`UNIT_ID`/`AGENT_ID`, the address-range checker behind `N_ADDR_RANGES`, the
latency threshold, drop-and-count instead of `block_ready`. Four pins are
appended for the clock gate.

### When to use it

Use `axi4_master_rd_monlite_cg` when the port is idle for long stretches and the monitor's clock
is worth stopping; use [`axi4_master_rd_monlite`](axi4_master_rd_monlite.md) when it is not, and
[`axi4_master_rd_mon_cg`](axi4_master_rd_mon_cg.md) when the full monitor's perf window, debug packets or
filters are needed on a gated port.

---

## Parameters

All of [`axi4_master_rd_monlite`](axi4_master_rd_monlite.md)'s parameters, plus:

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `CG_IDLE_COUNT_WIDTH` | int | `4` | Width of the idle countdown, sizing `cfg_cg_idle_count` |

---

## Ports

All of [`axi4_master_rd_monlite`](axi4_master_rd_monlite.md)'s ports, plus:

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `cfg_cg_enable` | input | 1 | Enable clock gating |
| `cfg_cg_idle_count` | input | `CG_IDLE_COUNT_WIDTH` | Idle cycles before the clock stops |
| `cg_gating` | output | 1 | Gated clock is stopped |
| `cg_idle` | output | 1 | No activity observed |

---

## Functional Description

One `amba_clock_gate_ctrl` gates the whole inner `axi4_master_rd_monlite`. Activity is
derived from VALID signals and outstanding work only, never from a peer's
READY, so a consumer that parks its response-ready high while idle does not
defeat gating:

- `user_valid` = `fub_axi_arvalid || fub_axi_rvalid || int_busy || w_monbus_valid || (|active_transactions)`
- `axi_valid` = `m_axi_arvalid || m_axi_rvalid`

While `cg_gating` is high the request-side readys are masked, so nothing is
accepted with the clock stopped:

| Port | While gated |
|------|-------------|
| `fub_axi_arready` | held at 0 while `cg_gating` is high |
| `m_axi_rready` | held at 0 while `cg_gating` is high |

A packet parked on the monitor bus and any occupied table entry hold the
block awake so the lite can retire the handshake, and the external
`monbus_valid` is masked by `!cg_gating` so the consumer never sees a valid a
stopped lite could not retire (the TASK-070 liveness terms). The lite's
4-entry output queue holds a parked packet across the wait.

---

## Related Modules

- [`axi4_master_rd_monlite`](axi4_master_rd_monlite.md) -- the lite wrapper this gates
- [`axi4_master_rd_mon_cg`](axi4_master_rd_mon_cg.md) -- the full-monitor clock-gated sibling whose gating logic this reuses
- [axi_monitor_lite](../monitor/axi_monitor_lite.md) -- the monitor itself

---

## Testing

`val/amba/monitor-lite/test_axi4_master_rd_monlite_cg.py` runs the same integration scenarios as
`val/amba/test_axi4_master_rd_mon_cg.py` with clock gating enabled underneath the traffic;
`val/amba/monitor-lite/test_monlite_cg_gating.py` asserts the six gating
phases (stop, ready-high immunity, wake, transfer integrity across gate and
ungate, a beat held under back-pressure, monitor-bus liveness) on every
`*_monlite_cg` wrapper at two idle counts.

```bash
source env_python
make -C val/amba/monitor-lite run-axi4_master_rd_monlite_cg-gate
```

---

**Last Updated:** 2026-09-26

---

## Navigation

- **[← Back to Monitor Index](../_book_monitor_index.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
