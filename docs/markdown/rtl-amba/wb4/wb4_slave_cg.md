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

# wb4_slave_cg

## Overview

The **clock-gated variant** of [wb4_slave](wb4_slave.md): an
`amba_clock_gate_ctrl` instance produces a gated clock that feeds an
otherwise unmodified `wb4_slave`. Functionally identical to the base
module; `cfg_cg_enable = 0` gives the base behaviour exactly. See the
Shared book's [Clock-Gated Variants
Guide](../shared/clock_gated_variants.md) and
[amba_clock_gate_ctrl](../shared/amba_clock_gate_ctrl.md).

## Parameters

In addition to all `wb4_slave` parameters:

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| CG_IDLE_COUNT_WIDTH | int | 4 | Width of the idle countdown; bounds the programmable idle threshold |

## Ports

`wb4_slave`'s ports plus `cfg_cg_enable`, `cfg_cg_idle_count`,
`cg_gating` and `cg_idle`, as on [wb4_master_cg](wb4_master_cg.md):

| Port | Direction | Description |
|---|---|---|
| `cfg_cg_enable` | in | Global clock-gate enable |
| `cfg_cg_idle_count [CG_IDLE_COUNT_WIDTH-1:0]` | in | Idle clocks before the clock is gated |
| `cg_gating` | out | Clock is gated now |
| `cg_idle` | out | Nothing pending (the controller's idle indicator) |

## Functional Description

### Wake-Up Terms

| Term | Why |
|---|---|
| `s_wb_CYC` | a bus cycle open: requests arriving, terminations due |
| `rsp_valid` | a FUB response offered |
| command pending on the output | a request waiting for the FUB |

`cmd_ready` is deliberately absent.

### Masks for the Wake-Latency Overlap

A stopped clock cannot register an accept, and the wake takes a clock or
two after the activity appears. Three signals are therefore masked while
`cg_gating` is high:

| Signal | Masked to | Why |
|---|---|---|
| `cmd_valid` (to the FUB) | low | a consumer must not retire a command the slave cannot see leave |
| `rsp_ready` (to the FUB) | low | a FUB must not have a response taken by a stopped clock |
| `s_wb_STALL` (to the master) | **high** | in pipelined mode an accept is `STB && !STALL` in the master's clock; a frozen "room" would let the master move on from a request the slave never sampled |

`STALL` stays high until the clock runs, and the master holds its request
while stalled (a B4 rule), so nothing is lost and nothing is duplicated.
Classic mode holds the request until termination and needs no `STALL`,
but is masked the same way.

## Design Notes

- Formal: `formal/amba/wb4_slave_cg/` proves the wrapper's glue contract
  with a clock-enable model of the gate cell (a derived clock is not
  provable in the repo's single-clock flow; the stopped clock itself is
  the cocotb test's job): reset state, gating clears by the third clock
  of an open cycle, no gating while a command is pending or with the
  enable low, no termination and no FUB handshake while gated, `STALL`
  high while gated; covers gating, an ungated accept, a termination and
  re-gating.
- The wake term is combinational into the controller (which registers it
  once), not a second local flop as in `apb4_slave_cg`; see
  `formal/amba/apb4_slave_cg/KNOWN_BUG.md` for the latency that flop
  adds.

## Related Modules

- [wb4_slave](wb4_slave.md), [wb4_master_cg](wb4_master_cg.md)
- [apb4_slave_cg](../apb4/apb4_slave_cg.md) — the same wrapper over APB

## Testing

`val/amba/test_wb4_slave_cg.py` runs the `wb4_slave` phases with gating
enabled and the same three checks as the master's test.
