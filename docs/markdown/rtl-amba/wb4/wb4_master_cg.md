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

# wb4_master_cg

## Overview

The **clock-gated variant** of [wb4_master](wb4_master.md): an
`amba_clock_gate_ctrl` instance produces a gated clock that feeds an
otherwise unmodified `wb4_master`. Functionally identical to the base
module; gating is enabled and tuned by input signals, not parameters, and
`cfg_cg_enable = 0` gives the base behaviour exactly. See the Shared book's
[Clock-Gated Variants Guide](../shared/clock_gated_variants.md) and
[amba_clock_gate_ctrl](../shared/amba_clock_gate_ctrl.md) for the
architecture and the gate cell.

## Parameters

In addition to all `wb4_master` parameters:

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| CG_IDLE_COUNT_WIDTH | int | 4 | Width of the idle countdown; bounds the programmable idle threshold |

## Ports

`wb4_master`'s ports plus:

| Port | Direction | Description |
|---|---|---|
| `cfg_cg_enable` | in | Global clock-gate enable |
| `cfg_cg_idle_count [ICW-1:0]` | in | Idle clocks before the clock is gated |
| `cg_gating` | out | Clock is gated now |
| `cg_idle` | out | Nothing pending (the controller's idle indicator) |

## Functional Description

### Wake-Up Terms

The registered wake term follows the family rule (peer VALIDs and every
place work can be pending, never a peer READY):

| Term | Why |
|---|---|
| `cmd_valid` | a FUB command offered |
| response pending on the output | a termination waiting for the FUB |
| `m_wb_CYC` | a bus cycle open: requests queued, terminations due |

`rsp_ready` is deliberately absent: a FUB that parks its ready high while
idle would otherwise hold the clock on forever.

### Masks for the Wake-Latency Overlap

Gating can engage on the same edge pending work appears, and the wake
takes a clock or two. The `rsp_valid` and the `cmd_ready` seen by the FUB
are both held low while `cg_gating` is high, so a FUB never has a command
taken, or a response retired, by a stopped clock. The masks only defer;
once the pending term is high gating cannot engage, so a visible valid is
never truncated. The bus side needs no mask: `CYC`/`STB` come from
registered state that is idle whenever the clock may stop, and a slave
terminates only inside a cycle.

## Notes

- Formal: `formal/amba/wb4_master_cg/` proves the wrapper's glue contract
  with a clock-enable model of the gate cell (a derived clock is not
  provable in the repo's single-clock flow; the stopped clock itself is the
  cocotb test's job): reset state, no gating while a cycle is open on the
  bus or a response is visible, no gating with the enable low, `cmd_ready`
  low while gated, and a command offered wakes the clock by its third
  clock; covers gating, an ungated transfer, a response handed back and
  re-gating.
- The wake term is combinational into the controller (which registers it
  once), not a second local flop as in `apb4_master_cg`; see
  `formal/amba/apb4_slave_cg/KNOWN_BUG.md` for the latency that flop adds.

## Related

- [wb4_master](wb4_master.md), [wb4_slave_cg](wb4_slave_cg.md)
- [apb4_master_cg](../apb4/apb4_master_cg.md) - the same wrapper over APB

## Test

`val/amba/test_wb4_master_cg.py` runs the `wb4_master` phases with gating
enabled and checks, every clock, that the clock is never gated while a
cycle is open, that the clock does gate after each phase drains, and that
it never gates with the enable low.
