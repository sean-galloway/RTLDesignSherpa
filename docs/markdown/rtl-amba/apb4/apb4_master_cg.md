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

# apb4_master_cg

**Module:** `apb4_master_cg.sv`
**Base Module:** [apb4_master](./apb4_master.md)
**Location:** `rtl/amba/apb4/`
**Status:** Production Ready

---

## Overview

This is the **clock-gated variant** of [apb4_master](./apb4_master.md). It adds power optimization through activity-based clock gating, and it's a thin wrapper: an `amba_clock_gate_ctrl` instance produces `gated_pclk`, which feeds an otherwise unmodified `apb4_master`.

- **Same Functionality:** 100% equivalent to base module
- **Runtime Control:** Gating is enabled and tuned by input signals, not parameters
- **Observable:** `cg_gating` output reports when the clock is gated
- **Bypassable:** Tie `cfg_cg_enable = 0` for behaviour identical to the base module

**For the clock-gating architecture and the underlying gate cell, see:**

**→ [Clock-Gated Variants Guide](../shared/clock_gated_variants.md)** and
**→ [amba_clock_gate_ctrl](../shared/amba_clock_gate_ctrl.md)**

Both live in the Shared book, which is published as a separate PDF. Take the
parameter and port names for this module from the tables below, not from the
generic guide.

---

## Parameters

In addition to all [apb4_master](./apb4_master.md) parameters:

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `CG_IDLE_COUNT_WIDTH` | int | 4 | Width of the idle countdown counter; bounds the maximum programmable idle threshold |

There is no `ENABLE_CLOCK_GATING` parameter and no per-domain `CG_GATE_*`
parameters on this module — gating is controlled at runtime through the
configuration inputs below.

### Derived Parameters (do not override)

These are declared as `parameter` so the elaborator can compute them, not so callers can set them. Each defaults to an expression over the parameters above; overriding one desynchronises it from its source and the design fails to elaborate or silently mis-sizes a bus. Set the parameters they are derived FROM and leave these alone.

| Derived parameter | Default expression |
|---|---|
| `STRB_WIDTH` | `DATA_WIDTH / 8` |
| `AW` | `ADDR_WIDTH` |
| `DW` | `DATA_WIDTH` |
| `SW` | `STRB_WIDTH` |
| `PW` | `PROT_WIDTH` |
| `ICW` | `CG_IDLE_COUNT_WIDTH` |
| `CPW` | `AW + DW + SW + PW + 1` |
| `RPW` | `DW + 1` |

## Ports

In addition to all [apb4_master](./apb4_master.md) ports:

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| `cfg_cg_enable` | 1 | Input | Global clock-gate enable. 0 = never gate (identical to base module) |
| `cfg_cg_idle_count` | CG_IDLE_COUNT_WIDTH | Input | Idle cycles to count down before gating the clock |
| `cg_gating` | 1 | Output | Asserted while the internal clock is gated |
| `cg_idle` | Out | 1 | Activity terms quiet (registered `~wakeup`). |

## Functional Description

### Wake-Up Condition

The wrapper holds the clock ungated while any of the following is true, sampled
one cycle earlier into an internal `r_wakeup` register:

```
cmd_valid || rsp_valid || m_apb_PSEL || m_apb_PENABLE
```

That is: a pending command, a pending response, or an APB transfer in progress.
Gating engages `cfg_cg_idle_count + 1` cycles after the internal wakeup
deasserts, which is `cfg_cg_idle_count + 3` cycles after all four terms go low,
because APB adds two register stages ahead of the ICG enable.

### Wake-Up Latency

Activity is registered once (AXI4, AXI5, AXI4-Lite, AXI4-Stream) or twice (APB,
APB5, AXI5-Stream) before reaching the ICG enable, which is combinational. This
wrapper registers activity into its own `r_wakeup` flop and then hands it to
`amba_clock_gate_ctrl`, which registers it again, so APB is a **two-stage**
family. The first gated-clock rising edge available to the wrapped `apb4_master`
therefore arrives **3 cycles** after activity asserts.

---

## Timing Characteristics

This module is **purely combinational** -- it contains no `always_ff` and no
latch, so it holds no state and adds no clock cycles. Its outputs settle a
propagation delay after its inputs, and it introduces no latency into a
pipeline that instantiates it.

Timing closure is therefore a question of the surrounding logic's slack, not of
this module's cycle count. No synthesis figures are quoted; none have been
measured.

---

## Usage Examples
```systemverilog
apb4_master_cg #(
    // Base module parameters (see apb4_master.md)
    .ADDR_WIDTH          (32),
    .DATA_WIDTH          (32),
    .CMD_DEPTH           (6),
    .RSP_DEPTH           (6),

    // Clock gating
    .CG_IDLE_COUNT_WIDTH (4)
) u_cg (
    .pclk              (apb_clk),
    .presetn           (apb_resetn),

    // Clock gating control
    .cfg_cg_enable     (1'b1),
    .cfg_cg_idle_count (4'd8),
    .cg_gating  (apb_cg_active),

    // ... all other ports same as apb4_master
);
```

**Simulation note:** set `cfg_cg_enable = 0` when debugging waveforms. A gated
clock makes the internal state appear frozen and is easy to misread as a hang.

---

## Design Notes

**A peer's READY must never enter the activity term.** A consumer that parks
its response-ready high while idle is behaving correctly; folding that signal
into `user_valid` pins this block permanently awake and defeats gating
entirely -- silently, because function is unaffected. Ten wrappers in this
repository shipped that way and nothing failed until someone measured.
`val/amba/test_cg_peer_ready.py` parks the peer READY high, holds every VALID
low, and requires `cg_gating`. Canonical rule:
`vault/handbook/design/clock-gating-activity-terms.md`.

**`cfg_cg_enable` is not a kill switch.** It arms gating and reaches
`amba_clock_gate_ctrl` only; the datapath and any monitor enables are forwarded
untouched. With it low the clock free-runs and this module behaves exactly like
its base.

**Gating latency.** The clock stops `cfg_cg_idle_count` + 2 cycles after the
last bus activity -- the idle counter, plus one for the `r_wakeup` flop. Size
the idle count against your traffic's inter-burst gap: too small and the block
wakes constantly, too large and it never gates.

**Cost.** Five flops: `r_wakeup` plus `r_idle_counter` at `IDLE_CNTR_WIDTH`,
scaling as 1 + `CG_IDLE_COUNT_WIDTH`. The ICG itself is a latch or BUFGCE, not
fabric flops.

---

## Related Modules

- **Base Module Functionality:** [apb4_master.md](./apb4_master.md)
- **Clock Gating Guide:** [clock_gated_variants.md](../shared/clock_gated_variants.md)
- **Detailed CG Examples:**
  - [axi4_master_rd_mon_cg.md](../axi4/axi4_master_rd_mon_cg.md) (AXI4 monitor)
  - [axil4_master_rd_mon_cg.md](../axil4/axil4_master_rd_mon_cg.md) (AXIL4 monitor)
  - [apb4_slave_cg.md](apb4_slave_cg.md) (APB interface)

---

## Testing

**No test coverage.** There is no
`val/**/test_apb4_master_cg.py`, and no module that instantiates this one has a testbench either, so nothing in the repository exercises it.

Treat any behaviour described on this page as unverified by simulation.

---

## Navigation

- **[← Back to APB Index](./README.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
