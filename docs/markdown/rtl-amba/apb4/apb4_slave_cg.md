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

# apb4_slave_cg

**Module:** `apb4_slave_cg.sv`
**Base Module:** [apb4_slave](./apb4_slave.md)
**Location:** `rtl/amba/apb4/`
**Status:** Production Ready

---

## Overview

The `apb4_slave_cg` module is a clock-gated variant of [apb4_slave](./apb4_slave.md) that adds comprehensive power optimization capabilities through activity-based clock gating.

### Key Differences from Base Module

- **Activity-Based Clock Gating:** Gates `pclk` when the interface has been idle
- **Runtime Configuration:** Enable and idle threshold are input signals, not parameters
- **Gating Status Output:** `apb_clock_gating` reports when the clock is gated
- **Zero Functional Impact:** Maintains 100% functional equivalence with base module

The module is a thin wrapper: one `amba_clock_gate_ctrl` instance produces
`gated_pclk`, which feeds an otherwise unmodified `apb4_slave`. There is a
**single** gate cell — there are no separate data-path and control-path gating
domains.

All other functionality is identical to the base module. See [apb4_slave.md](./apb4_slave.md) for complete functional specification.

### When to Use the Clock-Gated Variant

**Use `apb4_slave_cg` when:**
- Power consumption is a critical concern
- Design has periods of inactivity (burst traffic patterns)
- FPGA/ASIC has integrated clock gating support
- Meeting power budgets for battery-operated systems

**Use the base module (`apb4_slave`) when:**
- Maximum performance with no power constraints
- Continuous high-activity traffic
- Simpler design with fewer configuration parameters
- Minimizing gate count is priority

---

## Parameters

In addition to all parameters from [apb4_slave](./apb4_slave.md), this module adds:

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `CG_IDLE_COUNT_WIDTH` | int | 4 | Width of the idle countdown counter; bounds the maximum programmable idle threshold |

That is the only additional parameter. Gating is not parameterized on or off, and
there are no per-domain gating parameters — both are controlled at runtime.

### Derived Parameters (do not override)

These are declared as `parameter` so the elaborator can compute them, not so callers can set them. Each defaults to an expression over the parameters above; overriding one desynchronises it from its source and the design fails to elaborate or silently mis-sizes a bus. Set the parameters they are derived FROM and leave these alone.

| Derived parameter | Default expression |
|---|---|
| `STRB_WIDTH` | `DATA_WIDTH / 8` |
| `DW` | `DATA_WIDTH` |
| `AW` | `ADDR_WIDTH` |
| `SW` | `STRB_WIDTH` |
| `PW` | `PROT_WIDTH` |
| `ICW` | `CG_IDLE_COUNT_WIDTH` |
| `CPW` | `AW + DW + SW + PW + 1` |
| `RPW` | `DW + 1` |

## Ports

In addition to all ports from [apb4_slave](./apb4_slave.md):

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| `cfg_cg_enable` | 1 | Input | Global clock-gate enable. 0 = never gate (identical to base module) |
| `cfg_cg_idle_count` | CG_IDLE_COUNT_WIDTH | Input | Idle cycles to count down before gating the clock |
| `apb_clock_gating` | 1 | Output | Asserted while the internal clock is gated |

---

## Functional Description

### Single Gating Domain

There is one `amba_clock_gate_ctrl` instance producing one gated clock, which
feeds the entire wrapped `apb4_slave`. There is no separate data-path/control-path
split.

### Wake-Up Condition

The wrapper holds the clock ungated while any of the following is true, sampled
one cycle earlier into an internal `r_wakeup` register:

```
s_apb_PSEL || s_apb_PENABLE || cmd_valid || rsp_valid
```

That is: an APB transfer selected or in its ACCESS phase, a command still
presented to the backend, or a response still pending. Gating engages
`cfg_cg_idle_count + 1` cycles after the internal wakeup deasserts, which is
`cfg_cg_idle_count + 3` cycles after all four terms go low, because APB adds two
register stages ahead of the ICG enable.

### Gating State Machine

The gate cell follows the standard three-state sequence:

```
ACTIVE ───────► IDLE_COUNT ───────► GATED
  ▲                                    │
  │                                    │
  └────────────────────────────────────┘
        (Activity Detected)

States:
- ACTIVE:     Clock enabled, monitoring activity
- IDLE_COUNT: Counting cfg_cg_idle_count cycles before gating
- GATED:      Clock disabled, waiting for activity
```

### Wake-Up Latency

Activity is registered once (AXI4, AXI5, AXI4-Lite, AXI4-Stream) or twice (APB,
APB5, AXI5-Stream) before reaching the ICG enable, which is combinational. This
wrapper registers activity into its own `r_wakeup` flop and then hands it to
`amba_clock_gate_ctrl`, which registers it again, so APB is a **two-stage**
family. The first gated-clock rising edge available to the wrapped `apb4_slave`
therefore arrives **3 cycles** after activity asserts.

`clock_gate_ctrl` itself adds no flop: `w_gate_enable` is combinational from
`wakeup` into the ICG enable, so the third cycle is the released clock edge
rather than a further register stage.

`cfg_cg_idle_count` controls how long the clock stays running *after* traffic
stops, not how long wake-up takes — a larger value means fewer gate/ungate
transitions, not slower wake-up.

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

### Aggressive Gating (Bursty Traffic)

```systemverilog
apb4_slave_cg #(
    // Base parameters (see apb4_slave.md)
    .ADDR_WIDTH          (32),
    .DATA_WIDTH          (32),
    .DEPTH               (2),
    .CG_IDLE_COUNT_WIDTH (4)
) u_cg (
    .pclk              (apb_clk),
    .presetn           (apb_resetn),

    .cfg_cg_enable     (1'b1),
    .cfg_cg_idle_count (4'd4),   // gate quickly after 4 idle cycles
    .apb_clock_gating  (cg_active),
    // ... connect signals same as base module
);
```

### Conservative Gating

```systemverilog
apb4_slave_cg #(
    .ADDR_WIDTH          (32),
    .DATA_WIDTH          (32),
    .CG_IDLE_COUNT_WIDTH (4)
) u_cg (
    .pclk              (apb_clk),
    .presetn           (apb_resetn),

    .cfg_cg_enable     (1'b1),
    .cfg_cg_idle_count (4'd15),  // wait longer; fewer gate/ungate events
    .apb_clock_gating  (cg_active),
    // ... connect signals same as base module
);
```

Note that `cfg_cg_idle_count` is bounded by `CG_IDLE_COUNT_WIDTH`. With the
default width of 4, the largest usable threshold is 15 cycles; widen the
parameter if a longer idle window is required.

### Clock Gating Disabled (Functional Verification)

```systemverilog
apb4_slave_cg #(
    .ADDR_WIDTH          (32),
    .DATA_WIDTH          (32)
) u_cg (
    .pclk              (apb_clk),
    .presetn           (apb_resetn),

    .cfg_cg_enable     (1'b0),   // never gate
    .cfg_cg_idle_count (4'd0),
    // ... connect signals same as base module
);
```

**Note:** With `cfg_cg_enable = 0`, this module is functionally identical to the base module.

---

## Design Notes

### Power Savings

Clock gating removes the switching power of the wrapped `apb4_slave` during the
gated window. The achievable saving is therefore bounded by the fraction of time
the interface is idle, and by whether the target technology maps the enable onto
a real clock-gating cell (an ASIC ICG, a Xilinx `BUFGCE`, an Intel `ALTCLKCTRL`)
rather than a data-path enable.

**No power measurements have been taken for this module in this repository.** Any
specific percentage would be a guess. If a power number is needed, run
vendor power analysis on the target device with a representative traffic
switching activity file (SAIF/VCD) and compare against `apb4_slave`.

### Gating Status Signal

| Signal | Width | Description |
|--------|-------|-------------|
| `apb_clock_gating` | 1 | Asserted while the internal clock is gated. Integrate over a window to measure the gated duty cycle |

### Synthesis Considerations

The gated clock is produced inside `amba_clock_gate_ctrl`. Whether it becomes a
true gated clock or a fan-out of clock enables is a synthesis decision:

**Xilinx:**
- Vivado typically converts the enable into `BUFGCE` or into per-flop clock enables
- Confirm which happened in the post-synthesis netlist before claiming power savings
- Verify with post-implementation power analysis

**Intel (Altera):**
- Maps to `ALTCLKCTRL`; may need explicit vendor primitive instantiation
- Check power reports for gating effectiveness

**Lattice:**
- Basic clock gating supported
- May require manual instantiation of clock enables
- Verify functionality in timing simulation

**ASIC:**
- Work with foundry to select appropriate clock gating cells
- Integrated Clock Gating (ICG) cells provide best results
- Consider hold-time implications of clock gating
- Verify power intent with UPF (Unified Power Format)

---

## Related Modules

- **[apb4_slave](./apb4_slave.md)** - Base module (non-clock-gated)
- **Power Optimization Guide:** `docs/POWER_OPTIMIZATION_GUIDE.md`
- **Clock Gating Best Practices:** `docs/CLOCK_GATING_GUIDE.md`
- **AMBA Subsystem Overview:** `docs/markdown/rtl-amba/overview.md`

---

## Testing

### Clock Gating in Simulation

**Recommendation:** Disable clock gating during functional verification:

```systemverilog
// Testbench instantiation
apb4_slave_cg dut (
    .cfg_cg_enable (1'b0),   // Disable gating for functional debug
    // ... connections
);
```

**Rationale:**
- Simpler waveforms (no clock gating events)
- Easier debug: a gated clock freezes internal state and reads like a hang

### Power Analysis Verification

For power-specific verification:

1. **Enable gating** (`cfg_cg_enable = 1`) with a realistic `cfg_cg_idle_count`
2. **Monitor `apb_clock_gating`** to verify the expected gated duty cycle
3. **Vary traffic patterns** to test gating effectiveness
4. **Check wake-up timing** meets system requirements

---

## Navigation

- **[← Back to Base Module](./apb4_slave.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
