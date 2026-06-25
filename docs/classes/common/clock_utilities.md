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

# Clock Utilities — Class Overview

**Category:** Clocking / power
**Scope:** `clock_divider.sv`, `clock_gate_ctrl.sv`, `clock_pulse.sv`, `icg.sv`, `debounce.sv` (5 modules)
**Status:** Production-ready

---

## What this is

The clock-side helpers: a multi-tap counter-based clock divider, a latch-based integrated clock-gate cell (`icg`), an automatic idle-detect clock-gating controller built on top of it, a configurable periodic pulse generator, and a sample-based input debouncer for mechanical switches.

## Why use this class

Power-aware designs need clock gating (`icg` + `clock_gate_ctrl`). Slow domains and debug needs benefit from a phase-aligned divider. Periodic timing — heartbeats, sampling triggers, refresh intervals — comes from `clock_pulse`. Mechanical button inputs need `debounce` before they enter synchronous logic. These are the small but easy-to-get-wrong primitives that keep design-rule checks happy.

## Members

| Module | One-line role | When to pick |
|---|---|---|
| [`icg.sv`](../../../rtl/common/icg.sv) | Latch-based integrated clock-gate cell | Leaf cell — wrap a clock with an enable |
| [`clock_gate_ctrl.sv`](../../../rtl/common/clock_gate_ctrl.sv) | Idle-detect controller wrapping `icg`, with timeout + wake | Automatic gating when a block is idle |
| [`clock_divider.sv`](../../../rtl/common/clock_divider.sv) | Multi-tap divided-clock generator from a shared counter | Testbench/debug clocks, slow non-critical domains |
| [`clock_pulse.sv`](../../../rtl/common/clock_pulse.sv) | Periodic single-cycle pulse every `WIDTH` clocks | Heartbeats, sampling triggers, refresh strobes |
| [`debounce.sv`](../../../rtl/common/debounce.sv) | Sample-and-hold debouncer for noisy inputs | Mechanical switches, button inputs |

## Picking guide

For ASIC-style clock gating, instantiate `icg` directly inside generated logic, or use `clock_gate_ctrl` when you want automatic gating with an idle counter and wake path. Use `clock_pulse` whenever you need a known-period strobe rather than rolling a counter+compare yourself. Use `clock_divider` only for testbenches, debug outputs, or non-functional clocks — for any real functional clock, go through a PLL/MMCM/clock manager primitive instead (this is called out explicitly in the `clock_divider` per-module doc). Use `debounce` on every mechanical input before it touches synchronous logic.

## Tests

[`val/common/`](../../../val/common/) — pytest + CocoTB suite. Naming: `test_clock_*.py`, `test_icg.py`, `test_debounce.py`.

## Full per-module specs

[`docs/markdown/RTLCommon/`](../../markdown/RTLCommon/) — one `.md` per module. Use those for parameter descriptions, port lists, and timing diagrams.

## Source

[`rtl/common/`](../../../rtl/common/) (`clock_*.sv`, `icg.sv`, `debounce.sv`)

---

## Navigation

- **[← Back to RTL Design Sherpa README](../../../README.md)**
- **[← Browse by Class index](../../../README.md#browse-by-class)**
- **[Main Documentation Index](../../DOCUMENTATION_INDEX.md)**
- **[Common Library per-module specs](../../markdown/RTLCommon/index.md)**
