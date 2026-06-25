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

# Arbiters — Class Overview

**Category:** Control / scheduling
**Scope:** `rtl/common/arbiter_*.sv` (4 modules)
**Status:** Production-ready

---

## What this is

Single-cycle arbiters that grant exactly one of N requesters access to a shared resource. The class covers fixed-priority (priority encoder), fair round-robin (rotating-mask), and weighted round-robin with QoS credits. The monbus-instrumented and PWM-weighted variants live in `rtl/amba/shared/`; this directory holds the protocol-agnostic primitives.

## Why use this class

Shared resources — register-file write ports, memory banks, bus masters, FIFO drains — all need arbitration. Rolling a fresh arbiter per use site is a common source of unfairness, starvation, and timing bugs. These modules give you a single-cycle grant with proven fairness properties and clean parameterization on `N`.

## Members

| Module | One-line role | When to pick |
|---|---|---|
| [`arbiter_priority_encoder.sv`](../../../rtl/common/arbiter_priority_encoder.sv) | Fixed priority — lowest index wins | Strict priority, real-time channels, leaf primitive |
| [`arbiter_round_robin_simple.sv`](../../../rtl/common/arbiter_round_robin_simple.sv) | Rotating-mask round-robin, no ack handshake | Symmetric clients, fair sharing, simplest fair option |
| [`arbiter_round_robin.sv`](../../../rtl/common/arbiter_round_robin.sv) | Round-robin with grant-ack handshake | Multi-cycle service, transactions held until ack |
| [`arbiter_round_robin_weighted.sv`](../../../rtl/common/arbiter_round_robin_weighted.sv) | Credit-based weighted RR with QoS, dynamic weights | Proportional bandwidth, QoS, starvation-free WRR |

## Picking guide

Use `arbiter_priority_encoder` when one channel really is more important than another — interrupts, error reporting, leaf primitive inside another arbiter. Use `arbiter_round_robin_simple` for symmetric peers that need fair sharing in a single cycle. Use `arbiter_round_robin` when grants must hold for multi-cycle transactions and the granted master signals completion with an ack. Use `arbiter_round_robin_weighted` when clients have different bandwidth budgets or QoS classes — the credit scheme prevents starvation even with dynamic weight updates.

## Tests

[`val/common/`](../../../val/common/) — pytest + CocoTB suite. Naming: `test_arbiter_*.py`.

## Full per-module specs

[`docs/markdown/RTLCommon/`](../../markdown/RTLCommon/) — one `.md` per module. Use those for parameter descriptions, port lists, and waveform examples.

## Source

[`rtl/common/`](../../../rtl/common/) (`arbiter_*.sv`)

> For monbus-instrumented and PWM-weighted variants, see [`rtl/amba/shared/`](../../../rtl/amba/shared/) (`arbiter_rr_pwm_monbus.sv`, `arbiter_wrr_pwm_monbus.sv`).

---

## Navigation

- **[← Back to RTL Design Sherpa README](../../../README.md)**
- **[← Browse by Class index](../../../README.md#browse-by-class)**
- **[Main Documentation Index](../../DOCUMENTATION_INDEX.md)**
- **[Common Library per-module specs](../../markdown/RTLCommon/index.md)**
