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

# Performance and Verification

## Performance Model

> **PLANNED** — The mesh cell RTL is not yet implemented. The design is per the delta mesh design spec dated 2026-10-13 (`docs/superpowers/specs/2026-10-13-delta-mesh-design.md`).

The `bin/delta_mesh_perf.py` model uses the standard interconnection-network cost model:

- **Zero-load latency** `T0 = H·tr + D/v + L/b`, where H is the hop count, tr is the per-hop router delay, D is the distance, v is the propagation speed, L is the packet length, and b is the channel bandwidth.
- **Queuing** is modeled as M/D/1 under deterministic flit service.
- **Saturation throughput** is derived from the maximum channel load γ_max, using bisection-bound and multicommodity-flow analysis. The model reports minimum delivered flow, not average.
- **Traffic patterns** include uniform random, nearest-neighbor/stencil, tornado, bit-complement, and transpose.
- **Methodology** uses infinite source queues, warm-up/measurement/drain phases, and latency measured from generation to departure.

Loaded-latency microbenchmarks follow NPU benchmarking practice. Network-calculus delay and backlog bounds for the fixed-priority classes are a phase-2 addition.

## Verification Plan

The mesh verification plan is an 8-suite cocotb program. Each suite is a generator configuration plus a dedicated test file:

1. **Routing** — reset default DOR, programmed-table routing, table load via config port with readback verify.
2. **QoS** — strict priority order, aging inversion under saturation, bulk minimum reservation, class isolation under tree-saturation attack.
3. **Multicast** — fanout correctness, no-response rule, delivery-VC deadlock soak.
4. **Deadlock soak** — random traffic under adversarial-but-valid random tables, plus VC1 stress with VC0 escape, soaking to N×10⁶ flits.
5. **Systolic** — torus nearest-neighbor ring/wavefront with measured per-hop latency, source-route fixed-latency path check, and 3-D stencil halo exchange.
6. **Counters** — every ocelus counter against a golden model.
7. **DFT mode** — three patterns route correctly; pattern count check.
8. **Perf model calibration** — measured versus modeled latency and throughput on the design-spec §10 patterns; report deltas.

Formal assists include an offline VC0-table acyclicity checker, one-hot grant assertions per output, and a TLAST-before-grant-release assertion that preserves packet atomicity. Detailed microarchitecture verification lives in the Delta MAS; the design spec dated 2026-10-13 is the source of truth for the architecture described here.
