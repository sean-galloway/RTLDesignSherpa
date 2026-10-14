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

# Verification Targets

> **PLANNED:** This chapter describes the planned `delta_mesh_cell` verification strategy per the 2026-10-13 design spec (`docs/superpowers/specs/2026-10-13-delta-mesh-design.md`). No RTL implementation exists yet.

## cocotb Suites

The mesh verification plan is eight cocotb suites, each driven by a different generator configuration.

| Suite | Focus | Pass criteria |
|---|---|---|
| Routing | Reset DOR, programmed tables, config load + readback | Correct output port per table; readback matches write |
| QoS | Strict priority, aging inversion, bulk reservation | Class order under saturation; bulk minimum bandwidth |
| Multicast | Fanout correctness, no-response rule, delivery-VC soak | All destinations receive exactly one copy; no deadlock |
| Deadlock soak | Random adversarial-but-valid tables, VC1 stress with VC0 escape | No hangs to N × 10^6 flits |
| Systolic | Torus ring, wavefront, source-route fixed latency, 3-D stencil | 1 cycle/hop steady state where lookahead applies |
| Counters | Every ocelus counter against golden model | Count match over scripted traffic |
| DFT mode | Three patterns route correctly | Pattern count and `test_active` behavior |
| Perf model calibration | Measured vs modeled latency/throughput | Reported deltas within tolerance |

: Mesh cocotb verification suites

## Formal Assists

Three formal checks assist the cocotb suites:

1. **VC0 acyclicity checker.** Run offline on table images before load; rejects any VC0 subrelation that violates Duato's sufficient condition [D2].
2. **One-hot grant assertions.** Per-output switch and VC grants must be one-hot or zero-hot, identical to the flat-mode assertion discipline.
3. **TLAST-before-grant-release packet atomicity.** A grant may not be released before the `TLAST` handshake completes, preventing packet interleaving on an output.

## Performance Model Calibration

The Python performance model (`bin/delta_mesh_perf.py`) predicts zero-load latency and saturation throughput for uniform, nearest-neighbor, tornado, bit-complement, and transpose patterns. The perf-model suite compares measured results against the model and reports deltas; the model itself is verified by the same methodology used for network-processor benchmarks [P20][Q1].

## References

- Duato, Yalamanchili, Ni, *Interconnection Networks: An Engineering Approach*, 2nd ed., Morgan Kaufmann, 2003 — acyclicity condition for deadlock-free escape VC [D2].
- Dally & Towles, *Principles and Practices of Interconnection Networks*, Morgan Kaufmann, 2004 — performance analysis methodology [P20].
- Franklin et al. (eds.), *Network Processor Design: Issues and Practices, Vol. 1*, Morgan Kaufmann, 2002 — hardware-level benchmarking practice [Q1].
