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

> **IMPLEMENTED:** This chapter describes the `delta_mesh_cell` verification suites as built. The design is per the 2026-10-13 design spec (`docs/superpowers/specs/2026-10-13-delta-mesh-design.md`).

## cocotb Suites

The mesh verification plan is ten cocotb suites, each driven by a different generator configuration.

| Suite | Focus | Pass criteria |
|---|---|---|
| Cell routing | Reset DOR, programmed tables, config load + readback | Correct output port per table; readback matches write |
| Fabric 2x2 | All-pairs delivery across multi-hop paths | Every packet delivers exactly once |
| Flow control | Credit exhaustion, atomicity, steady-state throughput | No loss, no interleaving, sustained 1 flit/clk |
| Tables | Malformed-dst drop, cross-VC drop drain, table reroute | Drop counted once; drain stays on its own VC |
| Modes | Broadcast mode-switch, ack barrier, mode images 1/2/3/5/6 | Barrier completes; traffic routes per selected image |
| Tetrad | Mode 9 K4 all-to-all, P_DIA one-hop latency | All 12 ordered pairs deliver in 1 hop |
| Tile | Mode 10 K4-of-tetrads, P_DIA2 one-hop latency | Diagonal-tetrad pairs deliver in 1 hop |
| QoS | Strict priority, aging inversion, bulk reservation | Class order under saturation; bulk minimum bandwidth |
| Multicast | Fanout correctness, no-response rule, deadlock soak | All destinations receive exactly one copy; 10^6-flit soak green |
| Counters | Counter bank readback, DFT escape | Readback matches scripted traffic; DFT pattern switches |
| Systolic | Torus ring, dateline, source-route, speculation | Ring latency measured; dateline forces VC0; SR bypasses table drop; speculation parity |
| Perf model calibration | Tornado pattern at three loads vs `bin/delta_mesh_perf.py` | Zero-load T0 within 20% of model; loaded deltas recorded |

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
