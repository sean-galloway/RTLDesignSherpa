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

# Observability Counters and DFT

> **PLANNED:** This chapter describes the planned `delta_mesh_cell` microarchitecture per the 2026-10-13 design spec (`docs/superpowers/specs/2026-10-13-delta-mesh-design.md`). No RTL implementation exists yet.

## Ocelus Counter Suite

The ocelus observability block attaches to every input/output port and every VC. Counters clear on `aresetn` and are readable through the config port.

| Counter group | What it counts | Use |
|---|---|---|
| Flit counts | Sent and received flits per port/VC | Throughput sanity |
| Packet counts | `TLAST` handshakes per port/VC | Packet completion |
| Stall cycles | Per-VC backpressure cycles | Congestion location |
| Arbitration | Win/loss per QoS class | Fairness and aging verification |
| Queue occupancy | Current and max watermark | Buffer sizing feedback |
| Latency | Injection-to-ejection min/avg/max + jitter | Perf model calibration |
| Multicast | Replication count per branch | Multicast coverage |
| Errors | Misroute drops, credit starvation events | Debug |

: Ocelus counter suite

Boundary cells optionally timestamp head flits so end-to-end latency can be measured against the rapids DMA clock. The suite is ahead of the NoC textbook literature, which says little about hardware observability, and is instead modeled on NPU practice [Q4][Q2][Q8].

## DFT Test Mode

DFT mode reconfigures each cell into one of three deterministic routing patterns so the mesh wiring behaves as a concatenated bus. Stuck-at and bridge faults become testable with approximately `ceil(log2(n))` patterns, where `n` is the number of cells in the fabric [N6]. The mode is entered through the config port; a `test_active` output per cell indicates DFT state.

| Pattern | Routing behavior | Fault target |
|---|---|---|
| Pattern 0 | All cells route +X | Horizontal wiring |
| Pattern 1 | All cells route +Y | Vertical wiring |
| Pattern 2 | All cells route +Z | Depth wiring |

: DFT routing patterns

> **Design note:** DFT mode is mutually exclusive with normal traffic. The cell gates non-test flits while `test_active` is asserted; returning to normal mode requires a fabric-wide mode-switch sequence.

## References

- Jantsch & Tenhunen (eds.), *Networks on Chip*, Kluwer, 2003 — testing the communication infrastructure with three switch configurations [N6].
- Franklin et al. (eds.), *Network Processor Design: Issues and Practices, Vol. 1*, Morgan Kaufmann, 2002 — IXP2400 PMU, Toaster per-queue stats, Agere ASI RMON counters [Q4][Q2][Q8].
