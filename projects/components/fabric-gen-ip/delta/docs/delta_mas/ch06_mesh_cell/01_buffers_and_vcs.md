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

# Buffers and Virtual Channels

> **PLANNED:** This chapter describes the planned `delta_mesh_cell` microarchitecture per the 2026-10-13 design spec (`docs/superpowers/specs/2026-10-13-delta-mesh-design.md`). No RTL implementation exists yet.

## Per-Port Input Buffer Organization

Each `delta_mesh_cell` has seven AXI4-Stream input ports: six neighbor ports (±X, ±Y, ±Z) and one local port. Every input port keeps two virtual channels, so the buffering resource is `7 ports × 2 VCs`. Each VC is a physically separate buffer partition with its own single-port readout; the two partitions on one port share only the incoming flit stream up to the VC demux.

| Resource | Count per cell | Notes |
|---|---|---|
| Input ports | 7 | 6 neighbor + 1 local |
| VCs per port | 2 | VC0 = escape, VC1 = adaptive/QoS alternate |
| Buffer partitions | 14 | one single-port readout array per VC |
| Read ports consumed | 7 | one per input port, multiplexing its two VCs into the pipeline |

: Input buffer organization

The single-port-per-input choice is deliberate. It is cheaper than a fully-ported VC-per-input arrangement, and it matches the expected throughput because only one flit per input port advances in a given cycle. The real cost is area, not bandwidth: Proteo reported that FIFO flops dominated a NoC node at 81% of area [N8: §4.5], so the generator exposes a regs-vs-SRAM buffer knob.

## Why Per-VC Reservation Is Required

A shared input buffer that any VC can draw from looks efficient until adaptive routing starts bouncing packets. Here is the part that bites: a packet can hold the last free slot in a shared buffer while waiting for a credit that is held by another packet, which in turn is waiting for a slot in the same buffer. That cycle is a deadlock, and it is exactly why the literature insists on per-VC buffer reservation for VC-based deadlock avoidance. Duato's sufficient condition for deadlock freedom assumes that a packet queued on one channel cannot block resources belonging to another channel [D2][D7]; Dally & Towles restate the same requirement for per-VC input buffer organization [P18: §17.1]. Partitioning the buffer keeps the channel-dependency graph clean and makes the escape-channel proof hold.

> **Design note:** A shared read port is fine; a shared *storage pool* is not. The demux that writes a flit into VC0 or VC1 must be deterministic from the flit's VC field; do not let a full VC0 spill into VC1 space, or the deadlock analysis collapses.

## Credit-Based Flow Control

Every (output port, VC) pair maintains a credit counter that tracks the number of free buffer slots at the downstream input VC. A flit may leave this cell only if the corresponding credit is non-zero. When the downstream cell consumes the flit, it returns a credit. The counter depth must cover the round-trip latency so the channel can run at full duty factor:

`F · Lf / tcrt ≥ b`

where `F` is the flow-control frequency, `Lf` is the forward channel latency, `tcrt` is the credit-return latency, and `b` is the minimum number of credits needed to keep the pipe full. If the inequality fails, the link will go idle waiting for credits even though both ends have data [P10][P15].

| Counter | Location | Width driver |
|---|---|---|
| Downstream credit | Per (output port, VC) | round-trip latency × flits per cycle |
| Consumed credit | Per (output port, VC) | same as credit counter |

: Credit counter sizing

## Failure Mode: Ready Drops Mid-Burst

So what happens when `TREADY` drops mid-burst on an output? The flit stays in the upstream buffer, the credit is not returned, and the upstream pipeline stalls for that VC only. Because each VC has its own credit counter, a backpressured VC1 path does not block VC0 escape traffic. That isolation is the whole point of splitting the buffers.

## References

- Duato, Yalamanchili, Ni, *Interconnection Networks: An Engineering Approach*, 2nd ed., Morgan Kaufmann, 2003 — channel-dependency theory and VC-based deadlock avoidance [D2][D7].
- Dally & Towles, *Principles and Practices of Interconnection Networks*, Morgan Kaufmann, 2004 — per-VC input buffer reservation and credit sizing [P10][P15][P18].
- Jantsch & Tenhunen (eds.), *Networks on Chip*, Kluwer, 2003 — Proteo node area and FIFO cost data [N8: §4.5].
