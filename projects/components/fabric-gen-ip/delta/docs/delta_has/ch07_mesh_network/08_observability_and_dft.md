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

# Observability and DFT

## Ocelus Counter Suite

> **PLANNED** — The mesh cell RTL and ocelus integration are not yet implemented. The design is per the delta mesh design spec dated 2026-10-13 (`docs/superpowers/specs/2026-10-13-delta-mesh-design.md`).

Each cell exposes a set of per-port, per-VC counters readable through the config port. The suite is informed by NPU observability practice rather than by the sparse NoC literature:

- flit counts (sent/received)
- packet counts (TLAST)
- stall cycles per VC
- arbitration win/loss per class
- queue occupancy (current and max watermark)
- injection-to-ejection latency minimum, average, maximum, and jitter
- multicast replication count
- misroute-drop count
- credit starvation events

Optional head-flit timestamps at boundary cells give end-to-end latency measurements. Counters clear on `aresetn`.

## DFT Test Mode

Test mode configures each cell into one of three deterministic routing patterns so the mesh wiring behaves as a concatenated bus. With three patterns, stuck-at and bridge faults are testable with approximately ⌈log₂(n)⌉ patterns. The mode is controlled through the config port, and each cell drives a `test_active` output.
