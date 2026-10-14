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

# Deferred Items

> **PLANNED** — The mesh cell RTL is not yet implemented. The items below are recorded from the delta mesh design spec dated 2026-10-13 (`docs/superpowers/specs/2026-10-13-delta-mesh-design.md`) and are explicitly not part of the current design.

The following features were considered and deferred:

- **GT/TDM slot-table circuits** — Ethereal/NoC slot tables, headerless GT flits, end-to-end credit flow control, and optional VOQ. Phase-2 candidate.
- **Fault-tolerant routing** — block fault regions, software absorb/reinject, and fault-status registers.
- **Barrier/superstep sync wave** — ECLIPSE-style synchronization wave; lands with the CGRA work, not delta.
- **Express channels/cubes** — little use at the target radix; skipped.
- **Logical-to-physical address mapping** — revisit if remapping or fault-recovery demands it.
- **GALS/async links** — single clock is a deliberate simplification contrary to this literature direction.
- **VOQ option** — area/throughput trade; add when a user needs it.
- **Within-class per-flow fairness (WRR/DRR)** — deferred until a user asks.
- **Flit-reservation flow control** — revisit if systolic latency targets are not met by route lookahead.
- **Reliable-mode resend/NACK** — only if a control-plane user needs lossless delivery beyond class-0 VC isolation.
