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

> **STATUS** — The mesh cell RTL is implemented. The items below remain deferred or are tracked in other workstreams.

The following features were considered and deferred:

- **CXS interface mode** — IMPLEMENTED (owner decision 2026-10-16): `--ifc {axis,cxs}` selects the interface plane; CXS mode wraps the unchanged AXIS core with native AMBA 5 CXS ports so a CXS rapids attaches without adapters. Validated for directed traffic; concurrent-load CXS shows a duplication/loss corner tracked as issue #122.
- **MonBus observation aggregation** — the tetrad/tile wrappers that merge cell MonBus streams live in the compute-eng-ip tile IP, not in delta (parallel session; datapath unchanged).
- **Route lookahead to 1 cycle/hop** — the aspirational systolic target; current measured pipeline is 4 cycles/hop (issue #120).
- **SRAM FIFO_IMPL** — the `--fifo-impl sram` option hangs in the current RTL (issue #118); regression uses `--fifo-impl reg`.

- **GT/TDM slot-table circuits** — Ethereal/NoC slot tables, headerless GT flits, end-to-end credit flow control, and optional VOQ. Phase-2 candidate.
- **Fault-tolerant routing** — block fault regions, software absorb/reinject, and fault-status registers. Multi-path tables with failover as a table write are now being worked: hazards in Resilient Routing: Open Hazards, delta DELTA-013.
- **Barrier/superstep sync wave** — ECLIPSE-style synchronization wave; lands with the CGRA work, not delta.
- **Express channels/cubes** — little use at the target radix; skipped.
- **Logical-to-physical address mapping** — revisit if remapping or fault-recovery demands it.
- **GALS/async links** — single clock is a deliberate simplification contrary to this literature direction.
- **VOQ option** — area/throughput trade; add when a user needs it.
- **Within-class per-flow fairness (WRR/DRR)** — deferred until a user asks.
- **Flit-reservation flow control** — revisit if systolic latency targets are not met by route lookahead.
- **Reliable-mode resend/NACK** — only if a control-plane user needs lossless delivery beyond class-0 VC isolation.
