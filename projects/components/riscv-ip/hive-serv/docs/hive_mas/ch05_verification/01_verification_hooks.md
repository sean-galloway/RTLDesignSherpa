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

# Verification Hooks and Observability

## Observation Bus

Every block drives a fixed slice of a flat observation record
(`hive_obs_pkg`), exported through `hive_top` in `hive_c_clk` domain.
Slices include: injection queue occupancy/stall, descriptor_gen doorbell
events, control-network grant sequence and per-slave service intervals,
trigger_logic raw lines, switch_controller FSM state, and CDC FIFO
full/empty flags. The repo's Ocelus monitor system attaches to this bus for
protocol and coverage collection in system simulations — no internal
signals are probed ad hoc.

## Protocol Checkers (immediate assertions)

| Check | Where |
|-------|-------|
| tuser/tdest legal combinations (HAS §2 validation rules) | Delta ingress of each HIVE stream |
| No CDA before boot phase C | descriptor_gen output |
| Descriptor order preserved | CDC FIFO output vs. enqueue |
| Broadcast simultaneity (same cycle all routers) | switch_controller observation |
| TID integrity (tid == tile_id on CE PKT_DATA) | Delta NI (owned by Delta; HIVE TB asserts it) |
| Quiesce-before-switch | switch_controller (with interlock) |

: Checker inventory

## Formal Properties

The HAS §7 formal inventory maps to properties owned here:

- **Router deadlock freedom** — Delta-owned; HIVE testbenches assume it.
- **Descriptor FIFO ordering** — asserted on the injection queue + CDC FIFO
  chain.
- **Context switch atomicity** — no packet observation between
  `SET_ROUTING_MODE` and `CONFIG_ACTIVATE` on any router tap.
- **TID integrity** — cross-asserted with Delta NI.
- **Quiesce completeness** — `active_packets == 0` on all participating
  routers before the atomic point.

## Testbench Structure (cocotb, rds-dv framework)

- BFMs: AXIS masters/slaves from `cocotb-framework` for the Delta-facing
  streams; AXIL BFM for the register window; a lightweight control-network
  frame BFM for the star.
- Reference: firmware-level golden models for descriptor generation and
  scheduling; spike is not applicable (no ISA verification — the cores are
  imported and verified by their own suites).
- Levels: unit per FUB (HAS §7 example), integration per block pair, system
  per HAS Chapter 7. Coverage targets: 100% line, 95%+ branch; functional
  coverage points derive from this book's behavior chapters (one covergroup
  per §4 sequence's decision points).

---

**Last Updated:** 2026-10-12
