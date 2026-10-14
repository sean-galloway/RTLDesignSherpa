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

# Routing and Configuration

## Routing Tables

> **PLANNED** — The mesh cell RTL and its routing tables are not yet implemented. The design is per the delta mesh design spec dated 2026-10-13 (`docs/superpowers/specs/2026-10-13-delta-mesh-design.md`).

Each `delta_mesh_cell` holds a RAM routing table. The lookup key is `(destination coordinate, QoS class)` and the result is `(output port mask, VC)`. Because QoS classes are isolated, each class can have an independent route to the same destination, giving path diversity without changing the cell datapath.

The table is a standard node-table implementation: one lookup per hop. That lookup penalty is why source-route mode (§7.3) exists for latency-critical systolic schedules.

## Reset Default

At reset every cell loads a hardwired dimension-ordered route toward the rapids boundary. The route is connected and acyclic by construction, so it forms a safe bootstrap path even before software loads custom tables. In-band config packets ride this default route.

## Table Constraints

The generator and the table-load checker enforce three rules that keep the mesh deadlock-free:

- VC0 entries must form a connected, acyclic subrelation in the extended channel-dependency graph. This is checked at table-load time, not just at reset.
- VC1 entries must be minimal, or must carry a misroute budget and create no indirect dependence on VC0.
- VC1→VC0 transitions are permitted at any hop; VC0→VC1 transitions are forbidden.

## In-Band Configuration

Config packets target a reserved destination and are intercepted by the cell's ejection block instead of being delivered to the local port. The config format is `{op (read/write), entry index, entry data}`. Reads return response packets to the source so software can load-verify.

Per-cell unicast loading is the primary way to install custom routes: N cells × M entries are written at boot, and individual entries can be rewritten at runtime. Config traffic uses QoS class 0 and the reset-default route; a boundary cell or rapids injects the config stream.

## Broadcast Mode-Switch

A broadcast mode-switch message switches the entire fabric to one of the standard modes. Every cell stores generator-emitted images for the standard modes in ROM or preloaded RAM. The new mode applies only after a fabric-wide ack barrier: each cell returns a config read-response ack, and the injector treats the mode as active only when all acks are in. No packet straddles two modes.

Mode 0 is custom — the per-cell unicast tables. Modes 1-8 are the standard fabric modes. Switching among standard modes does not touch the custom tables.
