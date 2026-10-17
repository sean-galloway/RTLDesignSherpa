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

# Cell — Compute Engine IP

**Codename:** cell · **Directory:** `cell/` — the compute-eng-ip family
alongside [`hive-serv`](../hive-serv/).

Cell is the repo's compute engine: a coarse-grained reconfigurable array
(CGRA) that HIVE orchestrates and RAPIDS feeds. Where [hive-serv](../hive-serv/)
is the control plane (one VexRiscv master + sixteen SERV monitors), cell is
the data plane — the part that actually computes.

## Blocks

| Block | Name | What | Status |
|---|---|---|---|
| Compute cell | [`cell`](docs/PRD.md) | One `delta_mesh_cell` node (black box; containment is the whole cell↔delta relationship, owner clarification 2026-10-16) + input memory + ALU/execution FSM + result memory + packetizer + credit logic. Rapids fills the input memory through the node; the FSM consumes lines, computes, writes results; results leave as packets batched X flits; each consumed input line returns a credit to rapids | **PRD 0.1 (2026-10-16)** |
| Compute array | `cgra` | Reconfigurable array of richer PEs — the 2026-10-13 ambition, deferred 2026-10-16. The cell's block boundaries are chosen so an array replaces ALU+FSM without disturbing the network, credit, or observation contracts | Deferred |
| Result routing | [`axon`](docs/axon_spec.md) | **Superseded 2026-10-16** by the cell PRD's output path (the result memory + packetizer do the collect/packetize/stream role axon sketched, against the adopted §11 header/credit protocols) | Superseded |

## Architecture

```
        rapids ── packets ──▶ delta_mesh_cell ──▶ INPUT MEMORY
                                  (local port)         │ lines
                                              ALU + execution FSM
                                                (config-selected fn)
                                                        ▼
              rapids ◀── credit packets          RESULT MEMORY
                  ▲ (consumed-line credits)            │ X-flit batches
                  └──────────── packetizer ◀───────────┘
```

Sixteen cells per tile per the adopted hierarchy
([tile](../tile) TILE_SPEC §11); the tile connects to rapids through
the root nodes and mux. Full dataflow, credit/grant behavior, config
registers, and open questions: **[cell PRD](docs/PRD.md)**.

**Fabric configuration (owner decisions 2026-10-13):** in-band only — delta
routers are programmed through routing tables carried by PKT_CONFIG; no
dedicated configuration wires. Routing is QoS-aware (the HIVE HAS router
register map already provisions `ROUTE_TABLE_n`, `FLOW_CTRL_CFG`, and
`PRIORITY_MASK`; descriptor priority levels cover the traffic side).

**Conventions (standing owner decisions — apply to cell as they do to HIVE):**
delta is the fabric; everything crossing a block boundary is AXI4-Stream;
AXI4-Lite is for registers only; SERV is the repo's tiny agent core; the
verification stack is cocotb + the rds-dv BFMs.

## History

- compute-eng-ip created 2026-09-29 in the component-tree regrouping;
  `hive` retired here 2026-09-27 (unstarted), re-homed to riscv-ip
  2026-10-10, returned 2026-10-13 when cell revived the family.
- 2026-10-16: cell redefined to the ALU cell ([PRD](docs/PRD.md)) on
  owner datapath decisions (node fills input memory; ALU+FSM computes;
  consumed-line credits; X-flit batching; grants on the result path;
  credit batching config N default 1; B4/8/16/32 element widths). CGRA
  deferred; axon superseded; TILE_SPEC §11 adopted the same day.
