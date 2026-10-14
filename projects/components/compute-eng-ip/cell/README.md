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
| Compute array | `cgra` | Reconfigurable 3-D nearest-neighbor array of compute units (owner: "cells"); four cells form a **quad**, four quads form a **tile** — the tile level is what connects to RAPIDS. Configuration is in-band through delta (routing tables via PKT_CONFIG, no extra wires) and routing is QoS-aware. Fabric geometry, PE datapath, and context model TBD — own HAS/MAS when designed | TBD (architecture set 2026-10-13) |
| Result routing | [`axon`](docs/axon_spec.md) | SERV + delta pair that collects tile results and streams them out over the AXIS fabric (the tile-level twin of HIVE's monitors); attaches at the tile boundary | Spec sketch |

## Architecture sketch

```
            HIVE-C descriptors (CDA, via delta)
                      │
        ┌─────────────┴──────────────┐
        │            cell            │
        │  ┌──────────────────────┐  │
        │  │        cgra          │  │   3-D nearest-neighbor array:
        │  │  cells in quads      │  │   4 cells = 1 quad
        │  │  (4 cells per quad)  │  │   4 quads = 1 tile
        │  │  quads in a tile     │  │   tile <-> RAPIDS
        │  └──────────┬───────────┘  │
        │             ▼ results      │
        │  ┌──────────────────────┐  │
        │  │        axon          │  │   SERV agents on delta at the
        │  │  (SERV + delta)      │  │   tile boundary: collect +
        │  └──────────┬───────────┘  │   stream out
        └─────────────┼──────────────┘
                      ▼ PKT_DATA / results
                 delta fabric → RAPIDS (S2MM)
```

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
