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
| Compute array | `cgra` | The reconfigurable PE array itself — fabric size, PE datapath, configuration memory, and instruction/context model are TBD and get their own HAS/MAS when designed | TBD |
| Result routing | [`axon`](docs/axon_spec.md) | SERV + delta pair that collects CGRA results and streams them out over the AXIS fabric (the tile-level twin of HIVE's monitors) | Spec sketch |

## Architecture sketch

```
            HIVE-C descriptors (CDA, via delta)
                      │
        ┌─────────────┴──────────────┐
        │            cell            │
        │  ┌──────────────────────┐  │
        │  │        cgra          │  │   PE array (TBD):
        │  │  PE PE PE PE PE PE   │  │   config + compute
        │  │  PE PE PE PE PE PE   │  │
        │  └──────────┬───────────┘  │
        │             ▼ results      │
        │  ┌──────────────────────┐  │
        │  │        axon          │  │   SERV agents on delta:
        │  │  (SERV + delta)      │  │   collect + stream out
        │  └──────────┬───────────┘  │
        └─────────────┼──────────────┘
                      ▼ PKT_DATA / results
                 delta fabric → RAPIDS (S2MM)
```

**Conventions (standing owner decisions — apply to cell as they do to HIVE):**
delta is the fabric; everything crossing a block boundary is AXI4-Stream;
AXI4-Lite is for registers only; SERV is the repo's tiny agent core; the
verification stack is cocotb + the rds-dv BFMs.

## History

- compute-eng-ip created 2026-09-29 in the component-tree regrouping;
  `hive` retired here 2026-09-27 (unstarted), re-homed to riscv-ip
  2026-10-10, returned 2026-10-13 when cell revived the family.
