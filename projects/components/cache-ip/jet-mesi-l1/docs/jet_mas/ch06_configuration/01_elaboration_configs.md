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

# Elaboration Configurations

**Status:** planned contract. Geometry is inherited from amber D1
(4–32 KiB, 32–64 B lines, 2–8 ways; default 32 KiB / 64 B / 4-way = 128
sets; the tiny 16-set/2-way formal config). jet adds exactly two knobs
(HAS ch05):

| Parameter | Range | Default | Controls |
|---|---|---|---|
| `MSHR_COUNT` | 2–16 | 8 | outstanding misses (J1) |
| `VICTIM_DEPTH` | 1–4 | 2 | writeback buffer depth (J5) |

Everything else the J-rows considered is a fixed behavior, not a parameter:
organization (full-assoc CAM), merge policy (exact-line, no escalation),
hit-under-miss scope (reads+writes), response order (in-order release),
congestion (strict stall, snoop priority).

## Named configurations

| Name | Geometry | MSHR_COUNT | VICTIM_DEPTH | Purpose |
|---|---|---|---|---|
| `tiny` | 16 sets / 2 ways | 2 | 1 | SymbiYosys |
| `default` | 128 sets / 4 ways | 8 | 2 | the product center |
| `sweep` | default | 2/4/8/16 | 2 | the J7 occupancy→bandwidth curve |
| `wb_sweep` | default | 8 | 1/2/4 | the drain-decoupling curve |

## Rig selection

No `RIG` parameter (amber's rule): the rig is the top module — `jet_top`
(pair) or `jet_ace_top` (onyx).
