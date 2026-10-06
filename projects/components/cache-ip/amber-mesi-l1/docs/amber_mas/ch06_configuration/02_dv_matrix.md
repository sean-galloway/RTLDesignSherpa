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

# DV Matrix Dimensions

## Pattern-B Cocotb Grids

The primary DV layer is Pattern-B GATE/FUNC/FULL cocotb grids over the geometry × policy × rig matrix.

### Dimensions

| Dimension | Values |
|-----------|--------|
| Geometry | default (128/4/64/64), tiny (16/2/64/64), bring-up (4/2/32/32) |
| Policy | LRU, FIFO, RANDOM, tree-PLRU |
| Rig | `amber` (pair-rig AXI4), `amber_ace` (onyx-rig ACE) |
| Write policy | wb_wa, wt_na (bring-up only) |

### Grid Coverage

| Grid | Geometry | Policy | Rig | Purpose |
|------|----------|--------|-----|---------|
| GATE | tiny | LRU | amber | fast gate-level sanity |
| FUNC | default | LRU, FIFO, RANDOM | amber | functional regression |
| FUNC | default | LRU | amber_ace | coherent-transaction sanity |
| FULL | default | all four | both rigs | nightly regression + cache_sim parity |
| FULL | tiny | LRU | both rigs | formal companion runs |

## Formal Targets

SymbiYosys is scoped to the control layer at the tiny geometry:

- No stale data served after an external write (pending-fill bypass correctness).
- No deadlock or livelock under fair arbitration.
- Victim-buffer handoff correctness.
- `amber_snoop_resp` AC/CR/CD ordering.

## Golden-Model Parity

For LRU, FIFO, and RANDOM, amber hit/miss/miss-class counts must match `cache_sim` at identical geometry and policy. tree-PLRU has no `cache_sim` golden model today; it is cross-checked by RTL self-checks and recorded as a future sim extension.

## MonBus Coverage

Every event class in Chapter 4 must be visible on MonBus in simulation. The `_monlite` wrapper is present-vs-absent in the regression so the gate-cost delta is part of the evidence.

---

**Last Updated:** 2026-10-06
