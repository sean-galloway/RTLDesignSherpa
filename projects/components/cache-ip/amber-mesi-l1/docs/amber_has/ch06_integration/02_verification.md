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

# Verification Strategy

## Pattern-B cocotb grids

The primary verification layer is Pattern-B GATE/FUNC/FULL cocotb grids over the geometry × policy × rig matrix (amber D9). The ACE BFMs are the RDS-DV cocotb-framework 1.2.0 ACE extensions: `AXI4ACEMasterRead`, `AXI4ACEMasterWrite`, and `AXI4ACESnoopSlave`/`Master`.

## Golden-model parity

For LRU, FIFO, and RANDOM, amber's hit/miss/miss-class counts must match the cache_sim trace replay at identical geometry and policy. tree-PLRU has no cache_sim golden model today; it is cross-checked by RTL self-checks and is recorded as a future sim extension (Chapter 6.4). Miss classes follow cache_sim: compulsory, capacity, and conflict.

## Formal targets

SymbiYosys is scoped to the control layer and proven at the tiny 16-set / 2-way geometry:

- No stale data served after an external write (pending-fill bypass correctness).
- No deadlock or livelock under fair arbitration.
- Victim-buffer handoff correctness.
- `amber_snoop_resp` AC/CR/CD ordering.

The proof surface is intentionally narrow: proving the whole cache data path at default geometry is not the goal; proving the control and snoop-responder logic that correctness depends on is.

## Python reference model

The Python reference model and the FSM oracles derive from the gem5 Ruby `MESI_Two_Level` SLICC tables (D9). `L1cache.sm`'s enumerated transient states are the source for the `amber_pkg` state encoding. Every stable and transient transition is cross-checked against the executable protocol spec, not prose.

## MonBus coverage

Every event class listed in Chapter 4.5 must be visible on MonBus in simulation. The `_monlite` wrapper is present-vs-absent in the regression so the gate-cost delta is part of the evidence.
