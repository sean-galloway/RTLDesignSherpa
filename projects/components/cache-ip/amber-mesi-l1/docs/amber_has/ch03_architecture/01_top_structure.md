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

# Top Structure and the Two Rigs

## No rig parameter

amber does not use a `RIG` elaboration parameter. The rig is the top you instantiate: instantiate `amber` for the pair rig, instantiate `amber_ace` for the onyx rig (F12). Both tops compile; both are exercised in the DV matrix. This keeps the rig-specific wiring out of the shared core and avoids a mode signal that would broaden the formal surface for no benefit.

## `amber` — pair-rig top

`amber` wraps `l1_core` with:

- House `axi4_master_rd` and `axi4_master_wr` for plain AXI4 memory access (D3, decided PRD v0.6 2026-10-07).
- The `l1_snoop_resp` ACE adapter facing the peer cache.
- No coherent-transaction issuer; memory-side misses are ordinary AR/AW bursts.

The snoop responder sees the peer's AC/CR/CD even though the memory side is plain AXI4. That is exactly the pair-rig shape: coherence is handled cache-to-cache; memory only supplies cold misses and absorbs dirty write-backs.

## `amber_ace` — onyx-rig top

`amber_ace` wraps the same `l1_core` with:

- `axi4ace_master_rd` and `axi4ace_master_wr` toward `onyx`.
- `amber_ace_issue`, which maps cache-side events to the onyx D2 subset: read miss → `ReadNotSharedDirty`/`ReadUnique` (issue #106; formerly `ReadShared`), write promotion → `CleanUnique`/`MakeUnique` on the AR channel with the spec encodings (issue #106), dirty eviction → `WriteBack`, clean eviction → `Evict`.
- The same `l1_snoop_resp` adapter, but facing `onyx` rather than a peer.

Memory is not directly reachable; all fabric traffic is coherent and routed through `onyx`.

## What is inside `l1_core`

`l1_core` contains everything that does not change between rigs: `l1_cpu_frontend`, `l1_control`, `l1_tag_array`, `l1_data_array`, `l1_repl`, `l1_victim`, `l1_fill`, `l1_drain`, `l1_snoop_resp`, and `l1_monlite`. The fill/drain modules expose a rig-agnostic internal interface; the top selects the AXI4 or ACE transport adapter that drives it.
