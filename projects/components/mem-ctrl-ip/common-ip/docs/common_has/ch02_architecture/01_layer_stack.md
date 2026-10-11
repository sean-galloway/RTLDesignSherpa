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

# The Architecture: axi4 → storage → scheduler → (ras) → training → dfi

This chapter is the vision, written down. It was set out by the partner in
the Phase-2 campaign and it drives every block in common-ip. The layers
below are listed in command-flow order. The whole unit, drawn in the
family's diagram house style
([STYLE.md](../assets/graphviz/STYLE.md) — the classic DDR-MC course form the
owner fixed as the reference):

![The mem-ctrl-ip whole unit — AXI channels at top, the layer stack in the middle, DDR PHY bar at the bottom](../assets/graphviz/01_whole_unit.png)

## The layer contract

Each layer has exactly one job. The table is the binding statement; the
per-block microarchitecture is in
[common_mas](../../common_mas/common_mas_index.md) and is not restated here.

| Layer | Job | Owns | Does not own |
|---|---|---|---|
| `mc_axi4_layer` | Turn host AXI4 traffic into memory-command descriptors | AXI4 slave intakes, shallow FIFOs, burst chop/split, final coalescing; read-data return endpoint | DRAM knowledge of any kind; scheduling; the DRAM data path |
| `mc_storage_layer` | Hold the schedulable-entry pool and the bank image | rd/wr CAMs (or SRAM-backed equivalents), read snooping, per-bank open-row image as a *select*, address mapping | The pick itself; DRAM command encoding |
| `mc_scheduler_layer` | Pick the next DRAM command | The schedulable-entry view contract, bank/global timers, command arbiter, maintenance arbitration (refresh, ZQ, training windows) | Where entries are stored (that is the storage layer's job); PHY timing |
| `mc_ras_layer` (optional) | Reliability transforms on the data path | ECC insert/check as a transform pair, scrub as a maintenance client | Anything when not instantiated — its absence is a true bypass, not a stub |
| `mc_training_layer` | The training control plane as a maintenance client | ZQ calibration control, DQ calibration, write-leveling interface, the maintenance slot arbitration that carries them | The training *search* (PHY responsibility, per doctrine — the family doc's boundary rule) |
| `mc_dfi_NpM_layer` | Deliver commands and data to the PHY at a DFI revision | Command formatter/pipeline, write serializer, read aligner, the aclk↔dfi_clk CDC — per generation: `dfi_2p1_layer`, `dfi_3p1_layer`, `dfi_4p0_layer` | Scheduling decisions; training searches |

## Why layers — the reason this shape exists

The point of the stack is **drop-in performance features on a stable
contract**. Because the storage layer presents the scheduler the same
descriptor view the AXI layer does, a feature that needs a different
entry-pool organization (bigger CAM, SRAM-backed pool, hashed bank
assignment) changes the storage layer only — the scheduler and everything
downstream do not move. A product that needs no reordering replaces the
storage layer with its lite configuration and keeps the same scheduler
(Ch 5.2). The seam is the architecture; the blocks are replaceable parts on
it.

This is also why the scheduler is defined against a **schedulable-entry
view** rather than against the CAMs directly: the pick machinery argmaxes
over schedulable-entry vectors, and *something* has to hold those entries —
that something is the storage layer in a full build, and the stripped AXI
layer serving N=1 in a lite build. "Storage off" can never be literally
zero hardware (the entry store cannot reach zero); it is the lite config,
not an omission.

## The three structural rules of the stack

1. **Command flow is one direction.** Descriptors flow axi4 → storage →
   scheduler → dfi. Nothing upstream is consulted after a pick commits; the
   seam's advisory snapshot is the boundary (Ch 2.2).
2. **Maintenance requests; it never preempts** (family doctrine 2, in force
   here unchanged). Refresh, ZQ, calibration are guests on the command bus
   with a request/grant contract into the scheduler's maintenance slots.
3. **Optional layers are param-selected, not compile-selected by absence.**
   The RAS layer exists or it does not; a build without it wires the storage
   and DFI layers together directly. What is *never* optional: the entry
   store, the write-data buffer (it cannot reach zero), and the CDC.

## What the rocks own

Generation-specific blocks stay rock-side today, by the two-customer rule:
the init sequencer, the mode register, the refresh controller, the page
policy engine, and the power-down controller. The scheduler layer is a thin
rock wrapper around the common scheduler core precisely for this: the
wrapper instantiates the rock's children and maps the rock's maintenance
source into the generic maintenance slot
([mc_scheduler_knobs.md](../../mc_scheduler_knobs.md) §6 documents the union
that made this possible). When a second customer appears for one of those
blocks — the refresh controller family is the leading candidate — the
extraction follows the same rule that produced this stack.
