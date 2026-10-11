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

# The Descriptor Seam

The seam is the interface between layers, and the load-bearing idea of this
architecture: **the storage layer presents the scheduler exactly the same
descriptor interface the AXI layer does.** One shape, two providers. This
chapter states the contract and its invariants.

## The contract

A layer upstream of the scheduler exposes a pool of schedulable entries:

- **N entry slots** (`N = 8` in the full storage configuration; `N = 1` in
  the stripped AXI-layer configuration — "argmax set to 1 for both reads and
  writes, then it matches to a FIFO"). The full configuration is not a
  different protocol; it is the same vectors with more entries behind them.
- **Per-entry vectors:** the scheduler's pick machinery argmaxes over
  schedulable-entry vectors — for each entry, its validity, read/write class,
  decoded address (row / bank / column), age, and readiness inputs. The
  vectors are the contract; the storage behind them (CAM, SRAM, a FIFO in
  the N=1 case) is an implementation freedom of the providing layer.
- **Commit / issue removal:** when the scheduler fires a command built from
  an entry, it removes the entry (or the consumed portion of it) through the
  same interface. Partial consumption — a chopped burst issuing over
  multiple cycles — is the provider's bookkeeping, invisible downstream.

Because the AXI layer can be designed to emit the same information for a
single in-order item, a controller can be assembled with no storage layer at
all and the scheduler cannot tell the difference from the vectors alone.
That is what makes the lite product SKU (Ch 5.2) a configuration rather than
a redesign.

## The invariants

These hold at every seam in the family. They are recorded here so a
performance-feature drop-in cannot break one silently.

1. **Read snooping sees un-coalesced writes.** The read path snoops the
   write stream at write-data-CAM granularity, before any write coalescing.
   A merged descriptor would hide write data a later read must see; so
   snooping is defined against the un-coalesced view and coalescing happens
   after.
2. **Merged descriptors inherit the oldest age.** When the storage layer
   coalesces entries, the result carries the age of its oldest constituent.
   Age drives the scheduler's starvation avoidance; inheriting anything
   newer would let a coalesced burst jump the queue.
3. **The advisory snapshot / epoch is the boundary.** What the scheduler
   sees is an advisory snapshot of the pool, refreshed at an epoch boundary.
   The scheduler does not reach back upstream after a pick commits; the
   epoch is the consistency point. Anything stronger (live querying of the
   pool) couples the layers in a way the drop-in goal forbids.

## What the seam is not

- **The return path is not on the seam.** Read data flows storage → AXI
  through `mc_rd_return_ring` — a separate contract with its own ordering
  rules (it must reorder to AXI IDs). It cannot ride the descriptor seam,
  and the symmetry goal must not absorb it: *never let the perfect get in
  the way of the good.* A future revision may unify the seams; until then
  the descriptor seam is command-direction only.
- **The open-row image is not a seam payload.** The per-bank open-row image
  stays scheduler-adjacent (the storage layer provides it as a *select*
  feeding the scheduler's own view). It does not cross the seam as an
  independent interface; that would let two layers believe two different
  things about which row is open.
- **The seam is not a bus.** No arbitration crosses it; the upstream layer
  owns its entries until the scheduler consumes them.

## Where this stands in the rocks

Today's rocks wire the seam concretely as
`mc_axi4_layer → mc_storage_layer → <rock>_scheduler_layer`, with the CAMs
living in the storage layer and the rock scheduler wrapper presenting the
rock's maintenance clients to the common core. pumice is the reference
integration (measured at 66.67 / 75 MHz on Nexys A7). The contract in this
chapter is the destination the storage-layer extraction already implements;
when a rock's documentation and this contract disagree, this contract wins
and the rock book is the defect.
