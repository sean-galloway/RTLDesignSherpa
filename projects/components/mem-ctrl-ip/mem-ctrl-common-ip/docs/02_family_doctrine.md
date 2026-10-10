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

# Family doctrine

**Version:** 0.1
**Date:** 2026-10-04
**Status:** v0.1, filed with the andesite docs tranche. Doctrine binds every
controller book in this family; where a controller's book disagrees, the book
is the defect.

Doctrine is short on purpose. Each entry is one rule, its reason, and where it
was learned.

## 1. Config, not parameter

Runtime-selectable behavior is a CSR or config bit, never a build parameter.
One bitstream characterizes; software picks the memtype, the timings, the
scheduling policy after the fact. Build-time parameters are only for what
truly can't move — geometry, bus widths, the things that cost area. The test
is "would a lab ever want to flip this without a re-synthesis?" If yes, it's a
config bit. scoria's design point already runs this way — every timing is a
runtime CSR — and andesite keeps it.

## 2. Maintenance requests; it never preempts

Refresh, ZQ calibration, and their relatives are guests on the command bus.
They raise a request, the scheduler grants them a window, and they wait their
turn — they never preempt an in-flight host transaction. "All policies:
request/grant, never preempt" is settled in scoria's design requirements
(`design-requirements.md:324`), and scoria's ZQ chapter restates it from the
landed RTL (the refresher FSM shares its arbitration, and it waits). The rule
exists because DRAM maintenance exists to protect data the host already wrote;
barging in mid-burst to "maintain" would defeat the point.

## 3. The host side is AXI4 + APB

Every controller in the family presents the same host-side shape: an AXI4
slave for the data path and an APB slave for the register block, with the
register map generated from RDL (PeakRDL flow) and registers named, not
offset-numbered, in books. pumice shipped it, scoria inherited it, andesite
inherits it unchanged. A common host shape is what lets the family's
controllers swap under the same software.

## 4. Markings are relative, and they match everywhere

A controller derived from a predecessor marks every block INHERITED,
MODIFIED, or NEW — relative to the named predecessor (scoria marks against
pumice; andesite marks against scoria). A block's marking is a property of
the block, not of the chapter it's in: the ch02 table, the ch03 prose, the
block diagram's colors, and the MAS inventory all carry the same marking for
the same block. When they drift, that's a defect in whichever surface caved,
and the fix is to make them agree, not to argue about which was "first."

## 5. The evidentiary rule

Every claim in a family book is one of three things: (a) inherited from a
named source (cite the source), (b) cited to a JEDEC or DFI clause (cite the
clause), or (c) recorded as an open question in the book's integration
chapter. Nothing else gets asserted. The corollary for this era of the family:
no DFI 4.0 spec is on disk, so every DFI 4.0 claim whose clause can't be
verified in-house carries the `§TBC(TASK-005)` suffix — a named task confirms
or corrects it, and invented clause numbers would read as evidence when
they're really guesses.
