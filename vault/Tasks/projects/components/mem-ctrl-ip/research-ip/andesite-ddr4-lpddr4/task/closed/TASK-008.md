# TASK-008: LPDDR4 book reconciliation -- inline CKE, bank count, CA cycle detail
> Source: `/mnt/data/github/dfi-specs/lpddr4/index.md` design-topics and
> deltas list

**Priority:** P2
**Status:** closed 2026-10-04 — completed and owner-directed (pre-RTL creation pass)
**Owner:** TBD

Three deltas between the research index and the andesite books, one of them a
direct conflict with the settled design point:

1. **CKE removal.** JESD209-4 removes the dedicated CKE pin; the CKE function
   rides inline on the CA bus. The MAS formatter's interface table drives
   `dfi_cke` unconditionally — reconcile what the LPDDR4 path drives (DFI
   still carries `dfi_cke` for DDR4; the LPDDR4 CA path must encode
   CKE-equivalent state). Books' dormant/power-down story (HAS Ch 3.1)
   interacts.
2. **Bank count — RESOLVED 2026-10-04 (owner ruling).** The research index
   claimed bank groups for LPDDR4; the owner ruled it wrong — bank groups
   come online with DDR5/LPDDR5, and the andesite design point (8 banks per
   channel, no bank groups, grep-gated across the books) stands. The index
   has been corrected in place (`/mnt/data/github/dfi-specs/lpddr4/index.md`,
   operator research storage, no repo commit). The books required no change.
3. **CA cycle detail.** The index says RD/WR span 2 CA cycles and ACT splits
   into ACT-1/ACT-2; the MAS says "two cycles per command" flat. Add the
   per-command cycle structure to the CA submodule page at the next MAS edit
   pass, cited to JESD209-4E.

Closes when all three are resolved as book edits (with the geometry gate
re-run green) or as recorded decisions.
