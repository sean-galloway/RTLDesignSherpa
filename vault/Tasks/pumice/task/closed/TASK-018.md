# TASK-018: Retire the deskew RTL + PHY_TIMING.deskew_lo/hi CSR

> **Migrated from `PUMICE-007`** on 2026-09-27, when this area's flat
> `closed.md` was split into one file per item to match the rest of the vault.
> The legacy ID is cited throughout the repo -- RTL comments, DV code, handbook
> notes, commit messages and session memory -- so it is NOT rewritten at those
> call sites; `vault/Tasks/MIGRATION_MAP.md` and this line are how an old
> `PUMICE-007` reference resolves. Body below is verbatim from the flat page.
>
> Lane chosen by reading this item's own Status line and opening, not its title:
> a keyword pass over the 35 items misclassified 14 of them.


**Status:** closed 2026-08-24 — already done by 38c8ae63 (Jul 22), the day before this page was stamped open

The deskew path was superseded (see PUMICE-008 in `dropped.md`): the board read
fix was the PUMICE-005 bring-up tuple at deskew 0/0. The RTL and its CSR fields
remain and cost area/timing. Delete rather than train — but only after the
board is re-validated on a rebuilt bitstream so the removal is not entangled
with an active bring-up.

**Resolution (2026-08-24):** the fourth stale entry from the Jul 23 vault
migration (with 002/003/004). `38c8ae63` had already retired the whole
experiment — aligner delay-lines, DESKEW_W threading, PHY_TIMING.deskew_lo/hi
(RDL regenerated), train_deskew/validate_reads, Makefile/ILA hooks — and the
same commit closed board bring-up with reads working on the rebuilt bitstream,
which was this task's stated precondition. Verified against the tree: zero
deskew references in rtl/, the regmap, or the board area; the only survivor is
the historical removal note in pumice_csr.rdl.
