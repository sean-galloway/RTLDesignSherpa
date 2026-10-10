# ISSUE-009: three coverage gaps behind green runs

> **Migrated from `PUMICE-032`** on 2026-09-27, when this area's flat
> `closed.md` was split into one file per item to match the rest of the vault.
> The legacy ID is cited throughout the repo -- RTL comments, DV code, handbook
> notes, commit messages and session memory -- so it is NOT rewritten at those
> call sites; `vault/Tasks/MIGRATION_MAP.md` and this line are how an old
> `PUMICE-032` reference resolves. Body below is verbatim from the flat page.
>
> Lane chosen by reading this item's own Status line and opening, not its title:
> a keyword pass over the 35 items misclassified 14 of them.


**Status:** CLOSED 2026-09-11  **Priority:** was P2
**Found by:** the PUMICE-031 sweep.

1. **Silicon-bug guards in no regression.** `test_a7ddrphy_bl4_anchored`,
   `_gear_mismatch`, `_read_window` and `test_axi_rd_device_word_check` sat at
   the dv/tests root, which no area collects. They are now the `phy/` area, in
   the dispatcher's AREAS: 16 pass, 2 skip. The skips are gear_mismatch's own,
   disproven on silicon, and it keeps its reason. `4f7dda96b`.
2. **The macro DFI-layer test ran at gear 0.** It never drove `gear_i`,
   `n_subcmd_i` or the strides, which read 0 under Verilator, so a
   DFI_RATE=2 build ran with phase 1's enables masked. A model that only asked
   whether an enable was non-zero passed anyway. It now drives the board
   default and rejects any partial enable; a gear-0 mutant goes red.
   `b53e2b822`.
3. **A requirement cited a skipped test.** design-requirements.md's
   "gear=MAX bit-identical" row cited "macro regression (109)" (3 tests now)
   and the skipped `test_a7ddrphy_gear_mismatch`. It now names the real
   enforcement: the mask is all-ones by construction, every core/top TB runs
   at gear = MAX, and the item-2 check catches a masked phase. `b53e2b822`.

Side effect: the pre-commit filelist check crashed on a tracked `.sby` that
another session's in-flight rename had deleted, blocking every commit in the
repo. Fixed in `36a971588`.

Not done: `dfi_init_complete_i` is still undriven in the DFI-layer test, which
does not exercise init. No test runs gear < MAX, and the requirement does not
ask for one.
