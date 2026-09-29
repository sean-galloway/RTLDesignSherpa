# ISSUE-007: ORDER_MODE overlays miss 75 MHz: CLOSED by shortening the pre-pick stage

> **Migrated from `PUMICE-024`** on 2026-09-27, when this area's flat
> `closed.md` was split into one file per item to match the rest of the vault.
> The legacy ID is cited throughout the repo -- RTL comments, DV code, handbook
> notes, commit messages and session memory -- so it is NOT rewritten at those
> call sites; `vault/Tasks/MIGRATION_MAP.md` and this line are how an old
> `PUMICE-024` reference resolves. Body below is verbatim from the flat page.
>
> Lane chosen by reading this item's own Status line and opening, not its title:
> a keyword pass over the 35 items misclassified 14 of them.


**Status:** closed 2026-09-09 — the ENHANCED tier now closes post-route

The overlays missed 75 MHz by 21-53 ps depending on the placer. Root cause was
not the overlays themselves but where the arbiter did its slot-to-data muxing:
the output stage indexed the CAMs' flat {bank,row,col} vectors with the
REGISTERED pre-pick slot, so six NUM_ENTRIES:1 muxes sat AFTER the pre-pick
flop and fed r_bank/r_row/r_col. That was the reported critical path in every
build (`r_*_pop -> ... -> r_bank`).

Fix: mux at the pre-pick flop instead, registering the already-narrow
{bank,row,col} per class. The wide muxes move into the STAGE-1b cycle where
arg_sel has already resolved and there is slack, and the output stage keeps
only the small class-priority mux. `rd_col_ap` already used exactly this
pattern, so it is the established idiom rather than a new one. Sampling one
cycle earlier is also more coherent: a CAM entry's key is fixed at insert and
the forward guards prevent re-selecting a just-selected slot, so the operands
now come from the same epoch as the decision.

Post-route at 75 MHz, same flow, before -> after:

| Build | Before | After |
|---|---|---|
| base | +0.010 ns, 0 failing | +0.009 ns, 0 failing |
| ENHANCED | -0.021 ns, 4 failing | **+0.005 ns, 0 failing of 72896** |

The base tier was already closing so it does not move (both figures are inside
the placement band); the enhanced tier closes for the first time. Cost is about
144 flops and 0.19% LUT. The same change also shortens the prepick-guard cone,
which feeds the mask build.

Validation: pumice fub 96 / macro 3 / top 119, zero failures; char sim 31
passed + 2 xfailed, zero unexpected.
