# gabbro product configuration

The chosen configuration for the gabbro SKU — the single source of truth
for "what makes this SKU this SKU". Filled at build time; every row that is
not yet decided stays `TBD` rather than guessing.

Status: **scaffold** (2026-10-11) — no values committed yet.

## Layer selection

| Common layer | Configuration for gabbro |
|---|---|
| `mc_axi4_layer` | TBD |
| `mc_storage_layer` | Full (v3 benefits from reordering; no lite default) |
| `mc_scheduler_layer` | TBD; refresh base = scoria-proven **elastic refresh (v3)** once converged into the common layer |
| `mc_training_layer` | DDR3/LPDDR3 client set — TBD |
| `mc_ras_layer` | Per SKU need — ECC candidate, doctrine-9 gated (params select the feature set; no area for unused features) |
| `mc_dfi_3p1_layer` | Full — 2p1 pipeline + v3.1 generation surface (command dfi_3p1, leveling handshake) |

Never-omitted check (ch5.2): entry store, write-data staging, CDC,
maintenance request/grant — all present in the full configuration above.

## Parameters / knobs

TBD at build: frequencies, burst profile, pool depths, timer CSRs
(frequency-bound; see the common HAS frequency warning).

## CSR baseline

TBD.

## Board

TBD: owner Kintex-7 board (planned, shared with the LPDDR2/3/4 bring-up
plan); constraint source and PHY part committed at build.
