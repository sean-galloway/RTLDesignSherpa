# diorite product configuration

The chosen configuration for the diorite SKU — the single source of truth
for "what makes this SKU this SKU". Filled at build time; every row that is
not yet decided stays `TBD` rather than guessing.

Status: **scaffold** (2026-10-11) — no values committed yet; the research
rock it consumes (andesite) is itself not yet built.

## Layer selection

| Common layer | Configuration for diorite |
|---|---|
| `mc_axi4_layer` | TBD |
| `mc_storage_layer` | Full |
| `mc_scheduler_layer` | TBD |
| `mc_training_layer` | DDR4/LPDDR4 client set — TBD |
| `mc_ras_layer` | Per SKU need — ECC candidate, doctrine-9 gated |
| `mc_dfi_4p0_layer` | Full — shared pipeline + v4 command surface: bank groups (`cmd_bg`), gear-down phase mask, CA parity / `alert_n`, DBI (gear-down and CA parity §TBC in the common MAS at scaffold time) |

Never-omitted check (ch5.2): entry store, write-data staging, CDC,
maintenance request/grant — all present in the full configuration above.

## Parameters / knobs

TBD at build: frequencies, burst profile, pool depths, timer CSRs
(frequency-bound; see the common HAS frequency warning).

## CSR baseline

TBD.

## Board

TBD: owner Kintex-7 board (planned); constraint source and PHY part
committed at build.
