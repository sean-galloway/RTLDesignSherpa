# granite product configuration

The chosen configuration for the granite SKU — the single source of truth
for "what makes this SKU this SKU". Filled at build time; every row that is
not yet decided stays `TBD` rather than guessing.

Status: **scaffold** (2026-10-11) — no values committed yet.

## Layer selection

| Common layer | Configuration for granite |
|---|---|
| `mc_axi4_layer` | TBD (data width, ID width per board AXI fabric) |
| `mc_storage_layer` | **Lite** — N=1 in-order seam; entry store at minimum (ch5.2 v2 default) |
| `mc_scheduler_layer` | TBD (prospect-pool depth, age CSRs — frequency-dependent; see the common HAS frequency warning) |
| `mc_training_layer` | DDR2/LPDDR2 clients from the pumice-proven set (ZQ, MRR/DQ-cal, write-leveling interface) — exact client list TBD |
| `mc_ras_layer` | **Absent** — true bypass, reserved CSR decode only (ch5.2 v2 default) |
| `mc_dfi_2p1_layer` | Full — command / write / read pipelines + CDC |

Never-omitted check (ch5.2): entry store present (storage lite retains it),
write-data staging present (at SKU minimum), aclk↔dfi_clk CDC present (in the DFI
layer), maintenance request/grant present (training layer).

## Parameters / knobs

TBD at build: frequencies (aclk / dfi_clk / UI), burst profile, write-data
buffer depth, timer CSR values (committed only with a frequency — a change
of frequency invalidates the whole set; see the common HAS warning).

## CSR baseline

TBD: pumice CSR surface narrowed to the product's layers (no RAS surface
beyond reserved decode).

## Board

TBD: Nexys A7-class product board; constraint source and PHY part committed
at build.
