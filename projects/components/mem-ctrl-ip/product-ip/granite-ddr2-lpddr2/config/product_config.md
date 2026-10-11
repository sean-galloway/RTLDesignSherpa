# granite product configuration

The chosen configuration for the granite SKU (DDR2/LPDDR2, v2) — the single
source of truth for "what makes this SKU this SKU". Structural choices live
in `rtl/includes/granite_pkg.sv`; this file records the reasoning and the
values still open. Per common_has ch5.2 a product is a configuration of the
common stack, not a new RTL tree — the layer selection itself is
`rtl/filelists/top/granite.f`.

Status: **configuration scaffolded 2026-10-11** — RTL top pending the
wrapper-dissolution task (TASK-001 in this product's vault area). No values
below are committed silicon; anything marked TBD is decided at bring-up.

## Layer selection

| Common layer | granite configuration |
|---|---|
| `mc_axi4_layer` | Lite SKU widths at instantiation (data width per board fabric — TBD). |
| `mc_storage_layer` | **Lite** (ch5.2 v2 default): `GRANITE_SEAM_N = 1`, in-order seam; `GRANITE_ENTRY_STORE_DEPTH = 1` — the entry store shrinks toward one, never to zero. |
| `mc_scheduler_layer` | Full pick machinery (FR-FCFS + age). Common v2 children compose per stage-3 wrapper dissolution: `mc_xddr2_init_sequencer`, `mc_xddr2_mode_register`, `mc_xddr2_refresh_ctrl`, `mc_page_policy` (+ optional `mc_cmd_history_checker`). |
| `mc_training_layer` | Shell composing the common LPDDR2 clients: `mc_lpddr2_zq_ctrl`, `mc_lpddr2_dq_cal`. DDR2 has no ZQ/DQ-cal maintenance requirement. |
| `mc_ras_layer` | **Absent** — true bypass: no transform pair instantiated, no scrub; only the reserved CSR decode. Omission, not a parameter. |
| `mc_dfi_2p1_layer` | Full — command / write / read pipelines + aclk↔dfi_clk CDC, encoding via `mc_xddr2_cmd_formatter`. |

Never-omitted check (ch5.2): entry store present (storage lite retains
one), write-data staging present (`GRANITE_WR_DATA_BUF_WORDS = 16`, SKU
minimum, never zero), aclk↔dfi_clk CDC present (in the DFI layer),
maintenance request/grant present (training layer). A product that cannot
refresh correctly is not a smaller product, it is a broken one.

The v2 generation needs no bank groups, no FGR, no DBI, no CA parity —
none appear in this SKU.

## Parameters / knobs

Committed in `granite_pkg.sv`: `GRANITE_SEAM_N`, `GRANITE_ENTRY_STORE_DEPTH`,
`GRANITE_WR_DATA_BUF_WORDS`, `GRANITE_ACLK_MHZ`, `GRANITE_DFI_MHZ`.
**Every timer CSR is an mc_clk cycle count derived from the
frequency plan — a frequency change invalidates the whole set** (common HAS
frequency warning); the MHz values are placeholders until a board commits
them (75 MHz is the pumice-proven Nexys A7-class point).

Open at bring-up: AXI data/ID widths, pool depths beyond the lite floor,
timer CSR values, ODT behavior (v2 boards wire it statically).

## CSR baseline

TBD: derived from the pumice CSR surface narrowed to this SKU — no RAS
surface beyond the reserved decode, no research-harness knobs (command
history, telemetry sweep). PeakRDL `regs/` lands with the first build.

## Board

TBD: Nexys A7-class product board. Constraint source and PHY part commit at
build.
