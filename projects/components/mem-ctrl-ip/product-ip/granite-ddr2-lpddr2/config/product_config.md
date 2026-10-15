# granite product configuration

The chosen configuration for the granite SKU (DDR2/LPDDR2, v2) — the single
source of truth for "what makes this SKU this SKU". Structural choices live
in `rtl/includes/granite_pkg.sv`; this file records the reasoning and the
values still open. Per common_has ch5.2 a product is a configuration of the
common stack, not a new RTL tree — the plane selection itself is
`rtl/filelists/top/granite.f`.

Status: **first build in progress 2026-10-11** — storage plane dissolved into
a storage-lite `mc_xddr2_entry_store`, refresh option set reduced, and the
real `granite_core.sv` top composed. No values below are committed silicon;
anything marked TBD is decided at bring-up.

## Plane selection

| Common plane | granite configuration |
|---|---|
| `mc_axi4_plane` | Lite SKU widths at instantiation (data width per board fabric — TBD). |
| `mc_xddr2_entry_store` | **Storage-lite seam** (ch5.2 v2 default): `GRANITE_SEAM_N = 8`, in-order seam — allocates in-order so the seam behaves as an N-deep FIFO per direction while the scheduler argmaxes over the entry vectors (same pick machinery pumice runs at `NUM_ENTRIES = 8`). Depth 8 hides the read round-trip latency (~5 outstanding needed at BL8). Storage "off" shrinks toward one, never to zero. Replaces `mc_storage_plane`. |
| `mc_init_plane` | JEDEC init sequencing, mode-register shadow + CL/CWL/BL decode, DFI PHY init handshake, `init_state_o` telemetry. Common to both xDDR2 rocks; identical instantiation in pumice. |
| `mc_scheduler_plane` | Full pick machinery (FR-FCFS + age), external-init mode (`HAS_INIT_SEQUENCER=0`, `HAS_MODE_REGISTER=0`): init commands arrive from `mc_init_plane` through the external-init port. Common v2 children: `mc_xddr2_refresh_ctrl` (reduced option set), `mc_page_policy`. Command history checker omitted in this SKU. |
| `mc_training_plane` | Shell composing the common LPDDR2 clients: `mc_lpddr2_zq_ctrl`, `mc_lpddr2_dq_cal`. DDR2 has no ZQ/DQ-cal maintenance requirement. |
| `mc_storage_plane` | **Absent** — replaced by `mc_xddr2_entry_store` above. |
| `mc_ras_plane` | **Absent** — true bypass: no transform pair instantiated, no scrub; only the reserved CSR decode. Omission, not a parameter. |
| `mc_dfi_2p1_plane` | Full — command / write / read pipelines + aclk↔dfi_clk CDC, encoding via `mc_xddr2_cmd_formatter`. |

Never-omitted check (ch5.2): entry store present (`mc_xddr2_entry_store`,
one entry per direction), write-data staging present
(`GRANITE_WR_DATA_BUF_WORDS = 16`, SKU minimum, never zero), aclk↔dfi_clk
CDC present (in the DFI plane), maintenance request/grant present (training
plane). A product that cannot refresh correctly is not a smaller product, it
is a broken one.

The v2 generation needs no bank groups, no FGR, no DBI, no CA parity — none
appear in this SKU.

## Refresh option set

Granite configures `mc_xddr2_refresh_ctrl` with the reduced option set:

| Option | granite value | note |
|---|---|---|
| `HAS_POSTPONE`     | 0 | Busy-side postpone credit disabled; strict tREFI. |
| `HAS_PULLIN`       | 0 | Idle pull-ahead credit disabled. |
| `HAS_REFPB`        | 0 | REFab only; per-bank refresh disabled. |
| `HAS_DRAIN_BURST`  | 0 | Drain-burst / streak counter disabled. |

Pumice (research reference) keeps all options at their default 1.

## Parameters / knobs

Committed in `granite_pkg.sv`: `GRANITE_SEAM_N`, `GRANITE_ENTRY_STORE_DEPTH`,
`GRANITE_WR_DATA_BUF_WORDS`, `GRANITE_ACLK_MHZ`, `GRANITE_DFI_MHZ`.
**Every timer CSR is an mc_clk cycle count derived from the
frequency plan — a frequency change invalidates the whole set** (common HAS
frequency warning). Granite A7 plan: 75 MHz sys / 300 MT/s DDR2-300, with
`GRANITE_SYS_66` selectable at build time for the 66.67 MHz / DDR2-266 fallback.

Open at bring-up: AXI data/ID widths, pool depths beyond the lite floor,
timer CSR values, ODT behavior (v2 boards wire it statically).

## CSR baseline

`regs/granite_csr.rdl` — derived address-for-address from `pumice_csr.rdl`
(owner ruling: one CSR base for the family; absent features stay RESERVED
at their addresses, never deleted). Telemetry/stats instrumentation and the
refresh advanced options (postpone/pull-in/REFpb) are reserved; knobs that
are granite parameters (`wr_batch_max`, `gear_ratio`) are read-only at the
`granite_pkg` values. Generated artifacts (regblock + docs + regmap, 66
regs / 170 fields) live in `regs/generated/`.

## Board

TBD: Nexys A7-class product board. Constraint source and PHY part commit at
build.
