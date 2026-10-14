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

# FUB Breakdown

This section inventories the post-Phase-2 pumice block breakdown. Pumice is now
a consumer of the common-ip memory-controller stack plus a small set of
rock-specific FUBs. The family-wide architecture, ownership rules, and plane
stack are documented in
[common-ip HAS ch05](../../../../../common-ip/docs/common_has/ch05_lineup/01_common_ip_layout.md);
per-block microarchitecture is in
[common-ip MAS](../../../../../common-ip/docs/common_mas/common_mas_index.md).
The rest of this chapter only records which common blocks pumice uses and where
they are wired.

## 1. What pumice consumes from common-ip

Pumice imports the family package and instantiates five common planes
directly, with no pumice-side wrappers; its choices are parameters on those
planes. The shared leaf FUBs live inside the planes; pumice does not
instantiate them directly.

| Common block | common_mas chapter | Pumice instantiation site |
|---|---|---|
| `mc_common_pkg` | [ch01 — package](../../../../../common-ip/docs/common_mas/ch01_package/01_mc_common_pkg.md) | imported in [`pumice_core.sv:30`](../../../rtl/top/pumice_core.sv) and the common macros that compose it |
| `mc_axi4_plane` | [ch02 — host-side plane](../../../../../common-ip/docs/common_mas/ch02_axi4_plane/01_mc_axi4_plane.md) | [`pumice_core.sv:376`](../../../rtl/top/pumice_core.sv) (`u_axi_plane`) |
| `mc_axi_burst_chopper` | [ch02 — host-side plane](../../../../../common-ip/docs/common_mas/ch02_axi4_plane/01_mc_axi4_plane.md) | inside `mc_axi4_plane` ([`pumice_core.sv:376`](../../../rtl/top/pumice_core.sv)) |
| `mc_wr_splitter` | [ch02 — host-side plane](../../../../../common-ip/docs/common_mas/ch02_axi4_plane/01_mc_axi4_plane.md) | inside `mc_axi4_plane` ([`pumice_core.sv:376`](../../../rtl/top/pumice_core.sv)) |
| `mc_wr_intake` | [ch02 — host-side plane](../../../../../common-ip/docs/common_mas/ch02_axi4_plane/01_mc_axi4_plane.md) | inside `mc_axi4_plane` ([`pumice_core.sv:376`](../../../rtl/top/pumice_core.sv)) |
| `mc_rd_intake` | [ch02 — host-side plane](../../../../../common-ip/docs/common_mas/ch02_axi4_plane/01_mc_axi4_plane.md) | inside `mc_axi4_plane` ([`pumice_core.sv:376`](../../../rtl/top/pumice_core.sv)) |
| `mc_rd_return_ring` | [ch02 — host-side plane](../../../../../common-ip/docs/common_mas/ch02_axi4_plane/01_mc_axi4_plane.md) | inside `mc_axi4_plane` ([`pumice_core.sv:376`](../../../rtl/top/pumice_core.sv)) |
| `mc_addr_mapper` | [ch02 — host-side plane](../../../../../common-ip/docs/common_mas/ch02_axi4_plane/01_mc_axi4_plane.md) | inside `mc_wr_intake`/`mc_rd_intake` of `mc_axi4_plane` ([`pumice_core.sv:376`](../../../rtl/top/pumice_core.sv)) |
| `mc_storage_plane` | [ch03 — entry-pool plane](../../../../../common-ip/docs/common_mas/ch03_storage_plane/01_mc_storage_plane.md) | [`pumice_core.sv:504`](../../../rtl/top/pumice_core.sv) (`u_store_plane`) |
| `mc_wr_data_cam` | [ch03 — entry-pool plane](../../../../../common-ip/docs/common_mas/ch03_storage_plane/01_mc_storage_plane.md) | inside `mc_storage_plane` ([`pumice_core.sv:504`](../../../rtl/top/pumice_core.sv)) |
| `mc_rd_cmd_cam` | [ch03 — entry-pool plane](../../../../../common-ip/docs/common_mas/ch03_storage_plane/01_mc_storage_plane.md) | inside `mc_storage_plane` ([`pumice_core.sv:504`](../../../rtl/top/pumice_core.sv)) |
| `mc_scheduler_plane` | [ch04 — scheduler plane](../../../../../common-ip/docs/common_mas/ch04_scheduler_plane/01_mc_scheduler_plane.md) | [`pumice_core.sv:601`](../../../rtl/top/pumice_core.sv) (`u_sched_plane`) |
| `mc_bank_timers` | [ch04 — scheduler plane](../../../../../common-ip/docs/common_mas/ch04_scheduler_plane/01_mc_scheduler_plane.md) | inside `mc_scheduler_plane` |
| `mc_bank_timer` | [ch04 — scheduler plane](../../../../../common-ip/docs/common_mas/ch04_scheduler_plane/01_mc_scheduler_plane.md) | inside `mc_bank_timers` inside `mc_scheduler_plane` |
| `mc_global_timers` | [ch04 — scheduler plane](../../../../../common-ip/docs/common_mas/ch04_scheduler_plane/01_mc_scheduler_plane.md) | inside `mc_scheduler_plane` |
| `mc_cmd_arbiter` | [ch04 — scheduler plane](../../../../../common-ip/docs/common_mas/ch04_scheduler_plane/01_mc_scheduler_plane.md) | inside `mc_scheduler_plane` |
| `mc_training_plane` | [ch05 — training plane](../../../../../common-ip/docs/common_mas/ch05_training_plane/01_mc_training_plane.md) | [`pumice_core.sv:756`](../../../rtl/top/pumice_core.sv) (`u_train_plane`) |
| `mc_dfi_2p1_plane` | [ch07 — DFI 2.1 plane](../../../../../common-ip/docs/common_mas/ch07_dfi_2p1_plane/01_mc_dfi_2p1_plane.md) | [`pumice_core.sv:803`](../../../rtl/top/pumice_core.sv) (`u_dfi_plane`) |
| `mc_dfi_cdc` | [ch07 — DFI 2.1 plane](../../../../../common-ip/docs/common_mas/ch07_dfi_2p1_plane/01_mc_dfi_2p1_plane.md) | inside `mc_dfi_2p1_plane` ([`pumice_core.sv:803`](../../../rtl/top/pumice_core.sv)) |
| `mc_dfi_cmd_path` | [ch07 — DFI 2.1 plane](../../../../../common-ip/docs/common_mas/ch07_dfi_2p1_plane/01_mc_dfi_2p1_plane.md) | inside `mc_dfi_2p1_plane` ([`pumice_core.sv:803`](../../../rtl/top/pumice_core.sv)) |
| `mc_dfi_wr_serializer` | [ch07 — DFI 2.1 plane](../../../../../common-ip/docs/common_mas/ch07_dfi_2p1_plane/01_mc_dfi_2p1_plane.md) | inside `mc_dfi_2p1_plane` ([`pumice_core.sv:803`](../../../rtl/top/pumice_core.sv)) |
| `mc_dfi_rd_aligner` | [ch07 — DFI 2.1 plane](../../../../../common-ip/docs/common_mas/ch07_dfi_2p1_plane/01_mc_dfi_2p1_plane.md) | inside `mc_dfi_2p1_plane` ([`pumice_core.sv:803`](../../../rtl/top/pumice_core.sv)) |
| `mc_dfi_3p1_cmd_path` | [ch08 — DFI 3.1 plane](../../../../../common-ip/docs/common_mas/ch08_dfi_3p1_plane/01_mc_dfi_3p1_plane.md) | not used by pumice (scoria) |
| `mc_dfi_4p0_cmd_path` | [ch09 — DFI 4.0 plane](../../../../../common-ip/docs/common_mas/ch09_dfi_4p0_plane/01_mc_dfi_4p0_plane.md) | not used by pumice (andesite) |

## 2. What pumice owns

Pumice owns no leaf FUBs any more. The DDR2/LPDDR2-generation
initialization, mode-register, refresh, page-policy, training, and
DFI-encoding FUBs it used to own now live in common-ip and are composed
directly by the common `mc_scheduler_plane`, `mc_training_plane`, and
`mc_dfi_2p1_plane` macros in `pumice_core`. Pumice owns the tops
(`pumice_top_geared`, `pumice_top`, `pumice_core`), `pumice_pkg`, the
`pumice_csr` register description, and the build-time selection of these
children:

| Block | Role | Location |
|---|---|---|
| `mc_xddr2_init_sequencer` | DDR2/LPDDR2 JEDEC MR/init cold-boot engine. | [`common-ip/rtl/fub/mc_xddr2_init_sequencer.sv`](../../../../../common-ip/rtl/fub/mc_xddr2_init_sequencer.sv), composed inside `mc_scheduler_plane` ([`pumice_core.sv:601`](../../../rtl/top/pumice_core.sv)) |
| `mc_xddr2_mode_register` | Per-rank MR shadow + live decode to CL/CWL/BL/AL. | [`common-ip/rtl/fub/mc_xddr2_mode_register.sv`](../../../../../common-ip/rtl/fub/mc_xddr2_mode_register.sv), composed inside `mc_scheduler_plane` |
| `mc_xddr2_refresh_ctrl` | tREFI down-counter, postponer, and REFab/REFpb dispatch. | [`common-ip/rtl/fub/mc_xddr2_refresh_ctrl.sv`](../../../../../common-ip/rtl/fub/mc_xddr2_refresh_ctrl.sv), composed inside `mc_scheduler_plane` |
| `mc_page_policy` | Runtime page-policy engine and command telemetry. | [`common-ip/rtl/fub/mc_page_policy.sv`](../../../../../common-ip/rtl/fub/mc_page_policy.sv), composed inside `mc_scheduler_plane` |
| `mc_xddr2_cmd_formatter` | JEDEC command encoding into DFI v2.1 wires (DDR2 truth table / LPDDR2 CA bus, OP `0x56`/`0xAB` for ZQ). | [`common-ip/rtl/fub/mc_xddr2_cmd_formatter.sv`](../../../../../common-ip/rtl/fub/mc_xddr2_cmd_formatter.sv); instantiated inside common `mc_dfi_cmd_path`, which pumice consumes via `mc_dfi_2p1_plane`. |
| `mc_lpddr2_zq_ctrl` (common-ip) | Periodic LPDDR2 ZQ calibration maintenance (MRW to MR10). | [`common-ip rtl/fub/mc_lpddr2_zq_ctrl.sv`](../../../../../common-ip/rtl/fub/mc_lpddr2_zq_ctrl.sv), composed inside `mc_training_plane` ([`pumice_core.sv:756`](../../../rtl/top/pumice_core.sv)) |
| `mc_lpddr2_dq_cal` (common-ip) | One-shot LPDDR2 DQ calibration interface (MRR MR32/MR40). | [`common-ip rtl/fub/mc_lpddr2_dq_cal.sv`](../../../../../common-ip/rtl/fub/mc_lpddr2_dq_cal.sv), composed inside `mc_training_plane` |

## 3. Retired and absorbed blocks

The pre-Phase-2 pumice-local plane macros and their leaf FUBs have been
replaced by common-ip equivalents. The old names may still appear in retired
sentinel tests and filelist comments; they are not part of the current build.

| Retired/absorbed block | Status after Phase-2 |
|---|---|
| `pumice_axi4_plane` | Replaced by common `mc_axi4_plane` ([`pumice_core.sv:376`](../../../rtl/top/pumice_core.sv)). |
| `pumice_wr_intake` / `pumice_rd_intake` | Replaced by common `mc_wr_intake` / `mc_rd_intake` inside `mc_axi4_plane`. |
| `pumice_wr_data_cam` / `pumice_rd_cmd_cam` | Replaced by common `mc_wr_data_cam` / `mc_rd_cmd_cam` inside `mc_storage_plane` ([`pumice_core.sv:504`](../../../rtl/top/pumice_core.sv)). |
| `pumice_bank_timers` (local) | Replaced by common `mc_bank_timers` inside `mc_scheduler_plane`. |
| `pumice_cmd_arbiter` (behavioral core) | Replaced by common `mc_cmd_arbiter` inside `mc_scheduler_plane`. The pumice port-adapter wrapper was **removed 2026-10-11** — never instantiated in the default build (it survived only as the issue-rate test DUT); history in git. |
| `pumice_scheduler_plane` (behavioral macro) | **Removed 2026-10-11** — its init/refresh/page-policy children are now composed directly by common `mc_scheduler_plane` ([`pumice_core.sv:601`](../../../rtl/top/pumice_core.sv)). |
| `pumice_training_plane` (behavioral macro) | **Removed 2026-10-11** — its LPDDR2 ZQ/DQ-cal clients are now composed directly by common `mc_training_plane` ([`pumice_core.sv:756`](../../../rtl/top/pumice_core.sv)). |
| `pumice_dfi_cdc` / `pumice_dfi_cmd_path` / `pumice_dfi_wr_serializer` / `pumice_dfi_rd_aligner` | Pumice-local DFI wrappers retired; common `mc_dfi_2p1_plane` owns the CDC and datapath ([`pumice_core.sv:803`](../../../rtl/top/pumice_core.sv)). |
| `txn_queue` | Replaced by the two common CAMs: `mc_wr_data_cam` + `mc_rd_cmd_cam`. |
| `bank_machine` | Replaced by FSM-free common `mc_bank_timer`, stamped by `mc_bank_timers`. |
| `xbank_timers` | Replaced by common `mc_global_timers` (turnaround) + `mc_bank_timers` (per-bank). |
| `cmd_encoder` | Replaced by common `mc_dfi_cmd_path` (which instantiates common `mc_xddr2_cmd_formatter`). |
| `odt_ctrl` | ODT handling now lives inside `mc_xddr2_cmd_formatter` / `mc_xddr2_mode_register`; no standalone block. |
| `page_predictor` (standalone) | Open-page decision is inline in common `mc_cmd_arbiter`; runtime policy is provided by common `mc_page_policy`. The adaptive modes retired 2026-09-27 (`mc_page_policy`: the `adapt_time`/`adapt_access` encodings 4/5 now fall through to the build default). |
| `wr_cmd_cam` | Replaced by common `mc_wr_data_cam`. |
| `scheduler` | Replaced by common `mc_scheduler_plane`. |
| `gear_dfi` | Replaced by common `mc_dfi_2p1_plane`. |
| `axi_frontend` / `axi_intake` / `*_macro`-as-architecture | Replaced by common `mc_axi4_plane`, generated `pumice_csr`, and `pumice_core`. |
| `powerdown_ctrl` | **Removed 2026-10-11** — was never wired into the default `pumice_core` build; no replacement block (low-power entry is a scheduler maintenance concern, not a standalone FUB). |
| `dfi_signal_pack` | **Removed 2026-10-11** — final DFI register stage dropped; common `mc_dfi_cmd_path` drives the bus from the formatter's registered outputs. |
| `addr_mapper` (local copy) | **Removed 2026-10-11** — the local copy was never instantiated; address mapping is the common `mc_addr_mapper`, instantiated inside `mc_wr_intake` / `mc_rd_intake`. |

Verified host-width freedom via [`pumice_top_geared`](../../../rtl/top/pumice_top_geared.sv) remains {64, 128, 256}.
