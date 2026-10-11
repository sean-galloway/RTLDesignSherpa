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
rock-specific FUBs. The family-wide architecture, ownership rules, and layer
stack are documented in
[common-ip HAS ch05](../../../../../common-ip/docs/common_has/ch05_lineup/01_common_ip_layout.md);
per-block microarchitecture is in
[common-ip MAS](../../../../../common-ip/docs/common_mas/common_mas_index.md).
The rest of this chapter only records which common blocks pumice uses and where
they are wired.

## 1. What pumice consumes from common-ip

Pumice imports the family package and instantiates four common layers through
thin wrappers where pumice-specific behavior is required. The shared leaf FUBs
live inside those layers; pumice does not instantiate them directly.

| Common block | common_mas chapter | Pumice instantiation site |
|---|---|---|
| `mc_common_pkg` | [ch01 — package](../../../../../common-ip/docs/common_mas/ch01_package/01_mc_common_pkg.md) | imported in [`pumice_core.sv:30`](../../../rtl/top/pumice_core.sv) and [`pumice_scheduler_layer.sv:24`](../../../rtl/macro/pumice_scheduler_layer.sv) |
| `mc_axi4_layer` | [ch02 — host-side layer](../../../../../common-ip/docs/common_mas/ch02_axi4_layer/01_mc_axi4_layer.md) | [`pumice_core.sv:376`](../../../rtl/top/pumice_core.sv) (`u_ifc`) |
| `mc_axi_burst_chopper` | [ch02 — host-side layer](../../../../../common-ip/docs/common_mas/ch02_axi4_layer/01_mc_axi4_layer.md) | inside `mc_axi4_layer` ([`pumice_core.sv:376`](../../../rtl/top/pumice_core.sv)) |
| `mc_wr_splitter` | [ch02 — host-side layer](../../../../../common-ip/docs/common_mas/ch02_axi4_layer/01_mc_axi4_layer.md) | inside `mc_axi4_layer` ([`pumice_core.sv:376`](../../../rtl/top/pumice_core.sv)) |
| `mc_wr_intake` | [ch02 — host-side layer](../../../../../common-ip/docs/common_mas/ch02_axi4_layer/01_mc_axi4_layer.md) | inside `mc_axi4_layer` ([`pumice_core.sv:376`](../../../rtl/top/pumice_core.sv)) |
| `mc_rd_intake` | [ch02 — host-side layer](../../../../../common-ip/docs/common_mas/ch02_axi4_layer/01_mc_axi4_layer.md) | inside `mc_axi4_layer` ([`pumice_core.sv:376`](../../../rtl/top/pumice_core.sv)) |
| `mc_rd_return_ring` | [ch02 — host-side layer](../../../../../common-ip/docs/common_mas/ch02_axi4_layer/01_mc_axi4_layer.md) | inside `mc_axi4_layer` ([`pumice_core.sv:376`](../../../rtl/top/pumice_core.sv)) |
| `mc_addr_mapper` | [ch02 — host-side layer](../../../../../common-ip/docs/common_mas/ch02_axi4_layer/01_mc_axi4_layer.md) | inside `mc_wr_intake`/`mc_rd_intake` of `mc_axi4_layer` ([`pumice_core.sv:376`](../../../rtl/top/pumice_core.sv)) |
| `mc_storage_layer` | [ch03 — entry-pool layer](../../../../../common-ip/docs/common_mas/ch03_storage_layer/01_mc_storage_layer.md) | [`pumice_core.sv:504`](../../../rtl/top/pumice_core.sv) (`u_storage`) |
| `mc_wr_data_cam` | [ch03 — entry-pool layer](../../../../../common-ip/docs/common_mas/ch03_storage_layer/01_mc_storage_layer.md) | inside `mc_storage_layer` ([`pumice_core.sv:504`](../../../rtl/top/pumice_core.sv)) |
| `mc_rd_cmd_cam` | [ch03 — entry-pool layer](../../../../../common-ip/docs/common_mas/ch03_storage_layer/01_mc_storage_layer.md) | inside `mc_storage_layer` ([`pumice_core.sv:504`](../../../rtl/top/pumice_core.sv)) |
| `mc_scheduler_layer` | [ch04 — scheduler layer](../../../../../common-ip/docs/common_mas/ch04_scheduler_layer/01_mc_scheduler_layer.md) | [`pumice_scheduler_layer.sv:315`](../../../rtl/macro/pumice_scheduler_layer.sv) (`u_core`) |
| `mc_bank_timers` | [ch04 — scheduler layer](../../../../../common-ip/docs/common_mas/ch04_scheduler_layer/01_mc_scheduler_layer.md) | inside `mc_scheduler_layer` ([`pumice_scheduler_layer.sv:315`](../../../rtl/macro/pumice_scheduler_layer.sv)) |
| `mc_bank_timer` | [ch04 — scheduler layer](../../../../../common-ip/docs/common_mas/ch04_scheduler_layer/01_mc_scheduler_layer.md) | inside `mc_bank_timers` inside `mc_scheduler_layer` |
| `mc_global_timers` | [ch04 — scheduler layer](../../../../../common-ip/docs/common_mas/ch04_scheduler_layer/01_mc_scheduler_layer.md) | inside `mc_scheduler_layer` ([`pumice_scheduler_layer.sv:315`](../../../rtl/macro/pumice_scheduler_layer.sv)) |
| `mc_cmd_arbiter` | [ch04 — scheduler layer](../../../../../common-ip/docs/common_mas/ch04_scheduler_layer/01_mc_scheduler_layer.md) | inside `mc_scheduler_layer` ([`pumice_scheduler_layer.sv:315`](../../../rtl/macro/pumice_scheduler_layer.sv)) |
| `mc_training_layer` | [ch05 — training layer](../../../../../common-ip/docs/common_mas/ch05_training_layer/01_mc_training_layer.md) | [`pumice_training_layer.sv:176`](../../../rtl/macro/pumice_training_layer.sv) (`u_shell`) |
| `mc_dfi_2p1_layer` | [ch07 — DFI 2.1 layer](../../../../../common-ip/docs/common_mas/ch07_dfi_2p1_layer/01_mc_dfi_2p1_layer.md) | [`pumice_core.sv:766`](../../../rtl/top/pumice_core.sv) (`u_dfi`) |
| `mc_dfi_cdc` | [ch07 — DFI 2.1 layer](../../../../../common-ip/docs/common_mas/ch07_dfi_2p1_layer/01_mc_dfi_2p1_layer.md) | inside `mc_dfi_2p1_layer` ([`pumice_core.sv:766`](../../../rtl/top/pumice_core.sv)) |
| `mc_dfi_cmd_path` | [ch07 — DFI 2.1 layer](../../../../../common-ip/docs/common_mas/ch07_dfi_2p1_layer/01_mc_dfi_2p1_layer.md) | inside `mc_dfi_2p1_layer` ([`pumice_core.sv:766`](../../../rtl/top/pumice_core.sv)) |
| `mc_dfi_wr_serializer` | [ch07 — DFI 2.1 layer](../../../../../common-ip/docs/common_mas/ch07_dfi_2p1_layer/01_mc_dfi_2p1_layer.md) | inside `mc_dfi_2p1_layer` ([`pumice_core.sv:766`](../../../rtl/top/pumice_core.sv)) |
| `mc_dfi_rd_aligner` | [ch07 — DFI 2.1 layer](../../../../../common-ip/docs/common_mas/ch07_dfi_2p1_layer/01_mc_dfi_2p1_layer.md) | inside `mc_dfi_2p1_layer` ([`pumice_core.sv:766`](../../../rtl/top/pumice_core.sv)) |
| `mc_dfi_3p1_cmd_path` | [ch08 — DFI 3.1 layer](../../../../../common-ip/docs/common_mas/ch08_dfi_3p1_layer/01_mc_dfi_3p1_layer.md) | not used by pumice (scoria) |
| `mc_dfi_4p0_cmd_path` | [ch09 — DFI 4.0 layer](../../../../../common-ip/docs/common_mas/ch09_dfi_4p0_layer/01_mc_dfi_4p0_layer.md) | not used by pumice (andesite) |

## 2. What pumice owns

Pumice retains the rock-specific initialization, mode-register, refresh,
page-policy, training, and DFI-encoding FUBs, plus thin wrappers around the
common scheduler and training shells.

| Block | Role | Location |
|---|---|---|
| `mc_xddr2_init_sequencer` | DDR2/LPDDR2 JEDEC MR/init cold-boot engine. | [`common-ip/rtl/fub/mc_xddr2_init_sequencer.sv`](../../../../../common-ip/rtl/fub/mc_xddr2_init_sequencer.sv), instantiated in [`pumice_scheduler_layer.sv:193`](../../../rtl/macro/pumice_scheduler_layer.sv) |
| `mc_xddr2_mode_register` | Per-rank MR shadow + live decode to CL/CWL/BL/AL. | [`common-ip/rtl/fub/mc_xddr2_mode_register.sv`](../../../../../common-ip/rtl/fub/mc_xddr2_mode_register.sv), instantiated in [`pumice_scheduler_layer.sv:225`](../../../rtl/macro/pumice_scheduler_layer.sv) |
| `mc_xddr2_refresh_ctrl` | tREFI down-counter, postponer, and REFab/REFpb dispatch. | [`common-ip/rtl/fub/mc_xddr2_refresh_ctrl.sv`](../../../../../common-ip/rtl/fub/mc_xddr2_refresh_ctrl.sv), instantiated in [`pumice_scheduler_layer.sv:248`](../../../rtl/macro/pumice_scheduler_layer.sv) |
| `mc_page_policy` | Runtime page-policy engine and command telemetry. | [`common-ip/rtl/fub/mc_page_policy.sv`](../../../../../common-ip/rtl/fub/mc_page_policy.sv), instantiated in [`pumice_scheduler_layer.sv:276`](../../../rtl/macro/pumice_scheduler_layer.sv) |
| `mc_xddr2_cmd_formatter` | JEDEC command encoding into DFI v2.1 wires (DDR2 truth table / LPDDR2 CA bus, OP `0x56`/`0xAB` for ZQ). | [`common-ip/rtl/fub/mc_xddr2_cmd_formatter.sv`](../../../../../common-ip/rtl/fub/mc_xddr2_cmd_formatter.sv); instantiated inside common `mc_dfi_cmd_path`, which pumice consumes via `mc_dfi_2p1_layer`. |
| `mc_lpddr2_zq_ctrl` (common-ip) | Periodic LPDDR2 ZQ calibration maintenance (MRW to MR10). | [`common-ip rtl/fub/mc_lpddr2_zq_ctrl.sv`](../../../../../common-ip/rtl/fub/mc_lpddr2_zq_ctrl.sv), instantiated in [`pumice_training_layer.sv:108`](../../../rtl/macro/pumice_training_layer.sv) |
| `mc_lpddr2_dq_cal` (common-ip) | One-shot LPDDR2 DQ calibration interface (MRR MR32/MR40). | [`common-ip rtl/fub/mc_lpddr2_dq_cal.sv`](../../../../../common-ip/rtl/fub/mc_lpddr2_dq_cal.sv), instantiated in [`pumice_training_layer.sv:131`](../../../rtl/macro/pumice_training_layer.sv) |
| `pumice_scheduler_layer` | Thin pumice wrapper around common `mc_scheduler_layer`; holds the rock init/refresh/page-policy FUBs. | [`rtl/macro/pumice_scheduler_layer.sv`](../../../rtl/macro/pumice_scheduler_layer.sv), instantiated in [`pumice_core.sv:601`](../../../rtl/top/pumice_core.sv) |
| `pumice_training_layer` | Thin pumice wrapper around common `mc_training_layer`; holds the rock ZQ/DQ-cal FUBs. | [`rtl/macro/pumice_training_layer.sv`](../../../rtl/macro/pumice_training_layer.sv), instantiated in [`pumice_core.sv:725`](../../../rtl/top/pumice_core.sv) |
| `pumice_cmd_arbiter` | Thin pumice wrapper around common `mc_cmd_arbiter`; preserved historical port list. | [`rtl/fub/pumice_cmd_arbiter.sv`](../../../rtl/fub/pumice_cmd_arbiter.sv); not instantiated in the default [`pumice_core`](../../../rtl/top/pumice_core.sv) build (the scheduler wrapper uses common `mc_scheduler_layer` instead). |

## 3. Retired and absorbed blocks

The pre-Phase-2 pumice-local layer macros and their leaf FUBs have been
replaced by common-ip equivalents. The old names may still appear in retired
sentinel tests and filelist comments; they are not part of the current build.

| Retired/absorbed block | Status after Phase-2 |
|---|---|
| `pumice_axi4_layer` | Replaced by common `mc_axi4_layer` ([`pumice_core.sv:376`](../../../rtl/top/pumice_core.sv)). |
| `pumice_wr_intake` / `pumice_rd_intake` | Replaced by common `mc_wr_intake` / `mc_rd_intake` inside `mc_axi4_layer`. |
| `pumice_wr_data_cam` / `pumice_rd_cmd_cam` | Replaced by common `mc_wr_data_cam` / `mc_rd_cmd_cam` inside `mc_storage_layer` ([`pumice_core.sv:504`](../../../rtl/top/pumice_core.sv)). |
| `pumice_bank_timers` (local) | Replaced by common `mc_bank_timers` inside `mc_scheduler_layer`. |
| `pumice_cmd_arbiter` (behavioral core) | Replaced by common `mc_cmd_arbiter` inside `mc_scheduler_layer`. The pumice-wrapper file remains but is not in the default build. |
| `pumice_scheduler_layer` (behavioral macro) | Now a thin wrapper around common `mc_scheduler_layer` ([`pumice_scheduler_layer.sv:315`](../../../rtl/macro/pumice_scheduler_layer.sv)). |
| `pumice_training_layer` (behavioral macro) | Now a thin wrapper around common `mc_training_layer` ([`pumice_training_layer.sv:176`](../../../rtl/macro/pumice_training_layer.sv)). |
| `pumice_dfi_cdc` / `pumice_dfi_cmd_path` / `pumice_dfi_wr_serializer` / `pumice_dfi_rd_aligner` | Pumice-local DFI wrappers retired; common `mc_dfi_2p1_layer` owns the CDC and datapath ([`pumice_core.sv:766`](../../../rtl/top/pumice_core.sv)). |
| `txn_queue` | Replaced by the two common CAMs: `mc_wr_data_cam` + `mc_rd_cmd_cam`. |
| `bank_machine` | Replaced by FSM-free common `mc_bank_timer`, stamped by `mc_bank_timers`. |
| `xbank_timers` | Replaced by common `mc_global_timers` (turnaround) + `mc_bank_timers` (per-bank). |
| `cmd_encoder` | Replaced by common `mc_dfi_cmd_path` (which instantiates the pumice-owned `dfi_cmd_formatter`). |
| `odt_ctrl` | ODT handling now lives inside `dfi_cmd_formatter` / `mode_register`; no standalone block. |
| `page_predictor` (standalone) | Open-page decision is inline in common `mc_cmd_arbiter`; runtime policy is provided by pumice-owned `pumice_page_policy`. The adaptive modes retired 2026-09-27 (`pumice_page_policy`: the `adapt_time`/`adapt_access` encodings 4/5 now fall through to the build default). |
| `wr_cmd_cam` | Replaced by common `mc_wr_data_cam`. |
| `scheduler` | Replaced by common `mc_scheduler_layer` (via `pumice_scheduler_layer`). |
| `gear_dfi` | Replaced by common `mc_dfi_2p1_layer`. |
| `axi_frontend` / `axi_intake` / `*_macro`-as-architecture | Replaced by common `mc_axi4_layer`, generated `pumice_csr`, and `pumice_core`. |
| `powerdown_ctrl` | **Removed 2026-10-11** — was never wired into the default `pumice_core` build; no replacement block (low-power entry is a scheduler maintenance concern, not a standalone FUB). |
| `dfi_signal_pack` | **Removed 2026-10-11** — final DFI register stage subsumed by common `mc_dfi_cmd_path`, which drives the bus directly. |
| `addr_mapper` (local copy) | **Removed 2026-10-11** — the local copy was never instantiated; the common intakes carry address mapping inline. Common `mc_addr_mapper` remains extracted-but-unadopted in common-ip. |

Verified host-width freedom via [`pumice_top_geared`](../../../rtl/top/pumice_top_geared.sv) remains {64, 128, 256}.
