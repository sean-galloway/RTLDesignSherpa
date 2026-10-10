# Revision Deltas and the andesite Tie-In

## 3.1 -> 4.0 revision deltas

DFI 4.0 is the largest single revision step in the DFI family. The changes fall into several groups.

### DDR4/LPDDR4 data-path additions

| Change | DFI 4.0 handling |
| --- | --- |
| Read/write data chip selects | New `dfi_rddata_cs` and `dfi_wrdata_cs` signals let the PHY compensate data-path timing per rank. |
| Read DBI | New dedicated `dfi_rddata_dbi` bus. |
| Write DBI | Reuses `dfi_wrdata_mask`; no separate `dfi_wrdata_dbi` exists. |
| Write DQ training | New `dfi_wdqlvl_*` signals and timing parameters. |

: Data-path deltas

### Command and control additions

| Change | DFI 4.0 handling |
| --- | --- |
| Bank groups | `dfi_bg` added in 3.0; retained in 4.0. |
| ACT_n | `dfi_act_n` added in 3.0; retained. |
| CA parity | `dfi_parity_in` and `dfi_alert_n` retained from 3.0. |
| Chip ID for 3DS | `dfi_cid` retained from 3.0. |
| LPDDR4 SDR CA | 6-bit CA mapped onto `dfi_address` over two cycles. |
| `tcmd_lat` | New LPDDR4 CS-to-CA delay parameter. |

: Control deltas

### System-level additions

| Change | DFI 4.0 handling |
| --- | --- |
| PHY master interface | New `dfi_phymstr_*` handshake. |
| Disconnect protocol | New `dfi_disconnect_error` plus disconnect timing parameters. |
| Frequency indicator | New `dfi_frequency` signal and `phyfreq_range` parameter. |
| Geardown mode | New `dfi_geardown_en` signal and `tgeardown_delay` parameter. |
| LPDDR4 channels | New `phychannel_en` parameter. |
| DB training | New `dfi_db_train_*` interface for LRDIMM. |
| Inactive CS support | New `syscs_state` parameter. |

: System-level deltas

### Training changes

| Change | DFI 4.0 handling |
| --- | --- |
| Per-slice read leveling | `dfi_rdlvl_en`/`req` and `dfi_rdlvl_gate_en`/`req` became per-slice; grouping via `mcrdlvl_slice_group`/`phyrdlvl_slice_group`. |
| Training chip-select rename | `_cs_n` suffix removed: `dfi_phy_wrlvl_cs`, `dfi_phy_rdlvl_cs`, `dfi_phy_rdlvl_gate_cs`, `dfi_phy_calvl_cs`. |
| PHY Independent Mode | Replaces v3.1 `dfi_phylvl_req_cs_n`/`dfi_phylvl_ack_cs_n`. |
| CA training additions | `dfi_calvl_ca_sel`, `dfi_calvl_data`/`done`/`result`/`strobe`, and associated timing parameters. |
| Write leveling strobe | Now per-slice with assert count via `syswrlvl_strobe_num`. |

: Training deltas

### Removed signal

`dfi_data_byte_disable` was removed in DFI 4.0 and replaced by the `dfidata_bit_enable`
programmable parameter.

## The andesite tie-in

The andesite DDR4/LPDDR4 memory controller targets DFI 4.0 because its predecessor left the
entire 3.1 -> 4.0 delta as "deliberately unimplemented." The andesite design implements that delta.

### Inherited surface

- The async-FIFO datapath, bubble-free, at 1:4 frequency ratio.
- `dfi_init_start`/`dfi_init_complete`, `dfi_error`/`dfi_error_info`, `dfi_reset_n`.
- `dfi_lp_ctrl_req`/`dfi_lp_data_req` presented but unacknowledged-by-default.

### Implemented 4.0 deltas

The andesite HAS Chapter 4.1 and MAS pin table list the implemented changes:

| DFI 4.0 feature | andesite block | Tie-in document |
| --- | --- | --- |
| `dfi_act_n`, `dfi_bg` | `cmd_formatter` (modified) | `docs/andesite_has/ch04_interfaces/01_dfi_v40.md` |
| `dfi_parity_in`, `dfi_alert_n` | `cmd_formatter` + new alert handling | `docs/andesite_has/ch04_interfaces/01_dfi_v40.md` |
| `dfi_wrdata_mask` as write DBI, `dfi_rddata_dbi` | `dfi_datapath` | `docs/andesite_has/ch04_interfaces/01_dfi_v40.md` |
| `dfi_geardown_en` | `init_sequencer` | `docs/andesite_has/ch04_interfaces/01_dfi_v40.md` |
| Training (`dfi_rdlvl_*`, `dfi_calvl_*`, `dfi_wrlvl_*`) | `training` block, `rdlvl_ifc`, `ca_train_ifc`, `wrlvl_ifc` | `docs/andesite_has/ch04_interfaces/01_dfi_v40.md`, `docs/andesite_mas/ch03_interfaces/01_dfi40_pins.md` |
| LPDDR4 CA bus | `cmd_formatter` LPDDR4 CA submodule | `docs/andesite_has/ch04_interfaces/01_dfi_v40.md` |

: andesite implementation of DFI 4.0 deltas

### Study corrections recorded in the area docs

The andesite HAS and MAS record several study corrections made on 2026-10-04:

- The v3.1 per-CS training handshake `dfi_phylvl_req_cs_n`/`dfi_phylvl_ack_cs_n` does not exist
  in DFI 4.0; it is replaced by PHY Independent Mode.
- Training chip selects dropped the `_n` suffix in 4.0.
- There is no `dfi_wrdata_dbi` pin; write DBI reuses `dfi_wrdata_mask`.
- `dfi_ca_capture` was wrong in name and direction; the correct signal is `dfi_calvl_capture`
  (MC-to-PHY).
- `dfi_init` is not a DFI signal; the spec uses `dfi_init_start` and `dfi_init_complete`.

### Verification posture

The andesite verification strategy targets the DFI 4.0 boundary using the in-house CocoTB
framework DFI component. The BFM is DFI 4.0-partial; gaps at the andesite design point (LPDDR4
CA map, design-point JEDEC timing CSVs, gear-down validation, per-slice read leveling, CA VREF
sweep feedback) are listed in `docs/andesite_has/ch06_integration/01_verification_open.md`. The
verification plan exercises init sequences, gear-down entry, CA parity, ODT, FGR, LPDDR4 CA
encoding, training protocols, and the dormant low-power pair.

**Source:** DFI Specification v4.0 revision history and sections 3.6.8, 3.12, 3.13, 3.14; andesite HAS `ch04_interfaces/01_dfi_v40.md`, andesite MAS `ch03_interfaces/01_dfi40_pins.md`, andesite HAS `ch06_integration/01_verification_open.md`
