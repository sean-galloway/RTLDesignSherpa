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

# DFI 4.0 Pin-Level Table

This page pins the boundary the HAS's Chapter 4 names: every signal HAS
Table 4.1 lists appears here as a pin-level row — name, direction, clock
domain, reset value, and the source block that drives or consumes it. The
HAS carries the argument; this table is what the DV framework's DFI signal
catalog checks against when the BFM exists (andesite TASK-005).

Citation discipline, restated from the HAS because it matters more here: the
DFI 4.0 specification is on disk
(`/mnt/data/github/dfi-specs/DDR_PHY_Interface_Specification_v4_0.pdf`) and
was studied on 2026-10-04. Clause references below are real DFI 4.0 section
numbers; any remaining `§TBC(TASK-005)` marks a claim the study could not
confirm. The "behavior" column states what andesite does, not what a clause
number says.

Reset convention for the whole table: DFI outputs reset to the de-asserted,
command-inactive level (chip selects high, command pins high, data enables
low); DFI inputs are qualified by their valid/enable companions and need no
reset value. Per-signal reset conventions of DFI 4.0 itself are listed in
Table 3, "DFI Signal Requirements" (§2.2.3 DFI Signals).

## Command and address pins

| Pin | Dir | Clock | Reset | Source block | Behavior | Citation |
|---|---|---|---|---|---|---|
| `dfi_cs` | out | DFI ctrl | 1 | [cmd_formatter](../ch02_blocks/01_cmd_formatter.md) | chip select; rank select from `rank_i` (v4.0 rename of `dfi_cs_n`) | §3.1 Control Interface |
| `dfi_act_n` | out | DFI ctrl | 1 | [cmd_formatter](../ch02_blocks/01_cmd_formatter.md) | activate select; 0 marks the ACT form | §3.1 Control Interface |
| `dfi_ras_n` | out | DFI ctrl | 1 | [cmd_formatter](../ch02_blocks/01_cmd_formatter.md) | command pin; A16 during non-ACT commands | §3.1 Control Interface |
| `dfi_cas_n` | out | DFI ctrl | 1 | [cmd_formatter](../ch02_blocks/01_cmd_formatter.md) | command pin; A15 during non-ACT commands | §3.1 Control Interface |
| `dfi_we_n` | out | DFI ctrl | 1 | [cmd_formatter](../ch02_blocks/01_cmd_formatter.md) | command pin; A14 during non-ACT commands | §3.1 Control Interface |
| `dfi_bank` | out | DFI ctrl | 0 | [cmd_formatter](../ch02_blocks/01_cmd_formatter.md) | bank address (DDR4: BA[1:0]; LPDDR4 holds idle) | §3.1 Control Interface |
| `dfi_bg` | out | DFI ctrl | 0 | [cmd_formatter](../ch02_blocks/01_cmd_formatter.md) | bank-group address BG[1:0], DDR4 only | §3.1 Control Interface |
| `dfi_address` | out | DFI ctrl | 0 | [cmd_formatter](../ch02_blocks/01_cmd_formatter.md) | address bus; row on ACT, column on RD/WR, MR data on MRS | §3.1 Control Interface |
| `dfi_cke` | out | DFI ctrl | 0 | [cmd_formatter](../ch02_blocks/01_cmd_formatter.md) | clock enable; ownership held by init until READY (HAS Ch 3.2 seam) | §3.1 Control Interface |
| `dfi_reset_n` | out | DFI ctrl | 0 | [init_sequencer](../ch02_blocks/02_init_sequencer.md) | DRAM RESET#, driven through the init window; presented under its DFI name at the boundary (scoria convention, HAS Ch 4.1) | §3.1 Control Interface |
| `dfi_parity_in` | out | DFI ctrl | 0 | [cmd_formatter](../ch02_blocks/01_cmd_formatter.md) | CA parity generation point; qualified by `parity_en_i` | §3.5.7 CRC and CA Parity |
| `dfi_alert_n` | in | DFI ctrl | — | NEW alert handling at the boundary | parity/training alert return from PHY; logged by the formatter, recovery owned by the sequencer (HAS Ch 3.2) | §3.5.7 CRC and CA Parity |
| `ca_o[5:0]` | out | DFI ctrl (DDR) | 0 | [cmd_formatter](../ch02_blocks/01_cmd_formatter.md) LPDDR4 CA submodule | LPDDR4 CA bus, double-data-rate, two cycles per command | §3.14 Channels for LPDDR4 memories |
| `ca_valid_o` | out | DFI ctrl | 0 | [cmd_formatter](../ch02_blocks/01_cmd_formatter.md) LPDDR4 CA submodule | marks both CA beat cycles | andesite internal qualifier |

: Table 3.1: DFI 4.0 command and address pins

`dfi_cid` (chip ID) is not driven at `NUM_RANKS = 1`; it is presented constant,
the same disposition scoria recorded for the v3.1 data-phase chip selects (HAS
Ch 4.1). A multi-rank build drives it from the granted command's rank
(§3.1 Control Interface, §4.3 3DS Stack Support).

## Gear-down

| Pin | Dir | Clock | Reset | Source block | Behavior | Citation |
|---|---|---|---|---|---|---|
| `dfi_geardown_en` | out | DFI ctrl | idle | [init_sequencer](../ch02_blocks/02_init_sequencer.md) | DDR4 geardown enable; when asserted the MC changes CA signals only every other DFI PHY clock (§4.18) | §3.13 Geardown Mode |

: Table 3.2: Gear-down entry

## Training and leveling pins

| Pin | Dir | Clock | Reset | Source block | Behavior | Citation |
|---|---|---|---|---|---|---|
| `dfi_phy_wrlvl_cs` | out | DFI ctrl | 1 | [training](../ch02_blocks/09_training.md) | selects write leveling (v4.0 rename of `dfi_phy_wrlvl_cs_n`) | §3.6 DFI Training Interface |
| `dfi_phy_rdlvl_cs` | out | DFI ctrl | 1 | [training](../ch02_blocks/09_training.md) | selects read leveling; unused by scoria, driven by `rdlvl_ifc` (v4.0 rename of `dfi_phy_rdlvl_cs_n`) | §3.6.1 Read Training Operation |
| `dfi_phy_rdlvl_gate_cs` | out | DFI ctrl | 1 | [training](../ch02_blocks/09_training.md) | read-gate leveling select; presented, exercised per BFM capability (HAS Q3) (v4.0 rename of `dfi_phy_rdlvl_gate_cs_n`) | §3.6.1 Read Training Operation |
| `dfi_phy_calvl_cs` | out | DFI ctrl | 1 | [training](../ch02_blocks/09_training.md) | selects CA training; driven by `ca_train_ifc` (v4.0 rename of `dfi_phy_calvl_cs_n`) | §3.6.4 CA Training Operation |
| `dfi_lvl_pattern` | out | DFI ctrl | 0 | [training](../ch02_blocks/09_training.md) | training pattern select | §3.6.6 dfi_lvl_pattern Encoding |
| `dfi_lvl_periodic` | out | DFI ctrl | 0 | [training](../ch02_blocks/09_training.md) | periodic-training control | §3.6.7 Periodic Training Flag |
| `dfi_calvl_en` | out | DFI ctrl | 0 | [training](../ch02_blocks/09_training.md) | MC enables CA training logic | §3.6.4 CA Training Operation |
| `dfi_calvl_req` | in | DFI ctrl | — | [training](../ch02_blocks/09_training.md) | PHY requests CA training | §3.6.4 CA Training Operation |
| `dfi_calvl_capture` | out | DFI ctrl | 0 | [training](../ch02_blocks/09_training.md) | CA-training capture strobe from MC to PHY | §3.6.4 CA Training Operation |
| `dfi_calvl_resp` | in | DFI ctrl | — | [training](../ch02_blocks/09_training.md) | CA-training response from PHY | §3.6.4 CA Training Operation |
| `dfi_calvl_ca_sel` | out | DFI ctrl | 0 | [training](../ch02_blocks/09_training.md) | CA foreground pattern strobe | §3.6.4 CA Training Operation |
| `dfi_calvl_data` | out | DFI data phases | 0 | [training](../ch02_blocks/09_training.md) | LPDDR4 CA VREF training data (per slice) | §3.6.4 CA Training Operation |
| `dfi_calvl_done` | out | DFI data phases | 0 | [training](../ch02_blocks/09_training.md) | LPDDR4 CA VREF training done | §3.6.4 CA Training Operation |
| `dfi_calvl_result` | in | DFI data phases | — | [training](../ch02_blocks/09_training.md) | LPDDR4 CA VREF training result from PHY | §3.6.4 CA Training Operation |
| `dfi_calvl_strobe` | out | DFI data phases | 0 | [training](../ch02_blocks/09_training.md) | LPDDR4 CA VREF training strobe | §3.6.4 CA Training Operation |

: Table 3.3: Training and leveling pins

## Data-path pins (DBI and the inherited surface)

| Pin | Dir | Clock | Reset | Source block | Behavior | Citation |
|---|---|---|---|---|---|---|
| `dfi_wrdata` / `dfi_wrdata_mask` | out | DFI data phases | 0 | [dfi_datapath](../ch02_blocks/10_dfi_datapath.md) | write data and mask/DBI; `dfi_wrdata_mask` becomes write DBI when DBI is enabled and `phydbi_mode = 0`; phase-multiplied `_pN`, inherited | §3.2.1 Write Data Mask/Write DBI |
| `dfi_wrdata_en` / `dfi_wrdata_cs` | out | DFI data phases | 0 | [dfi_datapath](../ch02_blocks/10_dfi_datapath.md) | write data enable; per-phase chip select driven constant at one rank (scoria convention; v4.0 rename of `dfi_wrdata_cs_n`) | §3.2.2 Write Data Chip Select |
| `dfi_rddata` / `dfi_rddata_valid` | in | DFI data phases | — | [dfi_datapath](../ch02_blocks/10_dfi_datapath.md) | read data and valid; inherited capture | §3.3.5 Read Data Signals and Parameters |
| `dfi_rddata_dbi` | in | DFI data phases | — | [dfi_datapath](../ch02_blocks/10_dfi_datapath.md) | read DBI, per byte; presented alongside `dfi_rddata` | §3.3.1 Read DBI |
| `dfi_rddata_cs` | out | DFI data phases | 1 | [dfi_datapath](../ch02_blocks/10_dfi_datapath.md) | per-data-phase chip select, constant at one rank (inherited; v4.0 rename of `dfi_rddata_cs_n`) | §3.3.2 Read Data Chip Select |
| `dfi_error` / `dfi_error_info` | in | DFI ctrl | — | boundary (alert handling) | error indication and info; scoria's surface, DDR4 CA-parity detail now used (HAS Ch 4.1) | §3.8 Error Interface |
| `dfi_init_start` | out | DFI ctrl | active | [init_sequencer](../ch02_blocks/02_init_sequencer.md) | MC init/frequency-change request; initialization-in-progress indication; inherited surface | §3.5.1 Initialization |
| `dfi_init_complete` | in | DFI ctrl | — | boundary | PHY init complete / frequency-change acknowledge | §3.5.1 Initialization |
| `dfi_lp_ctrl_req` / `dfi_lp_data_req` | out | DFI ctrl | 0 | dormant (`powerdown_ctrl` pair) | exposed per the timeout-and-report rule; nothing consumes them at this design point (HAS Ch 3.1) | §3.7 Low Power Control Interface |

: Table 3.4: Data-path and inherited pins

## Study corrections (2026-10-04, andesite TASK-005)

- **Active-low chip-select names are v3.1, not v4.0.** DFI 4.0 renames
  `dfi_cs_n` → `dfi_cs`, `dfi_wrdata_cs_n` → `dfi_wrdata_cs`,
  `dfi_rddata_cs_n` → `dfi_rddata_cs`, and all training chip selects from
  `dfi_phy_*_cs_n` to `dfi_phy_*_cs` (§3.1, §3.2.2, §3.3.2, §3.6). The
  original table used v3.1 names; this edition uses v4.0 names.
- **`dfi_phylvl_req_cs_n` / `dfi_phylvl_ack_cs_n` are not DFI 4.0 signals.**
  They were defined in v3.1 as PHY-requested training handshakes and are
  superseded in v4.0 by PHY Independent Mode (§3.6.8). They have been
  removed from this v4.0 pin table.
- **`dfi_wrdata_dbi` does not exist.** Write DBI reuses `dfi_wrdata_mask`
  when DBI is enabled and `phydbi_mode = 0` (§3.2.1). The separate
  `dfi_wrdata_dbi` pin has been removed.
- **`dfi_ca_capture` was wrong in name and direction.** The DFI 4.0 signal
  is `dfi_calvl_capture`, it is MC-to-PHY (out), and the PHY-to-MC
  observation returns are `dfi_calvl_resp` and `dfi_calvl_result`
  (§3.6.4).
- **`dfi_init` is not a DFI signal name.** The spec defines `dfi_init_start`
  (MC-to-PHY) and `dfi_init_complete` (PHY-to-MC) (§3.5.1). Both are now
  listed separately.

## What this table does not do

It does not restate the inherited datapath's phase structure (the `_pN`
buses and the 1:4 ratio are argued in HAS Ch 4.1 and owned by
[dfi_datapath](../ch02_blocks/10_dfi_datapath.md)). DFI 4.0 clause numbers
are now cited above; any remaining `§TBC(TASK-005)` marks a claim the study
could not confirm.
