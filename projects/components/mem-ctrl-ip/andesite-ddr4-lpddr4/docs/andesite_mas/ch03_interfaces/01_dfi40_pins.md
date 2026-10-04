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

# DFI 4.0 Pin-Level Table `§TBC(TASK-005)`

This page pins the boundary the HAS's Chapter 4 names: every signal HAS
Table 4.1 lists appears here as a pin-level row — name, direction, clock
domain, reset value, and the source block that drives or consumes it. The
HAS carries the argument; this table is what the DV framework's DFI signal
catalog checks against when the BFM exists (andesite TASK-005).

Citation discipline, restated from the HAS because it matters more here: the
DFI 4.0 `§TBC(TASK-005)` specification is not on disk. Signal *names* are
public and stated plainly; a DFI 4.0 `§TBC(TASK-005)` clause claim always
carries its suffix on the same line, and the "behavior" column states what
andesite does, not what a clause number says.

Reset convention for the whole table: DFI outputs reset to the de-asserted,
command-inactive level (chip selects high, command pins high, data enables
low); DFI inputs are qualified by their valid/enable companions and need no
reset value. Per-signal reset conventions of DFI 4.0 itself are `§TBC(TASK-005)`
until the spec lands.

## Command and address pins

| Pin | Dir | Clock | Reset | Source block | Behavior |
|---|---|---|---|---|---|
| `dfi_cs_n` | out | DFI ctrl | 1 | [cmd_formatter](../ch02_blocks/01_cmd_formatter.md) | chip select, active low; rank select from `rank_i` |
| `dfi_act_n` | out | DFI ctrl | 1 | [cmd_formatter](../ch02_blocks/01_cmd_formatter.md) | activate select; 0 marks the ACT form `§TBC(TASK-005)` |
| `dfi_ras_n` | out | DFI ctrl | 1 | [cmd_formatter](../ch02_blocks/01_cmd_formatter.md) | command pin; A16 during non-ACT commands |
| `dfi_cas_n` | out | DFI ctrl | 1 | [cmd_formatter](../ch02_blocks/01_cmd_formatter.md) | command pin; A15 during non-ACT commands |
| `dfi_we_n` | out | DFI ctrl | 1 | [cmd_formatter](../ch02_blocks/01_cmd_formatter.md) | command pin; A14 during non-ACT commands |
| `dfi_bank` | out | DFI ctrl | 0 | [cmd_formatter](../ch02_blocks/01_cmd_formatter.md) | bank address (DDR4: BA[1:0]; LPDDR4 via CA path) |
| `dfi_bg` | out | DFI ctrl | 0 | [cmd_formatter](../ch02_blocks/01_cmd_formatter.md) | bank-group address BG[1:0], DDR4 only |
| `dfi_address` | out | DFI ctrl | 0 | [cmd_formatter](../ch02_blocks/01_cmd_formatter.md) | address bus; row on ACT, column on RD/WR, MR data on MRS |
| `dfi_cke` | out | DFI ctrl | 0 | [cmd_formatter](../ch02_blocks/01_cmd_formatter.md) | clock enable; ownership held by init until READY (HAS Ch 3.2 seam) |
| `dfi_reset_n` | out | DFI ctrl | 0 | [init_sequencer](../ch02_blocks/02_init_sequencer.md) | DRAM RESET#, driven through the init window; presented under its DFI name at the boundary (scoria convention, HAS Ch 4.1) |
| `dfi_parity_in` | out | DFI ctrl | 0 | [cmd_formatter](../ch02_blocks/01_cmd_formatter.md) | CA parity generation point; qualified by `parity_en_i` |
| `dfi_alert_n` | in | DFI ctrl | — | NEW alert handling at the boundary | parity/training alert return from PHY; logged by the formatter, recovery owned by the sequencer (HAS Ch 3.2) |
| `ca_o[5:0]` | out | DFI ctrl (DDR) | 0 | [cmd_formatter](../ch02_blocks/01_cmd_formatter.md) LPDDR4 CA submodule | LPDDR4 CA bus, double-data-rate, two cycles per command |
| `ca_valid_o` | out | DFI ctrl | 0 | [cmd_formatter](../ch02_blocks/01_cmd_formatter.md) LPDDR4 CA submodule | marks both CA beat cycles |

: Table 3.1: DFI 4.0 command and address pins (clauses §TBC(TASK-005))

`dfi_cid` (chip ID) is not driven at `NUM_RANKS = 1`; it is presented constant,
the same disposition scoria recorded for the v3.1 data-phase chip selects (HAS
Ch 4.1). A multi-rank build drives it from the granted command's rank.

## Gear-down

| Pin | Dir | Clock | Reset | Source block | Behavior |
|---|---|---|---|---|---|
| gear-down entry signalling | out | DFI ctrl | idle | [init_sequencer](../ch02_blocks/02_init_sequencer.md) | the entry pulse that switches both sides of the boundary to half-rate CA; the DFI 4.0 signal name and handshake clauses are `§TBC(TASK-005)` — named here so the absence of an invented name is a decision |

: Table 3.2: Gear-down entry

## Training and leveling pins

| Pin | Dir | Clock | Reset | Source block | Behavior |
|---|---|---|---|---|---|
| `dfi_phylvl_req_cs_n` | out | DFI ctrl | 1 | [training](../ch02_blocks/09_training.md) | leveling request, per chip select; inherited scheme (HAS Ch 4.1) |
| `dfi_phylvl_ack_cs_n` | in | DFI ctrl | — | [training](../ch02_blocks/09_training.md) | leveling acknowledge, per chip select |
| `dfi_phy_wrlvl_cs_n` | out | DFI ctrl | 1 | [training](../ch02_blocks/09_training.md) | selects write leveling |
| `dfi_phy_rdlvl_cs_n` | out | DFI ctrl | 1 | [training](../ch02_blocks/09_training.md) | selects read leveling; unused by scoria, driven by `rdlvl_ifc` |
| `dfi_phy_rdlvl_gate_cs_n` | out | DFI ctrl | 1 | [training](../ch02_blocks/09_training.md) | read-gate leveling select; presented, exercised per BFM capability (HAS Q3) |
| `dfi_phy_calvl_cs_n` | out | DFI ctrl | 1 | [training](../ch02_blocks/09_training.md) | selects CA training; driven by `ca_train_ifc` |
| `dfi_lvl_pattern` | out | DFI ctrl | 0 | [training](../ch02_blocks/09_training.md) | training pattern select |
| `dfi_lvl_periodic` | out | DFI ctrl | 0 | [training](../ch02_blocks/09_training.md) | periodic-training control |
| `dfi_ca_capture` | in | DFI ctrl | — | [training](../ch02_blocks/09_training.md) | CA-training observation return from PHY |

: Table 3.3: Training and leveling pins

## Data-path pins (DBI and the inherited surface)

| Pin | Dir | Clock | Reset | Source block | Behavior |
|---|---|---|---|---|---|
| `dfi_wrdata` / `dfi_wrdata_mask` | out | DFI data phases | 0 | [dfi_datapath](../ch02_blocks/10_dfi_datapath.md) | write data and mask; phase-multiplied `_pN`, inherited |
| `dfi_wrdata_en` / `dfi_wrdata_cs_n` | out | DFI data phases | 0 | [dfi_datapath](../ch02_blocks/10_dfi_datapath.md) | write data enable; per-phase chip select driven constant at one rank (scoria convention) |
| `dfi_wrdata_dbi` | out | DFI data phases | 0 | [dfi_datapath](../ch02_blocks/10_dfi_datapath.md) | write DBI, per byte; qualified by the MR5 write-DBI enable |
| `dfi_rddata` / `dfi_rddata_valid` | in | DFI data phases | — | [dfi_datapath](../ch02_blocks/10_dfi_datapath.md) | read data and valid; inherited capture |
| `dfi_rddata_dbi` | in | DFI data phases | — | [dfi_datapath](../ch02_blocks/10_dfi_datapath.md) | read DBI, per byte; presented alongside `dfi_rddata` |
| `dfi_rddata_cs_n` | out | DFI data phases | 1 | [dfi_datapath](../ch02_blocks/10_dfi_datapath.md) | per-data-phase chip select, constant `'0` at one rank (inherited) |
| `dfi_error` / `dfi_error_info` | in | DFI ctrl | — | boundary (alert handling) | error indication and info; scoria's surface, DDR4 CA-parity detail now used (HAS Ch 4.1) |
| `dfi_init` | out | DFI ctrl | active | [init_sequencer](../ch02_blocks/02_init_sequencer.md) | initialization-in-progress indication; inherited surface |
| `dfi_lp_ctrl_req` / `dfi_lp_data_req` | out | DFI ctrl | 0 | dormant (`powerdown_ctrl` pair) | exposed per the timeout-and-report rule; nothing consumes them at this design point (HAS Ch 3.1) |

: Table 3.4: Data-path and inherited pins

## What this table does not do

It does not restate the inherited datapath's phase structure (the `_pN`
buses and the 1:4 ratio are argued in HAS Ch 4.1 and owned by
[dfi_datapath](../ch02_blocks/10_dfi_datapath.md)), and it assigns no DFI
4.0 clause numbers — every clause claim here is `§TBC(TASK-005)`, and
confirmation is andesite TASK-005's close condition, at which point each
suffix becomes a citation or a correction.
