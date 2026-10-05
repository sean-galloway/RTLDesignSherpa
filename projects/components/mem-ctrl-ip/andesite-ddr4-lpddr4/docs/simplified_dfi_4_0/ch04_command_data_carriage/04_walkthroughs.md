# Wire-Level Walkthroughs

These walkthroughs use a deliberately tiny teaching model so the DFI signals are visible without
being lost in real memory geometry.

## The simplified model

- One rank, one x8 data slice.
- 1:4 frequency ratio: four phases (`_p0`..`_p3`) per DFI clock, four read data words (`_w0`..`_w3`)
  per DFI clock.
- Two banks: B0, B1.
- One row per bank: R0.
- Burst length 8 (BL8), so a single column read returns 8 contiguous data words.
- Timing assumptions (illustrative only):
  - `tphy_wrlat` = 2 DFI clocks
  - `tphy_wrdata` = 1 DFI clock
  - `trddata_en` = 2 DFI clocks
  - `tphy_rdlat` = 3 DFI clocks

The model is unrealistic in size but correct in wire-level behavior.

## Walkthrough 1: activate -> read -> data return

The MC wants to read from bank B0, row R0, column C0.

At DFI clock T0, phase p0, the MC drives the ACT command:

| Signal | Value | Comment |
| --- | --- | --- |
| `dfi_cs_p0` | 0 (active) | Chip select asserted |
| `dfi_act_n_p0` | 0 | ACT form |
| `dfi_ras_n_p0` | A16 value | Row bit, plus command encoding |
| `dfi_cas_n_p0` | A15 value | Row bit, plus command encoding |
| `dfi_we_n_p0` | A14 value | Row bit, plus command encoding |
| `dfi_address_p0` | Row[13:0] | R0 |
| `dfi_bank_p0` | B0 | Bank select |
| `dfi_bg_p0` | BG0 | Bank group, if present |

: ACT command driven at T0/p0

After DRAM timing (tRCD) the MC issues the RD command at T4, phase p0:

| Signal | Value | Comment |
| --- | --- | --- |
| `dfi_cs_p0` | 0 | Chip select asserted |
| `dfi_act_n_p0` | 1 | Non-ACT form |
| `dfi_ras_n_p0` | 1 | RAS high for read |
| `dfi_cas_n_p0` | 0 | CAS low for read |
| `dfi_we_n_p0` | 1 | WE high for read |
| `dfi_address_p0` | Column + A10=0 | C0, no auto-precharge |
| `dfi_bank_p0` | B0 | Same bank |

: RD command driven at T4/p0

Two DFI clocks after the read command, at T6, the MC asserts `dfi_rddata_en` for the expected
burst duration (BL8 = 8 DRAM clocks = 2 DFI clocks at 1:4):

| Clock | `dfi_rddata_en_p0` | `dfi_rddata_en_p1` | `dfi_rddata_en_p2` | `dfi_rddata_en_p3` |
| --- | --- | --- | --- | --- |
| T6 | 1 | 1 | 1 | 1 |
| T7 | 1 | 1 | 1 | 1 |

: Read enable assertion for BL8 at 1:4 ratio

Three DFI clocks after `dfi_rddata_en` asserts, at T9, the PHY returns `dfi_rddata_valid` and
`dfi_rddata`:

| Clock | `dfi_rddata_valid` | `dfi_rddata_w0` | `dfi_rddata_w1` | `dfi_rddata_w2` | `dfi_rddata_w3` |
| --- | --- | --- | --- | --- | --- |
| T9 | 1 | D0 | D1 | D2 | D3 |
| T10 | 1 | D4 | D5 | D6 | D7 |

: Read data return for BL8

The read data words D0-D7 correspond to the 8-word burst starting at column C0.

## Walkthrough 2: activate -> write with mask

The MC wants to write to bank B1, row R0, column C0, masking byte 0 of the first data beat.

At T0 the MC issues ACT for B1/R0 as in Walkthrough 1, with `dfi_bank_p0` = B1.

After tRCD, at T4 the MC issues WR:

| Signal | Value | Comment |
| --- | --- | --- |
| `dfi_cs_p0` | 0 | Chip select asserted |
| `dfi_act_n_p0` | 1 | Non-ACT form |
| `dfi_ras_n_p0` | 1 | RAS high for write |
| `dfi_cas_n_p0` | 0 | CAS low for write |
| `dfi_we_n_p0` | 0 | WE low for write |
| `dfi_address_p0` | Column + A10=0 | C0, no auto-precharge |
| `dfi_bank_p0` | B1 | Same bank |

: WR command driven at T4/p0

Two DFI clocks after the write command, at T6, the MC asserts `dfi_wrdata_en`. One DFI clock
later, at T7, write data appears on `dfi_wrdata` and the mask on `dfi_wrdata_mask`:

| Clock | `dfi_wrdata_en` | `dfi_wrdata_w0` | `dfi_wrdata_mask_w0` |
| --- | --- | --- | --- |
| T7 | 1 | beat 0 (byte 0 masked) | 0x01 |
| T8 | 1 | beat 1 | 0x00 |

: Write data and mask for BL8

The mask value `0x01` means byte 0 of beat 0 is masked; the DRAM keeps its previous value for
that byte.

## Walkthrough 3: back-to-back reads with chip-select hold

In a single-rank system `dfi_rddata_cs` is driven inactive-high. The PHY still expects it to be valid
so it can verify the data path. This walkthrough shows two back-to-back BL8 reads to the same
open row.

At T0 the MC has already activated B0/R0. At T4 it issues RD C0. At T5 it issues RD C8 (next
burst-aligned column). Because both reads target the same rank, `dfi_rddata_cs` remains constant.

| Clock | Command | `dfi_rddata_en` start | `dfi_rddata_valid` start |
| --- | --- | --- | --- |
| T4 | RD C0 | T6 | T9 |
| T5 | RD C8 | T7 | T10 |

: Back-to-back reads at 1:4 ratio

The read enable windows for the two commands overlap. The PHY must return valid for each
command independently; the `dfi_rddata_valid` windows are T9-T10 for the first read and T10-T11
for the second read. The MC's read aligner unions or frames the enable windows to capture each
burst correctly.

**Source:** DFI Specification v4.0 sections 3.1, 3.2, 3.3, 4.2, 4.5, 4.6
