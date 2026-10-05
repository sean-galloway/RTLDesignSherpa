# Wire-Level Walkthroughs

These walkthroughs use a tiny teaching model so the DFI timing is visible at a
glance.

## Teaching model

- Two banks: B0 and B1.
- One rank, one chip select.
- DFI 2.1, 1:2 frequency ratio, so there are two phases per DFI clock:
  `_p0` and `_p1`.
- Burst length 4, one data word per phase, so BL4 fits in one DFI clock.
- `tphy_wrlat` = 1, `tphy_wrdata` = 1 for writes; `trddata_en` = 2,
  `tphy_rdlat` = 5 for reads.
- The controller places ACT on phase 0 and the first subsequent RD/WR on the
  programmed read or write phase.

## Walkthrough 1: Activate to Read

Assume the MC wants to read from an idle bank B0, row R3.

Cycle 0, phase 0: `dfi_cs_n` = 0, `dfi_ras_n` = 0, `dfi_cas_n` = 1,
`dfi_we_n` = 1, `dfi_bank` = B0, `dfi_address` = R3. This is the ACT command.
Cycle 0, phase 1 is a NOP: `dfi_cs_n` = 1.

After the DRAM's tRCD has passed, the MC issues a read.

Cycle 2, phase 0: NOP.
Cycle 2, phase 1: `dfi_cs_n` = 0, `dfi_ras_n` = 1, `dfi_cas_n` = 0,
`dfi_we_n` = 1, `dfi_bank` = B0, `dfi_address` = column C1 with A10 = 0 for no
auto-precharge. This is the RD command.

Two cycles after the RD command, at cycle 4, the MC asserts `dfi_rddata_en`.
It stays asserted for two phases to cover the BL4 burst.

Cycle 4, phase 0: `dfi_rddata_en_p0` = 1.
Cycle 4, phase 1: `dfi_rddata_en_p1` = 1.

The PHY returns the first valid data no later than `tphy_rdlat` = 5 cycles
after the enable. Suppose it returns early at cycle 5.

Cycle 5, phase 0: `dfi_rddata_w0` valid, `dfi_rddata_valid_w0` = 1.
Cycle 5, phase 1: `dfi_rddata_w1` valid, `dfi_rddata_valid_w1` = 1.

The MC captures the two words and delivers them as the BL4 read response.

## Walkthrough 2: Activate to Write

Assume the MC wants to write to bank B1, row R5.

Cycle 0, phase 0: `dfi_cs_n` = 0, `dfi_ras_n` = 0, `dfi_cas_n` = 1,
`dfi_we_n` = 1, `dfi_bank` = B1, `dfi_address` = R5. ACT command.
Cycle 0, phase 1: NOP.

After tRCD, the MC issues the write.

Cycle 2, phase 0: NOP.
Cycle 2, phase 1: `dfi_cs_n` = 0, `dfi_ras_n` = 1, `dfi_cas_n` = 0,
`dfi_we_n` = 0, `dfi_bank` = B1, `dfi_address` = column C2 with A10 = 0. WR
command.

One cycle after the write command, at cycle 3, the MC asserts
`dfi_wrdata_en_p0` and `dfi_wrdata_en_p1`. Because `tphy_wrdata` = 1, the data
follows one cycle later at cycle 4.

Cycle 3, phase 0: `dfi_wrdata_en_p0` = 1.
Cycle 3, phase 1: `dfi_wrdata_en_p1` = 1.

Cycle 4, phase 0: `dfi_wrdata_p0` = first data word, `dfi_wrdata_mask_p0` = 0.
Cycle 4, phase 1: `dfi_wrdata_p1` = second data word, `dfi_wrdata_mask_p1` = 0.

If the MC wanted to mask the lower byte of the first beat, it would set
`dfi_wrdata_mask_p0[0]` = 1.

## What the traces show

The control interface carries the command. The write/read data enables predict
when data is expected, and the data valid signal bounds the actual return. The
PHY is free to delay read data up to `tphy_rdlat`, but the MC must have
scheduled `dfi_rddata_en` based on `trddata_en`. For writes, the command leads
the enable by `tphy_wrlat`, and the enable leads the data by `tphy_wrdata`.

**Source:** DFI Specification v2.1.1 sections 3.1, 3.2, 3.3, 4.2, 4.3, 4.4
