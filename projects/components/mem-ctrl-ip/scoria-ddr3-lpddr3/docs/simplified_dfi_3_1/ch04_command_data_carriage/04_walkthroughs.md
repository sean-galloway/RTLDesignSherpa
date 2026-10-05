# Walkthroughs

These walkthroughs use a deliberately tiny teaching model so that every
DFI wire can be traced by hand.

## Teaching model

- One rank, one chip select (`dfi_cs_n` is a single bit).
- 1:2 frequency ratio: two PHY phases (`p0`, `p1`) per MC clock.
- DFI data width 32 bits, split into two 16-bit PHY data slices.
- Burst length 8 on DRAM, so each read or write moves four DFI data words.
- Fixed timing: `tcmd_lat = 0`, `tctrl_delay = 1`, `tphy_wrlat = 2`,
  `tphy_wrdata = 1`, `trddata_en = 2`, `tphy_rdlat = 4`.

## Walkthrough 1: activate -> read -> data return

The controller wants to read from bank 0, row 5, column 3.

Cycle 0:
- Control interface: `dfi_cs_n = 0`, `dfi_ras_n = 0`, `dfi_cas_n = 1`,
  `dfi_we_n = 1`, `dfi_bank = 0`, `dfi_address = row 5`. This is an ACT.
- `dfi_cke = 1`, `dfi_odt` driven to its programmed value.

Cycle 1:
- Control interface: `dfi_cs_n = 1` (NOP / deselect).

Cycle 4:
- After `tRCD` DRAM timing has been satisfied, the MC issues a read.
- Control interface: `dfi_cs_n = 0`, `dfi_ras_n = 1`, `dfi_cas_n = 0`,
  `dfi_we_n = 1`, `dfi_bank = 0`, `dfi_address = column 3`.

Cycle 6:
- `trddata_en = 2` cycles after the read, the MC asserts `dfi_rddata_en`
  for four cycles to request four DFI data words.

Cycle 10:
- `tphy_rdlat = 4` cycles after `dfi_rddata_en`, the PHY asserts
  `dfi_rddata_valid` and drives the first `dfi_rddata` word.

Cycles 10-13:
- The PHY returns four consecutive data words on `dfi_rddata`, with
  `dfi_rddata_valid` asserted each cycle.

## Walkthrough 2: activate -> write with preamble and mask

The controller wants to write `0xA5A5A5A5` to bank 1, row 2, column 7,
masking the lowest byte.

Cycle 0:
- Control interface: `dfi_cs_n = 0`, `dfi_ras_n = 0`, `dfi_cas_n = 1`,
  `dfi_we_n = 1`, `dfi_bank = 1`, `dfi_address = row 2`. ACT.

Cycle 4:
- After row-open timing, the MC issues a write.
- Control interface: `dfi_cs_n = 0`, `dfi_ras_n = 1`, `dfi_cas_n = 0`,
  `dfi_we_n = 0`, `dfi_bank = 1`, `dfi_address = column 7`.

Cycle 6:
- `tphy_wrlat = 2` cycles after the write command, the MC asserts
  `dfi_wrdata_en` for four cycles.

Cycle 7:
- `tphy_wrdata = 1` cycle after the enable, the MC drives the first
  `dfi_wrdata` word: `0xA5A5A5A5`.
- `dfi_wrdata_mask` is driven as `0x01` to mask the lowest byte. Bit 0
  masks the byte in `dfi_wrdata[7:0]`.

Cycles 7-10:
- The MC continues driving the same data word and mask for all four cycles
  of the burst.

Cycle 11:
- `dfi_wrdata_en` has de-asserted one cycle before the last data word.
- The write data completes on the DRAM bus after `twrdata_delay` cycles.

## Walkthrough 3: back-to-back reads on different rows

Bank 0 row 5 and bank 1 row 2 are both opened by earlier activates. The
controller issues two reads, one to each bank.

Cycle 0:
- Read from bank 0, column 3: `dfi_cs_n = 0`, `dfi_cas_n = 0`,
  `dfi_we_n = 1`, `dfi_bank = 0`, `dfi_address = column 3`.

Cycle 2:
- `dfi_rddata_en` asserts for four cycles (bank 0 read data expected).

Cycle 4:
- Second read from bank 1, column 7: `dfi_cs_n = 0`, `dfi_cas_n = 0`,
  `dfi_we_n = 1`, `dfi_bank = 1`, `dfi_address = column 7`.
- Because the two reads are contiguous, `dfi_rddata_en` stays asserted for
  four more cycles.

Cycle 6:
- `dfi_rddata_valid` asserts for the first read data (earliest allowed by
  `tphy_rdlat = 4` from cycle 2).

Cycle 10:
- `dfi_rddata_valid` asserts for the second read data (four cycles after
  the second `dfi_rddata_en` assertion at cycle 6).

The data stream on `dfi_rddata` is contiguous even though the two reads
went to different banks, because the controller kept `dfi_rddata_en`
asserted across both commands.

**Source:** DFI Specification v3.1 sections 4.4, 4.5
