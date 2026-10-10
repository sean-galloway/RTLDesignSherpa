# Write Carriage

A DFI write transaction has two separable delays: the time from the write
command to the write-data enable, and the time from the enable to the data
itself. The PHY defines both delays; the MC schedules around them.

## Write timing parameters in use

| Parameter | Meaning |
| --- | --- |
| `tphy_wrlat` | Cycles from write command to `dfi_wrdata_en` assertion. |
| `tphy_wrdata` | Cycles from `dfi_wrdata_en` assertion to `dfi_wrdata` driven. |
| `twrdata_delay` | Cycles from `dfi_wrdata_en` assertion to completion on the DRAM bus. |

: Write carriage timing parameters

Both `tphy_wrlat` and `tphy_wrdata` can be zero. They must be held
constant while commands are flowing; they may only be changed when the bus
is idle.

## Single write transaction

1. The MC issues a write command on the control interface.
2. `tphy_wrlat` cycles later, the MC asserts `dfi_wrdata_en`.
3. `tphy_wrdata` cycles after that, the MC drives the first `dfi_wrdata`
   word.
4. The MC holds `dfi_wrdata_en` for the length of the transfer. For a
   burst-length-8 write this is four DFI data words.
5. `dfi_wrdata_en` de-asserts `tphy_wrdata` cycles before the last valid
   data word.
6. The write completes on the DRAM bus `twrdata_delay` cycles after
   `dfi_wrdata_en` first asserted.

## Contiguous vs non-contiguous writes

For back-to-back writes with matching timing, `dfi_wrdata_en` can stay
asserted across command boundaries and the data stream is contiguous. If
the command spacing is larger or the timing parameters differ, the enable
and data de-assert between commands.

| Case | `dfi_wrdata_en` | Data stream |
| --- | --- | --- |
| Back-to-back, same parameters | Continuous | Contiguous |
| Interrupted first burst | Asserted for partial first burst plus full second burst | Contiguous for part of first plus all of second |
| Independent writes | De-asserts between commands | Non-contiguous |

: Write data stream patterns

## Write chip select timing

When `dfi_wrdata_cs_n` is used, the PHY defines `tphy_wrcslat` and
`tphy_wrcsgap`. The MC drives the chip select `tphy_wrcslat` cycles after
the write command and holds it for the data transfer length plus the gap
time. If the next write targets a different chip select, the MC must add
`tphy_wrcsgap` cycles between commands.

## DBI and CRC notes

When DBI is enabled and `phydbi_mode = 0`, `dfi_wrdata_mask` carries the
per-byte inversion bits instead of mask bits. When CRC is enabled and
`phycrc_mode = 0`, the MC sends the CRC data word on the `dfi_wrdata` bus
and extends `dfi_wrdata_en` accordingly. These are DDR4 features and are
not used by the scoria DDR3/LPDDR3 controller.

**Source:** DFI Specification v3.1 sections 3.2, 4.4, Table 6, Table 7
