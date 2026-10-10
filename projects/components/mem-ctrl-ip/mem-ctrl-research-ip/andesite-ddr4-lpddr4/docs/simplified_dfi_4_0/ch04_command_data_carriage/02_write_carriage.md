# Write Carriage

The write data interface carries write data, mask or write DBI, and enable signals from MC to PHY.
The PHY forwards them to the DRAM after the programmed write latency.

## Write timing overview

For a matched-frequency system, the sequence is:

1. MC issues write command on control interface.
2. After `tphy_wrlat` DFI clocks, MC asserts `dfi_wrdata_en`.
3. After `tphy_wrdata` DFI clocks from `dfi_wrdata_en`, first write data word appears on
   `dfi_wrdata`.
4. `dfi_wrdata_en` stays asserted for the duration of the burst. `dfi_wrdata_mask` (or write DBI
   when enabled) travels with the data.

In a 1:4 frequency-ratio system, the control command is issued on one phase and the
phase-suffixed write data (`dfi_wrdata_p0`..`p3`) carries four DRAM-clock words per DFI clock.

## Write data enable

`dfi_wrdata_en` is ideally one bit per PHY data slice. All bits are identical in normal operation, so
the MC-to-PHY width may differ. The enable must be asserted early enough to satisfy `tphy_wrlat`
and must remain asserted for the entire burst.

## Write mask and write DBI

`dfi_wrdata_mask` is one bit per byte of write data. When DBI is disabled, a `1` masks the
associated byte. When DBI is enabled and `phydbi_mode = 0`, the same bus carries the DBI
pattern: a `1` tells the DRAM to invert the corresponding byte before storing it. There is no separate
`dfi_wrdata_dbi` signal in DFI 4.0.

When `phydbi_mode = 1`, the PHY computes and inserts DBI internally; the MC presents plain
data and mask.

## Write CRC

Write CRC may be generated in the MC (`phycrc_mode = 0`) or in the PHY (`phycrc_mode = 1`).
When the MC generates CRC, the CRC word is appended to the write burst on `dfi_wrdata`. The
PHY reports CRC errors on `dfi_alert_n` with timing bounded by `tphy_crcmin_lat` and
`tphy_crcmax_lat`.

## Write data chip select

`dfi_wrdata_cs` identifies the target rank for the write data. During write leveling it identifies the
rank being trained. The PHY may need additional rank-switching gap (`tphy_wrcsgap`) when the
target rank changes between writes.

**Source:** DFI Specification v4.0 sections 3.2, 4.4, 4.5, 4.5.2, 4.5.3
