# Write Data Interface

The write data interface moves write payloads from the MC to the PHY. It
consists of the data bus `dfi_wrdata`, the byte mask `dfi_wrdata_mask`, and the
enable `dfi_wrdata_en`. The interface is unidirectional from MC to PHY.

## Write data signals

| Signal | Direction | Width | Default | What it does |
| --- | --- | --- | --- | --- |
| dfi_wrdata | MC -> PHY | DFI data width | no default | Write data payload. Valid while `dfi_wrdata_en` is asserted. |
| dfi_wrdata_en | MC -> PHY | DFI data enable width | 0x0 | Enable for write data and mask; asserted `tphy_wrlat` cycles after the write command and `tphy_wrdata` cycles before data. |
| dfi_wrdata_mask | MC -> PHY | DFI data width / 8 | no default | Per-byte mask; bit N masks `dfi_wrdata[8N+7:8N]`. |
: DFI 2.1 write data interface signals

In a frequency-ratio system these signals become `dfi_wrdata_pN`,
`dfi_wrdata_en_pN`, and `dfi_wrdata_mask_pN`. Phase 0 may drop the suffix. The
write data stream is still expected to begin with phase 0 unless the MC chooses
to send it unaligned and uses `tphy_wrdelay`.

## Timing model

Three parameters govern write data timing:

| Parameter | Meaning |
| --- | --- |
| tphy_wrlat | Cycles from write command on control interface to `dfi_wrdata_en` assertion. |
| tphy_wrdata | Cycles from `dfi_wrdata_en` assertion to first `dfi_wrdata`/`dfi_wrdata_mask` beat. |
| tphy_wrdelay | Optional PHY-side delay between enable and data in frequency-ratio systems. |
: Write data timing parameters

`dfi_wrdata_en` is asserted `tphy_wrlat` cycles after the write command. It must
remain asserted for the entire contiguous write data burst. The actual data and
mask appear `tphy_wrdata` cycles after `dfi_wrdata_en` asserts. For back-to-back
writes the enable can stay asserted across command boundaries.

The DFI 1.0/2.0 model effectively fixed `tphy_wrdata` to 1. DFI 2.1 made it a
programmable parameter so PHYs that need earlier notification of pending data
can request a larger value.

**Source:** DFI Specification v2.1.1 sections 3.2, 4.3
