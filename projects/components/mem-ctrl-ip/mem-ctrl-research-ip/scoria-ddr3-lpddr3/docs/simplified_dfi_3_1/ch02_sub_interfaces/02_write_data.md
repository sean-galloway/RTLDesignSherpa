# Write Data Interface

The write data interface carries write data from the MC to the PHY and
tells the PHY when that data is valid. The PHY then retimes the data onto
the DRAM DQ/DQS pins.

## Write data signals

| Signal | From | Width | Default | What it does |
| --- | --- | --- | --- | --- |
| `dfi_wrdata` | MC | DFI Data Width | none | Write data bus. Data is driven `tphy_wrdata` cycles after `dfi_wrdata_en` asserts. |
| `dfi_wrdata_en` | MC | DFI Data Enable Width | 0x0 | Write data and mask enable. Asserted `tphy_wrlat` cycles after a write command; held for the duration of the data transfer. |
| `dfi_wrdata_mask` | MC | DFI Data Width / 8 | none | Per-byte mask, or write DBI when DBI is enabled. Same timing as `dfi_wrdata`. |
| `dfi_wrdata_cs_n` | MC | CS Width x Data Enable Width | none | Optional write data chip select. Indicates the target rank for the data, and during write leveling indicates the rank being trained. |

: Write data interface signals

In a frequency-ratio system these signals are replicated as `dfi_wrdata_pN`,
`dfi_wrdata_en_pN`, `dfi_wrdata_mask_pN` and `dfi_wrdata_cs_n_pN`. The
`_pN` suffix gives the value for each PHY clock phase.

## `dfi_wrdata_en` behavior

`dfi_wrdata_en` is the central enable for write data. One continuous
assertion may cover data for multiple back-to-back write commands. The
signal is asserted `tphy_wrlat` cycles after the write command on the
control interface, and the actual data appears `tphy_wrdata` cycles after
the enable. The enable de-asserts `tphy_wrdata` cycles before the last
valid data word.

For a non-contiguous write, `dfi_wrdata_en` de-asserts between commands.
For contiguous writes it stays asserted across command boundaries.

## Write data mask and DBI

When DBI is disabled, `dfi_wrdata_mask[N]` masks the byte
`dfi_wrdata[N*8+7:N*8]`. When DBI is enabled and `phydbi_mode = 0`, the
same bus carries the write DBI inversion bits: `1` means the corresponding
byte is inverted before being driven to DRAM. Mask and DBI are mutually
exclusive.

## Write chip select

`dfi_wrdata_cs_n` is optional in normal operation. When it is used, the PHY
may need extra spacing (`tphy_wrcsgap`) between commands that target
different chip selects so it can re-time its data path. The signal is driven
`tphy_wrcslat` cycles after the write command and held for at least the
data transfer length plus the gap time.

## Write data timing parameters

| Parameter | Defined by | Meaning |
| --- | --- | --- |
| `tphy_wrlat` | PHY | Cycles from write command to `dfi_wrdata_en` assertion. |
| `tphy_wrdata` | PHY | Cycles from `dfi_wrdata_en` assertion to `dfi_wrdata` driven. |
| `twrdata_delay` | System | Cycles from `dfi_wrdata_en` assertion to completion of the write data transfer on the DRAM bus. |
| `tphy_wrcslat` | PHY | Cycles from write command to `dfi_wrdata_cs_n` assertion. |
| `tphy_wrcsgap` | PHY | Additional cycles required between commands when changing target chip select. |
| `tphy_crcmin_lat`, `tphy_crcmax_lat` | System | Min/max cycles from CRC data on `dfi_wrdata_en` to CRC error on `dfi_alert_n`. |

: Write data interface timing parameters

## Write data programmable parameters

| Parameter | Defined by | Meaning |
| --- | --- | --- |
| `phycrc_mode` | PHY | `0` = MC generates CRC; `1` = PHY generates CRC. |
| `phydbi_mode` | PHY | `0` = MC generates DBI and inverts data; `1` = PHY does. |

: Write data programmable parameters

CRC and DBI are DDR4-era features and are not used by the scoria
DDR3/LPDDR3 controller, but the signals and parameters are part of DFI 3.1
and are noted here for completeness.

**Source:** DFI Specification v3.1 sections 3.2, 4.4, Table 6, Table 7, Table 8
