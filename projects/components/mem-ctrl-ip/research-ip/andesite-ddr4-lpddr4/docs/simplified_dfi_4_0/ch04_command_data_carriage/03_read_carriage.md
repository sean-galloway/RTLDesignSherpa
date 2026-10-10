# Read Carriage

The read data interface returns read data from PHY to MC. The MC must tell the PHY when to
expect data by asserting `dfi_rddata_en`; the PHY returns data and per-slice valid signals after the
read latency.

## Read timing overview

For a matched-frequency system:

1. MC issues read command on control interface.
2. After `trddata_en` DFI clocks, MC asserts `dfi_rddata_en` for the expected burst duration.
3. Within `tphy_rdlat` DFI clocks from `dfi_rddata_en`, the PHY asserts `dfi_rddata_valid` and
   drives `dfi_rddata`.

In a 1:4 frequency-ratio system, `dfi_rddata_en` is phase-suffixed and the returned read data
appears as word-suffixed `_w0`..`_w3`.

## Read data valid

`dfi_rddata_valid` is one bit per PHY data slice. It is the one-to-one response to `dfi_rddata_en`
within `tphy_rdlat`. The MC uses it to qualify `dfi_rddata`. Stray valid signals without a matching
`dfi_rddata_en` are dropped.

## Read DBI

When DBI is enabled and `phydbi_mode = 0`, the PHY returns `dfi_rddata_dbi` alongside
`dfi_rddata`. A `1` indicates that the corresponding byte was inverted by the DRAM and must be
re-inverted by the receiver. When `phydbi_mode = 1` the PHY handles inversion internally and
`dfi_rddata_dbi` is not used.

## Read data chip select

`dfi_rddata_cs` identifies the rank for which read data is expected. During read training it identifies
the rank being trained. The PHY may need additional rank-switching gap (`tphy_rdcsgap`) when
the target rank changes between reads.

## Data not valid (LPDDR2)

`dfi_rddata_dnv` is an LPDDR2-specific per-byte signal that marks bytes which do not contain
valid data. It has the same timing as `dfi_rddata_valid`.

**Source:** DFI Specification v4.0 sections 3.3, 4.4, 4.6, 4.6.2
