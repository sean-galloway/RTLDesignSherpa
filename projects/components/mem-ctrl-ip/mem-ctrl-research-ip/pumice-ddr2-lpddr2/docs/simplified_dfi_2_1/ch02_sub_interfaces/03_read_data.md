# Read Data Interface

The read data interface returns read payloads from the PHY to the MC. It
consists of the read enable from the MC (`dfi_rddata_en`) and the returned data,
valid flag, and data-not-valid flag from the PHY.

## Read data signals

| Signal | Direction | Width | Default | What it does |
| --- | --- | --- | --- | --- |
| dfi_rddata_en | MC -> PHY | DFI data enable width | 0x0 | Tells the PHY to expect read data; asserted `trddata_en` cycles after the read command. |
| dfi_rddata | PHY -> MC | DFI data width | no default | Returned read data. |
| dfi_rddata_valid | PHY -> MC | DFI read data valid width | 0x0 | Asserted with valid read data for each cycle of the burst. |
| dfi_rddata_dnv | PHY -> MC | DFI data width / 8 | 0x0 | Per-byte data-not-valid flag; required for LPDDR2. |
: DFI 2.1 read data interface signals

In a frequency-ratio system `dfi_rddata_en` becomes `dfi_rddata_en_pN`, while
`dfi_rddata`, `dfi_rddata_valid`, and `dfi_rddata_dnv` become
`dfi_rddata_wN`, `dfi_rddata_valid_wN`, and `dfi_rddata_dnv_wN`. A 1:2 ratio
has two word copies; a 1:4 ratio has four. The word 0 suffix is optional.

## Timing model

| Parameter | Meaning |
| --- | --- |
| trddata_en | Cycles from read command on control interface to `dfi_rddata_en` assertion. |
| tphy_rdlat | Maximum cycles from `dfi_rddata_en` assertion to first `dfi_rddata_valid` assertion. |
: Read data timing parameters

The MC asserts `dfi_rddata_en` `trddata_en` cycles after the read command and
holds it for the duration of contiguous read data it expects. The PHY may
return data any time up to `tphy_rdlat` cycles after the enable; it is allowed
to return data earlier by asserting `dfi_rddata_valid` sooner. When valid is
asserted the entire DFI read data word must be valid.

`dfi_rddata_dnv` is used only for LPDDR2 and has the same timing as
`dfi_rddata_valid`. Bit N correlates to the byte group
`dfi_rddata[8N+7:8N]`. It is the PHY's way of marking bytes that should be
discarded.

**Source:** DFI Specification v2.1.1 sections 3.3, 4.4
