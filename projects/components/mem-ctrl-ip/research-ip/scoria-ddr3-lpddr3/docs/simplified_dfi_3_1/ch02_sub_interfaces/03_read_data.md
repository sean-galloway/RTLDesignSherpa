# Read Data Interface

The read data interface returns captured DRAM data from the PHY to the MC.
The MC tells the PHY how many words to expect; the PHY returns data when
it is ready and marks each word valid.

## Read data signals

| Signal | From | Width | Default | What it does |
| --- | --- | --- | --- | --- |
| `dfi_rddata_en` | MC | DFI Data Enable Width | 0x0 | Tells the PHY a read is underway and how many contiguous words are expected. Asserted `trddata_en` cycles after the read command. |
| `dfi_rddata` | PHY | DFI Data Width | none | Read data bus. Expected within `tphy_rdlat` cycles after `dfi_rddata_en` assertion. |
| `dfi_rddata_valid` | PHY | DFI Read Data Valid Width | 0x0 | One bit per PHY data slice, asserted with the corresponding data. |
| `dfi_rddata_dnv` | PHY | DFI Data Width / 8 | 0x0 | Data-not-valid indicator, per byte. Used by LPDDR2. |
| `dfi_rddata_dbi_n` | PHY | DFI DBI Width | none | Read DBI inversion bits. Used when `phydbi_mode = 0` and DBI is enabled. |
| `dfi_rddata_cs_n` | MC | CS Width x Data Enable Width | none | Optional read data chip select. During read training it indicates the rank being trained; in normal operation it identifies the target rank. |

: Read data interface signals

In a frequency-ratio system, `dfi_rddata_en` becomes `dfi_rddata_en_pN`
while the return data and qualifiers become `dfi_rddata_wN`,
`dfi_rddata_valid_wN`, `dfi_rddata_dnv_wN` and `dfi_rddata_dbi_n_wN`. The
`_wN` suffix identifies the DFI data word number.

## `dfi_rddata_en` and `dfi_rddata_valid`

`dfi_rddata_en` is the MC's prediction of how much read data is coming. It
is asserted `trddata_en` cycles after the read command and held for the
number of contiguous data words expected. The PHY responds with
`dfi_rddata_valid`; there is a one-to-one correspondence between assertion
cycles of `dfi_rddata_en` and `dfi_rddata_valid`.

`tphy_rdlat` is a maximum: the PHY may return data earlier than the
programmed value. Each bit of `dfi_rddata_valid` corresponds to one PHY
data slice, so different slices may return data on different cycles.

## Read chip select

Like its write counterpart, `dfi_rddata_cs_n` is optional. When used, the
PHY may require `tphy_rdcsgap` extra cycles between read commands that
switch target chip selects. The signal is asserted `tphy_rdcslat` cycles
after the read command.

## LPDDR2 data-not-valid

LPDDR2 defines data words that are not all valid. In that case the PHY
asserts `dfi_rddata_valid` for the returning word and simultaneously uses
`dfi_rddata_dnv` to mark the invalid bytes. This is the only DRAM class in
the v3.1 inventory that uses `dfi_rddata_dnv`.

## Read data timing parameters

| Parameter | Defined by | Meaning |
| --- | --- | --- |
| `trddata_en` | System | Cycles from read command to `dfi_rddata_en` assertion. |
| `tphy_rdlat` | PHY | Maximum cycles from `dfi_rddata_en` assertion to `dfi_rddata_valid` assertion. |
| `tphy_rdcslat` | PHY | Cycles from read command to `dfi_rddata_cs_n` assertion. |
| `tphy_rdcsgap` | PHY | Additional cycles required between commands when changing target chip select. |

: Read data interface timing parameters

`trddata_en` and `tphy_rdlat` are normally held constant while commands are
flowing; they may only be changed when the bus is idle.

**Source:** DFI Specification v3.1 sections 3.3, 4.5, Table 9, Table 10, Table 11
