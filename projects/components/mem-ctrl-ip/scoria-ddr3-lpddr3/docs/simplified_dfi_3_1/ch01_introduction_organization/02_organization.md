# Organization

## Sub-interface map for DFI 3.1

DFI 3.1 organizes its signals into eight sub-interfaces. Each interface has
a direction (MC to PHY or PHY to MC), a set of signals and a family of
timing parameters.

| Sub-interface | Direction | Purpose |
| --- | --- | --- |
| Control | MC -> PHY | Command, address, bank, chip select, CKE, ODT, reset |
| Write data | MC -> PHY | Write data, byte mask/DBI, write enable, write chip select |
| Read data | PHY -> MC | Read data, read valid, read chip select, DNV (LPDDR2) |
| Update | Both | MC-initiated and PHY-initiated update handshakes |
| Status | Both | Init, frequency ratio, clock disable, parity, alert |
| Training | Both | Gate training, read data eye training, write leveling, CA training |
| Low power control | MC -> PHY (ack PHY -> MC) | Low-power opportunity requests |
| Error | PHY -> MC | Error indication and error information |

: DFI 3.1 sub-interfaces

## Clocking

The DFI clock is the MC clock. All DFI signals are referenced to the rising
edge of this clock. The DFI PHY clock is the same frequency as the DRAM
clock, which is one half of the data rate. In a matched-frequency system the
MC clock and the PHY clock are the same; in a frequency-ratio system the PHY
clock runs at a multiple of the MC clock.

DFI allows ratios of 1:1, 1:2 and 1:4. The ratio is conveyed on
`dfi_freq_ratio` (2 bits): `00` for 1:1, `01` for 1:2, `10` for 1:4, `11`
reserved.

## Frequency ratio and the `_pN` / `_wN` replication rule

When the PHY clock is faster than the MC clock, the MC must supply multiple
phases of command and data information per MC clock cycle. DFI 3.1 handles
this with replicated signals:

- Commands and other MC-to-PHY signals that are sampled per PHY clock phase
  carry a `_pN` suffix. For example, `dfi_address_p0`, `dfi_address_p1`,
  `dfi_cs_n_p0`, `dfi_cs_n_p1`. The suffix for phase 0 is optional.
- Read data and read-data qualifiers from PHY to MC are delivered as DFI data
  words with a `_wN` suffix. For example, `dfi_rddata_w0`,
  `dfi_rddata_w1`, `dfi_rddata_valid_w0`, `dfi_rddata_valid_w1`.
- Variable-pulse-width status signals such as `dfi_alert_n` carry an `_aN`
  suffix to preserve pulse width across the clock-domain boundary.

The MC may issue commands on any phase. The PHY must be able to accept a
command on any and all phases. For signals driven in all phases, such as
`dfi_cke` and `dfi_odt`, the MC must drive every phase.

## PHY data slices and byte lanes

DFI data width is generally twice the DRAM data width, because one DFI data
word carries both edges of a DRAM data transfer. The PHY is often organized
as data slices, each handling a byte or a small group of bytes.

`dfi_wrdata_en` and `dfi_rddata_en` are ideally one bit per PHY data slice,
though the spec allows the width to differ between MC and PHY as long as the
lowest bit maps to the lowest data segment. `dfi_rddata_valid` is one bit per
PHY data slice so that each slice can return data independently.

`dfi_data_byte_disable` tells the PHY which byte lanes are unused. The bit
order matches `dfi_wrdata` and `dfi_rddata`. This signal is defined at
initialization and expected to remain constant.

## Simplified teaching model

All timing examples and walkthroughs in this book use a deliberately small
configuration so that phase and burst counts are obvious:

- One rank, one chip select.
- 1:2 frequency ratio: two PHY phases (`p0`, `p1`) per MC clock.
- DFI data width of 32 bits (two 16-bit PHY data words per MC clock), split
  into two slices.
- Burst length 8 on the DRAM, so a read or write transfers four DFI data
  words.
- `tphy_wrlat = 2`, `tphy_wrdata = 1`, `trddata_en = 2`, `tphy_rdlat = 4`
  unless stated otherwise.

Real systems are wider and may use 1:4 ratios; the scheduling rules are the
same.

**Source:** DFI Specification v3.1 sections 2.0, 3.5.3, 4.8, 5.0
