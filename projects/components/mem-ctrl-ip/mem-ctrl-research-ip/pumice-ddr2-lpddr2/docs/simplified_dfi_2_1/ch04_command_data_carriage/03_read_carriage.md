# Read Carriage

A read transaction on the DFI has two parts: the read command on the control
interface, and the returned data on the read data interface. The MC tells the
PHY when to expect data; the PHY tells the MC when the data is actually valid.

## Command to enable relationship

The MC asserts `dfi_rddata_en` `trddata_en` cycles after the read command. The
enable must stay asserted for the duration of contiguous read data expected
from the PHY. A single continuous assertion can cover data from multiple read
commands.

## Enable to data relationship

The PHY returns data by asserting `dfi_rddata_valid` with the data. The first
valid beat may arrive any time up to `tphy_rdlat` cycles after
`dfi_rddata_en`, but the PHY is allowed to return it earlier. When
`dfi_rddata_valid` is high, the entire DFI read data word is valid.

For LPDDR2 the PHY also asserts `dfi_rddata_dnv` with the same timing. A high
bit in `dfi_rddata_dnv` means the corresponding byte in `dfi_rddata` should be
discarded.

## Contiguous reads

Back-to-back reads can be covered by a single `dfi_rddata_en` assertion. The MC
only de-asserts the enable when it no longer expects contiguous data. The PHY
uses `dfi_rddata_valid` to mark the actual cycles that carry valid data.

## Frequency ratio packing

In a 1:2 ratio system the read data is returned on `dfi_rddata_w0` and
`dfi_rddata_w1`, one word per half DFI clock. In a 1:4 system there are four
word copies `_w0` through `_w3`. The read data enable is still phase-specific:
`dfi_rddata_en_p0`, `dfi_rddata_en_p1`, and so on.

**Source:** DFI Specification v2.1.1 sections 3.3, 4.4
