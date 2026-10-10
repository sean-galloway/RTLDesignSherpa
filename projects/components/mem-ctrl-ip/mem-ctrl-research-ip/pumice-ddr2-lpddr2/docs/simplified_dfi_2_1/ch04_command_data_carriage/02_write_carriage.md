# Write Carriage

A write transaction on the DFI has three parts: the write command on the
control interface, the write enable assertion, and the data/mask payload. The
PHY is responsible for turning that sequence into the correct DRAM timing.

## Command to enable relationship

The MC asserts `dfi_wrdata_en` `tphy_wrlat` cycles after the write command
appears on the control interface. The enable must stay asserted for every cycle
that contains write data. For contiguous back-to-back writes the enable can
remain high across the command boundary.

## Enable to data relationship

The actual data and mask appear `tphy_wrdata` cycles after `dfi_wrdata_en`
asserts. In older DFI versions `tphy_wrdata` was effectively fixed at 1; DFI 2.1
made it programmable so the PHY can ask for earlier notification.

`dfi_wrdata_mask` follows the same timing as `dfi_wrdata`. A mask bit of 1 means
"do not write this byte." Bit N covers `dfi_wrdata[8N+7:8N]`. If the data bus is
not a multiple of 8, the most significant mask bit covers the most significant
partial byte.

## Contiguous and interrupted writes

When two writes are separated by a bubble, the MC de-asserts `dfi_wrdata_en`
for at least one cycle. The PHY uses that gap to separate the two bursts. When
writes are back-to-back, the enable stays asserted and the data stream is
contiguous.

In a frequency-ratio system the write data is split across phases. The MC may
keep the data aligned to phase 0 by using `tphy_wrdelay`, or it may send the
data unaligned and let the PHY sort it out.

## Frequency ratio packing

In a 1:2 ratio system a single DFI clock contains two phases of write data. The
MC can therefore issue one write command per DFI clock and still supply both
halves of the burst on `dfi_wrdata_p0` and `dfi_wrdata_p1`. In a 1:4 ratio
system four phases fit in one DFI clock.

**Source:** DFI Specification v2.1.1 sections 3.2, 4.3
