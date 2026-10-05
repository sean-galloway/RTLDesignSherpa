# Organization

## Sub-interface map

DFI 2.1 partitions the MC/PHY boundary into seven sub-interfaces. Each group
has its own signals, direction, and timing parameters.

| Sub-interface | MC -> PHY | PHY -> MC | Purpose |
| --- | --- | --- | --- |
| Control | address, bank, RAS/CAS/WE, CKE, CS, ODT, reset | - | DRAM command reflection |
| Write data | write data, enable, mask | - | Write payload carriage |
| Read data | read enable | read data, valid, DNV | Read payload return |
| Update | ctrlupd_req | ctrlupd_ack, phyupd_req/type, phyupd_ack | Idle-window handshakes |
| Status | data_byte_disable, dram_clk_disable, freq_ratio, init_start, parity_in | init_complete, parity_error | Init and capability signaling |
| Training | rdlvl_*, wrlvl_* control | rdlvl_*, wrlvl_* response | Read/write leveling |
| Low power | lp_req, lp_wakeup | lp_ack | Power-down opportunity |
: DFI 2.1 sub-interface summary

The Control, Write data, and Read data sub-interfaces carry ordinary traffic.
Update, Status, Training, and Low power are housekeeping groups that let the PHY
pause traffic, report init completion, train delays, or enter low power states.

## Clocking

Every DFI signal is driven from a register on the rising edge of the DFI clock.
The specification does not fix where that clock comes from, only that both sides
agree on it. In a matched-frequency system the DFI clock and the PHY clock are
the same. In a frequency-ratio system the PHY runs at a multiple of the MC clock
and the DFI clock is the slower MC clock, while individual phases are sampled on
the faster PHY clock.

## Frequency ratio

DFI 2.1 supports three ratios: 1:1, 1:2, and 1:4. The optional `dfi_freq_ratio`
signal reports the ratio as `2'b00`, `2'b01`, or `2'b10`; `2'b11` is reserved.

When the ratio is not 1:1, the Control interface, Write data interface, and read
data enable are replicated into phase-specific copies with a `_pN` suffix. For
example, a 1:2 system can drive `dfi_address_p0` and `dfi_address_p1` in a
single MC clock, letting the PHY accept two commands per DFI clock. The MC may
place a command on any phase; the PHY must accept commands on all phases.

Read data, read data valid, and read data not valid are different. They are
replicated into DFI data word copies with a `_wN` suffix instead of `_pN`. A 1:2
ratio has `_w0` and `_w1`; a 1:4 ratio has `_w0` through `_w3`. The suffix for
phase 0 or word 0 is optional.

## Slices, bytes, and data ordering

DFI data signals are organized by byte lanes. `dfi_wrdata_mask[0]` masks
`dfi_wrdata[7:0]`, `dfi_wrdata_mask[1]` masks `dfi_wrdata[15:8]`, and so on. The
same ordering applies to `dfi_rddata_dnv` and `dfi_data_byte_disable`. The
`dfi_wrdata_en` and `dfi_rddata_en` widths are ideally one bit per memory data
slice, with bit 0 covering the lowest data segment.

## LPDDR2 command/address carve-out

LPDDR2 does not use `dfi_bank`, `dfi_ras_n`, `dfi_cas_n`, or `dfi_we_n`. Its
10-bit Command/Address (CA) bus is mapped onto `dfi_address` as a flat 20-bit
word: rising-edge CA bits on `dfi_address[9:0]` and falling-edge CA bits on
`dfi_address[19:10]`. The PHY splits that word into the two DDR CA cycles.

**Source:** DFI Specification v2.1.1 sections 2.0, 3.0, 3.1, 4.7
