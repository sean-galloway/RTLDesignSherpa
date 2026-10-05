# Introduction

## What DFI is

The DDR PHY Interface (DFI) is the wire-level contract between a DDR memory
controller (MC) and a DDR physical interface (PHY). Version 2.1.1, published by
Denali Software in June 2010, defines the signals, signal relationships, and
timing parameters needed to move commands, write data, and read data across
that boundary for DDR1, LPDDR1, DDR2, LPDDR2, and DDR3 memory devices.

The DFI deliberately does not specify everything inside the MC or the PHY. It
only standardizes the seam: what control information the MC hands off, how the
PHY reports data back, how the two sides agree that initialization is done, and
how optional features such as frequency ratio, low power, and training are
signaled. Anything else, test logic, extra calibration, PHY-specific gearing, is
left to the implementation.

## Why the MC/PHY split exists

A modern memory subsystem usually has three layers: the controller (scheduling,
bank state, refresh), the PHY (clock generation, pads, delay lines, serializers),
and the DRAM devices. The controller wants a stable programming model; the PHY
wants freedom to choose pad timing, delay lines, and clocking. DFI sits between
them so that a controller team and a PHY team can work against a shared
interface instead of sharing every implementation detail.

The DFI clock can come from either side or from the system. The only hard rule
is that every DFI signal must be driven from a register clocked by a rising edge
of the DFI clock. How the other side receives it, synchronously or
asynchronously, is an implementation choice.

## Edition lineage

| Version | Year | What changed |
| --- | --- | --- |
| DFI 1.0 | 2007 | Initial release; DDR1/LPDDR1/DDR2 focus |
| DFI 2.0 | 2007-2008 | DDR3 support, read leveling, write leveling |
| DFI 2.1 | 2008-2010 | LPDDR2 support, low power, frequency ratio, parity, frequency change, update interface, tphy_wrdata |
: DFI edition lineage

DFI 2.1 is backward compatible with 2.0 at the signaling level, but a 2.1 MC or
PHY may offer optional features that a 2.0 partner does not understand. This
book focuses on the 2.1 surface and calls out the optional additions explicitly.

## Memory types covered

DFI 2.1 lists support for DDR1, LPDDR1, DDR2, LPDDR2, and DDR3. Not every
signal applies to every type. For example, `dfi_reset_n` is only for DDR3,
`dfi_odt` is for DDR2 and DDR3, and the LPDDR2 CA bus rides on `dfi_address`
while `dfi_bank`, `dfi_ras_n`, `dfi_cas_n`, and `dfi_we_n` are held idle.

## Optional features

Several 2.1 mechanisms are optional and not required for basic DFI compliance:

- Frequency ratio (1:2 or 1:4 MC:PHY clock ratio)
- Low power control handshaking
- Command parity and `dfi_parity_error`
- Frequency change protocol
- PHY-initiated update (`dfi_phyupd_*`)
- Read and write leveling training

A minimal DDR2 controller can ignore most of these and still be DFI compliant.
The pumice DDR2/LPDDR2 controller takes exactly that minimal stance: it drives
the command, write-data, read-data, and init-status sub-interfaces and leaves
update, training, low power, and frequency change unimplemented in its first
revision.

**Source:** DFI Specification v2.1.1 sections 1.0, 2.0
