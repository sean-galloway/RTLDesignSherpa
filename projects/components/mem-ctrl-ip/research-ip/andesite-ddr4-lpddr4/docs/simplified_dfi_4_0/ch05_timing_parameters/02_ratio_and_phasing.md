# Frequency Ratio and Phasing

DFI supports three frequency ratios between the DFI clock and the DRAM clock: 1:1, 1:2 and
1:4. The `dfi_freq_ratio` signal encodes the ratio at initialization and is expected to remain
constant.

## Ratio definitions

| `dfi_freq_ratio` | Ratio | Meaning |
| --- | --- | --- |
| 00 | 1:1 | DFI clock and DRAM clock are the same frequency. |
| 01 | 1:2 | One DFI clock per two DRAM clocks. |
| 10 | 1:4 | One DFI clock per four DRAM clocks. |
| 11 | Reserved | Not used. |

: DFI frequency ratios

At 1:4, one DFI clock covers four DRAM clocks. Control and write data signals are replicated into
four phase-suffixed buses (`_p0`..`_p3`). Read data is returned as four word-suffixed buses
(`_w0`..`_w3`).

## What ratio does to scheduling

In a 1:1 system, the MC issues one command per DFI clock. In a 1:2 system, it may issue two
commands per DFI clock (one per phase). In a 1:4 system, it may issue up to four commands per
DFI clock. The PHY must accept commands on any phase.

The andesite design point uses 1:4. This means a single ACT-RD or ACT-WR sequence can be
packed tightly: the ACT on phase p0 of one DFI clock and the RD/WR on phase p0 of a later DFI
clock once tRCD (measured in DRAM clocks) is satisfied.

## Phase replication rules

- Control interface: `_pN` suffix gives the value for phase N of the DFI PHY clock.
- Write data interface: `_pN` suffix gives the write data word for phase N.
- Read data interface: `_wN` suffix gives the read data word N.
- `dfi_alert_n`: `_aN` suffix gives the value for clock cycle N.
- Phase 0 / word 0 / cycle 0 suffixes are optional.

## Timing parameter units in ratio systems

For matched-frequency systems, a DFI PHY clock equals a DFI clock. For frequency-ratio
systems, timing parameters that mention "DFI PHY clocks" are measured in the higher-speed PHY
clock domain (one quarter of the DFI clock period at 1:4), while parameters measured in "DFI
clocks" are measured in the slower DFI clock domain.

This distinction matters for `tinit_start`, `tinit_complete`, `tparin_lat` and several others. The MC must
use the correct domain when scheduling.

## Ratio change

A frequency change can include a ratio change. The protocol uses `dfi_init_start` and
`dfi_init_complete`. The MC must drive `dfi_freq_ratio` and `dfi_frequency` to their new values
while `dfi_init_start` is asserted, and the PHY must be ready to operate at the new ratio after the
handshake completes.

**Source:** DFI Specification v4.0 sections 3.5.4, 4.9, 4.10
