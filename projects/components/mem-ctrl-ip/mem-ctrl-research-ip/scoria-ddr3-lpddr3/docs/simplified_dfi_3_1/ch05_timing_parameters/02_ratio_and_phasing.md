# Ratio and Phasing

DFI 3.1 supports three frequency relationships between the MC clock and the
PHY clock: 1:1, 1:2 and 1:4. The ratio affects command scheduling, signal
naming and read data ordering.

## Matched frequency (1:1)

In a 1:1 system the MC clock and the PHY clock are the same. There is one
command opportunity per DFI clock cycle and one read/write data word per
cycle. No `_pN` or `_wN` suffixes are needed, though phase 0 suffixes are
optional.

## 1:2 frequency ratio

The PHY clock runs at twice the MC clock frequency. In each MC clock cycle
the PHY can execute two commands or transfer two read data words. The MC
therefore provides:

- `dfi_address_p0`, `dfi_address_p1`
- `dfi_cs_n_p0`, `dfi_cs_n_p1`
- `dfi_wrdata_en_p0`, `dfi_wrdata_en_p1`
- `dfi_rddata_en_p0`, `dfi_rddata_en_p1`
- `dfi_rddata_w0`, `dfi_rddata_w1` on the return path
- `dfi_rddata_valid_w0`, `dfi_rddata_valid_w1`

The PHY must be able to accept a command on any phase.

## 1:4 frequency ratio

The PHY clock runs at four times the MC clock frequency. The same
replication pattern applies with `_p0` through `_p3` for commands and
`_w0` through `_w3` for read data. The 1:4 mode is explicitly defined in
DFI 3.1 even though the specification text often shows only `_p0/_p1`
examples.

## Read data rotation

In a frequency-ratio system, read data words return on `dfi_rddata_wN` in a
rolling order. The MC and PHY must keep their data word pointers
synchronized. A frequency change resets both pointers to zero.

## Scheduling impact

Frequency ratio gives the MC two useful abilities:

1. Multiple command slots per MC clock. A 1:4 system can issue up to four
   commands in one MC clock cycle.
2. Higher data bandwidth at the PHY without increasing MC clock frequency.

The cost is wider buses, more complex pointer management and the need to
drive enables in every phase for signals such as `dfi_cke` and `dfi_odt`.

## Practical note for scoria

The scoria controller inherits a datapath designed around a four-phase
unit of transfer (`DFI_RATE = 4`). The v2.1.1 specification enumerated the
phase variants explicitly; v3.1 generalizes the notation to `_pN`. A naive
signal-name diff would wrongly report the phase signals as removed. They
are still present; only the naming convention changed.

**Source:** DFI Specification v3.1 sections 3.5.3, 4.8
