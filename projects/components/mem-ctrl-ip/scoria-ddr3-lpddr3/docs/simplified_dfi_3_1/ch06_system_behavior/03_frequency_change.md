# Frequency Change

DFI 3.1 reuses the initialization handshake for frequency changes during
normal operation. The MC requests a change with `dfi_init_start`; the PHY
acknowledges by de-asserting `dfi_init_complete`.

## Acknowledged frequency change

1. The MC asserts `dfi_init_start` during normal operation.
2. The PHY de-asserts `dfi_init_complete` within `tinit_start` cycles to
   accept the request.
3. The MC holds `dfi_init_start` asserted while the clock frequency
   changes.
4. The MC de-asserts `dfi_init_start` when the new frequency is stable.
5. The PHY re-initializes for the new frequency and re-asserts
   `dfi_init_complete` within `tinit_complete` cycles.

Both sides reset their DFI read data word pointers to zero when
`dfi_init_start` asserts.

## Not-acknowledged frequency change

If the PHY does not de-assert `dfi_init_complete` within `tinit_start`
cycles, the request is ignored. The MC must then de-assert
`dfi_init_start` and may try again later.

## Stable levels during the change

While `dfi_init_start` is asserted or `dfi_init_complete` is de-asserted,
both the MC and the PHY must hold the DFI and memory interface signals at
valid and stable levels. The DFI specification does not define a maximum
overall duration for the frequency change.

## Scoria note

The scoria controller implements the frequency-change protocol because it
is part of the v3.1 initialization interface, but the DDR3/LPDDR3 target
use case does not rely on dynamic frequency scaling.

**Source:** DFI Specification v3.1 sections 3.5.4, 4.9
