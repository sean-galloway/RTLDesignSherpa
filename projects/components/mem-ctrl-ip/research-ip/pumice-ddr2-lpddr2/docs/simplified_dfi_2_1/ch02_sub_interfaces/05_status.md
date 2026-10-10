# Status Interface

The status interface handles initialization, clock control, frequency ratio,
and optional DIMM parity reporting. Several of its signals are optional and only
matter if the system implements the related feature.

## Status signals

| Signal | Direction | Width | Default | What it does |
| --- | --- | --- | --- | --- |
| dfi_data_byte_disable | MC -> PHY | DFI data width / 8 | no default | Optional per-byte disable; valid only at initialization. |
| dfi_dram_clk_disable | MC -> PHY | DFI chip select width | 0x0 | When high, PHY stops clocking the DRAMs. |
| dfi_freq_ratio | MC -> PHY | 2 bits | no default | Optional static ratio: 00=1:1, 01=1:2, 10=1:4, 11=reserved. |
| dfi_init_complete | PHY -> MC | 1 bit | 0x0 | PHY is ready to respond to DFI traffic; also frequency-change ack. |
| dfi_init_start | MC -> PHY | 1 bit | 0x0 or 0x1 | MC indicates status signals are valid; also used to request frequency change. |
| dfi_parity_in | MC -> PHY | 1 bit | 0x0 or 0x1 | Even/odd parity for control interface; replicated as `dfi_parity_in_pN`. |
| dfi_parity_error | PHY -> MC | 1 bit | 0x0 | DIMM parity error report; correlated to ERR_OUT#. |
: DFI 2.1 status interface signals

## Initialization use

At power-up most command and status signals must be held at their default
values until `dfi_init_complete` asserts. The exceptions are signals that have
no meaningful default, such as `dfi_address` for most systems, or
`dfi_data_byte_disable` and `dfi_freq_ratio`, which the MC defines before or
during initialization.

`dfi_init_start` tells the PHY that `dfi_data_byte_disable` and/or
`dfi_freq_ratio` are valid. A PHY that depends on these settings may wait for
`dfi_init_start` before asserting `dfi_init_complete`. A PHY that does not may
assert `dfi_init_complete` earlier. In either case initialization is not
complete until both `dfi_init_start` and `dfi_init_complete` have been asserted
simultaneously for at least one DFI clock cycle.

## Frequency change use

During normal operation, if both sides support the optional frequency change
protocol, the MC may re-assert `dfi_init_start` to request a frequency change.
The PHY accepts by de-asserting `dfi_init_complete` within `tinit_start` cycles.
The MC holds `dfi_init_start` until the change completes; the PHY re-asserts
`dfi_init_complete` within `tinit_complete` cycles after `dfi_init_start` drops.

## Clock disable

`dfi_dram_clk_disable` lets the MC stop the clocks to the DRAM devices. The PHY
must hold the DRAM clock at a constant value within `tdram_clk_disable` cycles
after the signal asserts, and must resume valid clock edges within
`tdram_clk_enable` cycles after it de-asserts.

## Parity

`dfi_parity_in` carries even or odd parity over `dfi_address`, `dfi_bank`,
`dfi_cas_n`, `dfi_ras_n`, and `dfi_we_n`. In frequency-ratio systems it is
replicated as `dfi_parity_in_pN`. `dfi_parity_error` is returned by the PHY
within `tphy_paritylat` cycles when a DIMM detects a parity error.

**Source:** DFI Specification v2.1.1 sections 3.5, 4.1, 4.6, 4.8, 4.9
