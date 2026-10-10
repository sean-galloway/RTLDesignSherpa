# Introduction

## What DFI is

The DDR PHY Interface (DFI) is a digital boundary between a DDR memory
controller (MC) and the physical layer (PHY) that drives the actual DRAM
pins. The MC thinks in commands, addresses, banks and bursts; the PHY turns
those abstract transactions into edge-aligned clocks, strobes and data on
the DRAM bus. DFI exists so that controller architects and PHY architects
can work against a common contract instead of custom-wiring every MC/PHY
pair.

At its simplest, DFI carries:

- Control: command/address signals such as `dfi_cs_n`, `dfi_ras_n`,
  `dfi_cas_n`, `dfi_we_n`, `dfi_address`, `dfi_bank`, plus DRAM-specific
  enables like `dfi_cke` and `dfi_odt`.
- Write data: `dfi_wrdata`, `dfi_wrdata_en`, `dfi_wrdata_mask`.
- Read data: `dfi_rddata`, `dfi_rddata_valid`, plus `dfi_rddata_en` from the
  MC to tell the PHY how many words to expect.
- Status, update, training, low-power and error sidebands that let the PHY
  and MC coordinate initialization, calibration, power states and error
  reporting.

DFI 3.1 supports DDR4, DDR3, DDR2, DDR1, LPDDR3, LPDDR2 and LPDDR1
DRAMs. Not every signal is required for every DRAM class; the controller
for a given memory type drives only the subset it needs.

## Why the seam exists

The MC and PHY run at different abstraction levels and often at different
clock frequencies:

- The MC schedules commands and tracks bank state in its own clock domain.
- The PHY retimes commands to the DRAM clock, generates DQS, samples read
  data, and absorbs the analog timing complexity of the memory channel.

DFI decouples these two domains. The MC can issue a write command and trust
that, `tphy_wrlat` cycles later, the PHY is ready for the data. The PHY can
assert `dfi_rddata_valid` when it has captured read data, and the MC samples
it in its own domain. Timing parameters such as `tctrl_delay`,
`tphy_wrlat`, `tphy_wrdata`, `trddata_en` and `tphy_rdlat` are the contract
that lets both sides agree on when information is valid without sharing a
single clock.

## Key features of DFI 3.1

- Frequency ratios of 1:1, 1:2 and 1:4 between the MC clock (DFI clock) and
  the PHY clock (DFI PHY clock). Commands are replicated per phase with a
  `_pN` suffix; read data words use `_wN`.
- A formal initialization and frequency-change protocol over
  `dfi_init_start` and `dfi_init_complete`.
- Separate low-power request signals for the control and data paths
  (`dfi_lp_ctrl_req` and `dfi_lp_data_req`), new in 3.1.
- PHY-requested training in non-DFI training mode (`dfi_phylvl_req_cs_n`,
  `dfi_phylvl_ack_cs_n`), new in 3.1.
- LPDDR3 CA training (`dfi_calvl_*`), new in 3.1.
- Error reporting (`dfi_error`, `dfi_error_info`) and parity/CRC/alert
  signals, inherited from 3.0 and mostly relevant to DDR4 systems.

## Edition lineage

This book focuses on the subset of DFI 3.1 that a DDR3/LPDDR3 controller
uses. The scoria controller inherited much of its datapath and command
scheduling from a v2.1.1 baseline, then adopted v3.1 for its leveling and
initialization model. Chapter 7 records exactly what changed and what
scoria deliberately does not implement.

**Source:** DFI Specification v3.1 sections 1.0, 2.0
