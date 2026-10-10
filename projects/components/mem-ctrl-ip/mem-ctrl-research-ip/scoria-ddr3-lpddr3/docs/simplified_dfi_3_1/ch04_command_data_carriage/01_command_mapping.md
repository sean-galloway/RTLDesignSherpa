# Command Mapping

On the DFI control interface, DRAM commands are encoded by the command
signals `dfi_act_n`, `dfi_ras_n`, `dfi_cas_n` and `dfi_we_n`, together with
the address, bank and chip-select buses. The PHY forwards these values to
the DRAM pins with the timing controlled by `tcmd_lat` and `tctrl_delay`.

## DDR3 command encoding on DFI

For DDR3 the command mapping is the familiar JEDEC encoding:

| Command | `dfi_act_n` | `dfi_ras_n` | `dfi_cas_n` | `dfi_we_n` |
| --- | --- | --- | --- | --- |
| Activate (ACT) | 1 | 0 | 1 | 1 |
| Read (RD) | 1 | 1 | 0 | 1 |
| Write (WR) | 1 | 1 | 0 | 0 |
| Precharge (PRE) | 1 | 0 | 1 | 0 |
| Refresh (REF) | 1 | 0 | 0 | 1 |
| Mode Register Set (MRS) | 1 | 0 | 0 | 0 |
| NOP | 1 | 1 | 1 | 1 |
| Deselect | 1 | 1 | 1 | 0 |

: DDR3 command encoding on DFI control signals

`dfi_act_n` is held high for DDR3; it is only meaningful for DDR4, where an
active-low `dfi_act_n` repurposes `dfi_ras_n`, `dfi_cas_n` and `dfi_we_n`
as upper row address bits A16, A15 and A14.

## LPDDR3/LPDDR2 CA-bus mapping

For LPDDR3 and LPDDR2 the DRAM has no separate RAS/CAS/WE pins. Instead
the command, address and bank information travel on a double-data-rate CA
bus. DFI maps this CA bus onto the `dfi_address` bus:

| `dfi_address` bit | CA rising edge bit | CA falling edge bit |
| --- | --- | --- |
| 9:0 | CA9:CA0 | - |
| 19:10 | - | CA9:CA0 |

: LPDDR3/LPDDR2 CA mapping onto `dfi_address`

The PHY transmits `dfi_address[9:0]` on the rising CA edge and
`dfi_address[19:10]` on the falling CA edge. During LPDDR3/LPDDR2
operation the command signals `dfi_ras_n`, `dfi_cas_n`, `dfi_we_n`,
`dfi_act_n`, `dfi_bank`, `dfi_bg` and `dfi_cid` must be held constant.

## Chip select and enable usage

`dfi_cs_n` is low active and selects the target rank. `dfi_cke` enables
the DRAM clock. `dfi_odt` controls on-die termination and is relevant for
DDR3, DDR2 and LPDDR3. All three are driven in every phase in a frequency-
ratio system.

`dfi_reset_n` is used by DDR4 and DDR3. The scoria controller drives it
from its init sequencer and presents it as `dfi_reset_n_o` at the DFI
boundary.

## Command timing relationship

The MC drives `dfi_cs_n` and the command/address signals according to
`tcmd_lat`. If `tcmd_lat` is non-zero, the CA signals are driven that many
DFI PHY clock cycles after `dfi_cs_n` assertion. The PHY then applies its
own `tctrl_delay` before driving the DRAM pins.

**Source:** DFI Specification v3.1 sections 3.1, 4.2, Table 4
