# Status Interface

The status interface conveys configuration and status information between
the MC and the PHY. It covers initialization, frequency ratio, DRAM clock
disable, command parity and the alert signal.

## Initialization and configuration signals

| Signal | From | Width | Default | What it does |
| --- | --- | --- | --- | --- |
| `dfi_init_start` | MC | 1 bit | 0x0 or 0x1 | At init, indicates `dfi_data_byte_disable` and `dfi_freq_ratio` are valid. During normal operation, requests a frequency change. |
| `dfi_init_complete` | PHY | 1 bit | 0x0 | PHY is ready for normal DFI transactions. All command/status signals must be at default until this asserts. |
| `dfi_data_byte_disable` | MC | DFI Data Width / 8 | none | Marks unused byte lanes so the PHY may power them down. Defined at initialization only. |
| `dfi_freq_ratio` | MC | 2 bits | none | `00`=1:1, `01`=1:2, `10`=1:4, `11`=reserved. Required only for devices supporting multiple ratios. |
| `dfi_dram_clk_disable` | MC | DFI Chip Select Width | 0x0 | When asserted the PHY holds DRAM clocks at a constant value. |

: Status interface initialization and configuration signals

Initialization completes when both `dfi_init_start` and `dfi_init_complete`
are asserted simultaneously for at least one DFI clock cycle. The PHY may
assert `dfi_init_complete` before `dfi_init_start` if it does not need the
configuration signals.

## Parity and alert signals

| Signal | From | Width | Default | What it does |
| --- | --- | --- | --- | --- |
| `dfi_parity_in` | MC | 1 bit | 0x0 or 0x1 | Command parity bit, one per command. `0`=even, `1`=odd over the covered CA signals. Phase-indexed in frequency-ratio systems. |
| `dfi_alert_n_aN` | PHY | DFI Alert Width | 1 | Active-low CRC or command-parity error indicator propagated from DRAM ALERT_N. Pulse width preserved with `_aN` suffix. |

: Status interface parity and alert signals

`dfi_parity_in` covers `dfi_address`, `dfi_bank`, `dfi_bg`, `dfi_act_n`,
`dfi_cas_n`, `dfi_ras_n` and `dfi_we_n`. It is valid for one cycle per
command and is delayed by `tparin_lat` relative to the command. The PHY
delays it by the same `tctrl_delay` as the command bus. `dfi_alert_n`
asserts within `tphy_paritylat` cycles of the associated parity bit.

These signals are DDR4/DDR3 CA-parity and CRC features and are not used by
the scoria DDR3/LPDDR3 controller.

## Status timing parameters

| Parameter | Defined by | Meaning |
| --- | --- | --- |
| `tinit_start` | MC | Max cycles from `dfi_init_start` assertion to PHY de-asserting `dfi_init_complete` for a frequency change. |
| `tinit_complete` | PHY | Max cycles from `dfi_init_start` de-assertion to `dfi_init_complete` re-assertion after re-initialization. |
| `tdram_clk_disable` | PHY | Cycles from `dfi_dram_clk_disable` assertion to DRAM clock held constant. |
| `tdram_clk_enable` | PHY | Cycles from `dfi_dram_clk_disable` de-assertion to first valid DRAM clock edge. |
| `tparin_lat` | MC | Cycles from command to associated `dfi_parity_in`. |
| `tphy_paritylat` | PHY | Max cycles from `dfi_parity_in` to `dfi_alert_n` assertion. |

: Status interface timing parameters

**Source:** DFI Specification v3.1 sections 3.5, 4.1, 4.7, 4.9, 4.10, Table 14, Table 15
