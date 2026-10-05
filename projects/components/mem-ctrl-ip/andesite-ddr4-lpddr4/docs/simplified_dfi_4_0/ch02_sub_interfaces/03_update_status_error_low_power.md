# Update, Status, Error and Low-Power Interfaces

These interfaces handle housekeeping: update handshakes, initialization and frequency signaling,
error reporting, and low-power opportunity requests.

## Update interface

The update interface lets either side force a brief idle window on the DFI bus so that the PHY can
update internal delay settings or the MC can update its own state.

| Signal | Width | Default | Direction | What it does |
| --- | --- | --- | --- | --- |
| `dfi_ctrlupd_req` | 1 bit | 0x0 | MC -> PHY | MC-initiated update request. Asserted min `tctrlupd_min` / max `tctrlupd_max` cycles. Required immediately before a self-refresh exit command in DFI 4.0. |
| `dfi_ctrlupd_ack` | 1 bit | 0x0 | PHY -> MC | MC-initiated update acknowledge. PHY may ignore; if acknowledging, must assert before `tctrlupd_min` expires. DFI bus stays idle while asserted. |
| `dfi_phyupd_req` | 1 bit | 0x0 | PHY -> MC | PHY-initiated update request. DFI bus must idle while asserted. |
| `dfi_phyupd_ack` | 1 bit | 0x0 | MC -> PHY | PHY-initiated update acknowledge. MC must assert within `tphyupd_resp` and hold while `dfi_phyupd_req` is asserted. |
| `dfi_phyupd_type` | 2 bits | - | PHY -> MC | Selects one of four PHY update time classes (`tphyupd_type0`..`3`). Constant while request asserted. |

: Update interface signals

### Update timing parameters

| Parameter | Defined by | Description |
| --- | --- | --- |
| `tctrlupd_interval` | MC | Max DFI clocks the MC may wait between `dfi_ctrlupd_req` assertions. |
| `tctrlupd_min` / `tctrlupd_max` | MC | Min/max cycles `dfi_ctrlupd_req` can be asserted. |
| `tphyupd_resp` | PHY | Max DFI clocks from `dfi_phyupd_req` assertion to `dfi_phyupd_ack` assertion. |
| `tphyupd_type0`..`3` | PHY | Max cycles `dfi_phyupd_req` may stay asserted after ack for each type. |

: Update timing parameters

## Status interface

The status interface carries initialization, frequency, clock-disable and parity/alert signals.

| Signal | Width | Default | Direction | What it does |
| --- | --- | --- | --- | --- |
| `dfi_alert_n` | DFI Alert Width | 0x1 | PHY -> MC | CRC or CA parity error indicator. Pulse width mirrors DRAM subsystem error signal. Cycle-suffixed `_aN`. |
| `dfi_dram_clk_disable` | DFI DRAM Clk Disable Width | 0x0 | MC -> PHY | When active, PHY must hold DRAM clocks constant. Timing via `tdram_clk_disable` / `tdram_clk_enable`. |
| `dfi_freq_ratio` | 2 bits | - | MC -> PHY | Frequency ratio indicator: `00`=1:1, `01`=1:2, `10`=1:4, `11`=reserved. Defined at init, then constant. |
| `dfi_frequency` | 5 bits | - | MC -> PHY | Operating-frequency indicator. Up to 32 system-defined encodings. New in 4.0. |
| `dfi_init_complete` | 1 bit | 0x0 | PHY -> MC | PHY ready to accept DFI transactions. All command/status signals hold defaults until it asserts. De-assertion acknowledges a frequency change. |
| `dfi_init_start` | 1 bit | 0x0/0x1 | MC -> PHY | At init: indicates `dfi_freq_ratio` and `dfi_frequency` are valid. During operation: requests a frequency change. |
| `dfi_parity_in` | 1 bit | 0x0/0x1 | MC -> PHY | Command parity, one-to-one with each DFI command. Covers address, bank, bank-group, act_n, cas_n, cid, ras_n, we_n. Phase-suffixed `_pN`. |

: Status interface signals

### Status timing parameters

| Parameter | Defined by | Description |
| --- | --- | --- |
| `tdram_clk_disable` | PHY | DFI clocks from `dfi_dram_clk_disable` assertion until DRAM clock holds low at PHY-DRAM boundary. |
| `tdram_clk_enable` | PHY | DFI clocks from `dfi_dram_clk_disable` de-assertion to first valid DRAM clock rising edge. |
| `tinit_complete` | PHY | Max DFI clocks from `dfi_init_start` de-assertion to `dfi_init_complete` re-assertion during frequency change. |
| `tinit_complete_min` | PHY | Min DFI clocks before `dfi_init_complete` can be driven after a previous command or training event. |
| `tinit_start` | MC | DFI clocks from `dfi_init_start` assertion until PHY must de-assert `dfi_init_complete` to accept frequency change. |
| `tinit_start_min` | PHY | Min DFI clocks before `dfi_init_start` can be driven after a previous command or training event. |
| `tparin_lat` | MC | DFI PHY clocks between DFI command assertion and associated `dfi_parity_in`. |
| `tphy_paritylat` | PHY | Max DFI clocks between `dfi_parity_in` and associated `dfi_alert_n` return (min 0x4). |

: Status timing parameters

### Programmable status parameters

| Parameter | Defined by | Description |
| --- | --- | --- |
| `dfidata_bit_enable` | MC/PHY | Valid data bits on `dfi_wrdata` and `dfi_rddata`. Replaces removed `dfi_data_byte_disable`. |
| `phyfreq_range` | PHY | Number of `dfi_frequency` values the PHY supports (1-32). |

: Status programmable parameters

## Error interface

| Signal | Width | Default | Direction | What it does |
| --- | --- | --- | --- | --- |
| `dfi_error` | DFI Error Width | 0x0 | PHY -> MC | PHY-detected error condition (DRAM errors, DLL lock loss, read DQS error, etc.). Not phased. |
| `dfi_error_info` | DFI Error Width x 4 | 0x0 | PHY -> MC | Additional error-source information. Valid only when `dfi_error` asserted. Partially spec-defined, extensible with design-specific codes. |

: Error interface signals

| Parameter | Defined by | Description |
| --- | --- | --- |
| `terror_resp` | PHY | Max DFI clocks from affected DFI bus transaction(s) to `dfi_error` assertion. |

: Error timing parameter

## Low-power control interface

| Signal | Width | Default | Direction | What it does |
| --- | --- | --- | --- | --- |
| `dfi_lp_ack` | 1 bit | 0x0 | PHY -> MC | Low-power acknowledge. PHY may ignore; if acknowledging, asserts within `tlp_resp` and de-asserts within `tlp_wakeup` after request de-asserts. |
| `dfi_lp_ctrl_req` | 1 bit | 0x0 | MC -> PHY | Low-power request for the control interface: no more commands will be sent. |
| `dfi_lp_data_req` | 1 bit | 0x0 | MC -> PHY | Low-power request for the data interface: no more data will be sent. |
| `dfi_lp_wakeup` | 4 bits | - | MC -> PHY | Requested wakeup time, 16 encodings from 16 cycles (`0000`) doubling up to 262144 (`1110`) and unlimited (`1111`). May increase but never decrease after acknowledge. |

: Low-power control interface signals

| Parameter | Defined by | Description |
| --- | --- | --- |
| `tlp_resp` | MC | Max DFI clocks from low-power request assertion to `dfi_lp_ack` assertion (min 1, max 7; recommended 7). |
| `tlp_wakeup` | MC | Target max DFI clocks that `dfi_lp_ack` may stay asserted after request de-asserts (min 16). |

: Low-power timing parameters

**Source:** DFI Specification v4.0 sections 3.4, 3.5, 3.7, 3.8, Tables 13-17, 21, 22
