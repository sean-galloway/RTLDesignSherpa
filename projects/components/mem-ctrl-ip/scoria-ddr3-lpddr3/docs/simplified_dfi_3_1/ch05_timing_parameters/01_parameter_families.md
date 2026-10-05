# Parameter Families

DFI timing parameters are named `dfi_t*` in the specification text, though
the signal names omit the `dfi_` prefix for brevity. Each family constrains
a different part of the MC/PHY contract.

## PHY-defined vs MC/system-defined parameters

| Defined by | Examples | What the value tells you |
| --- | --- | --- |
| PHY | `tctrl_delay`, `tphy_wrlat`, `tphy_wrdata`, `tphy_rdlat`, `tphy_rdcslat`, `tphy_wrcslat`, `tphy_*_gap` | How much time the PHY needs internally to retime signals. |
| MC/system | `tcmd_lat`, `trddata_en`, `tctrlupd_min`, `tctrlupd_max`, `tctrlupd_interval`, `tlp_resp`, `tlp_wakeup` | Deadlines or guarantees the MC provides to the PHY. |
| Both/system | `twrdata_delay`, `terror_resp`, `tinit_start`, `tinit_complete`, parity/CRC latencies | Coordinated timing across both sides. |

: Timing parameter ownership

## Parameter families

| Family | Purpose |
| --- | --- |
| Command timing | `tcmd_lat`, `tctrl_delay` relate the command bus to chip select and to the DRAM pins. |
| Write data timing | `tphy_wrlat`, `tphy_wrdata`, `twrdata_delay` schedule write data relative to commands. |
| Read data timing | `trddata_en`, `tphy_rdlat`, `tphy_rdcsgap`, `tphy_rdcslat` schedule read data return. |
| Update timing | `tctrlupd_*`, `tphyupd_type*`, `tphyupd_resp` govern update handshakes. |
| Status/init timing | `tinit_start`, `tinit_complete`, `tdram_clk_disable`, `tdram_clk_enable`, parity/alert latencies. |
| Training timing | `trdlvl_*`, `twrlvl_*`, `tcalvl_*`, `tphylvl*` pace training sequences. |
| Low power timing | `tlp_resp`, `tlp_wakeup` bound the low-power handshake. |
| Error timing | `terror_resp` bounds error reporting delay. |

: Timing parameter families

## Minimum and maximum conventions

Most DFI timing parameters specify a minimum supportable value (often 0 or
1) and leave the maximum implementation-specific. The MC and PHY negotiate
the actual values at integration time. The only hard rule is that the MC
must meet the minimum assertion times and response deadlines, and the PHY
must not exceed the maximum latencies it advertises.

## Frequency-ratio timing

For frequency-ratio systems, timing parameters are defined in terms of DFI
PHY clock cycles. In a matched-frequency system the DFI PHY clock and the
DFI clock are the same, so the distinction disappears.

**Source:** DFI Specification v3.1 sections 3.1-3.8, 5.0
