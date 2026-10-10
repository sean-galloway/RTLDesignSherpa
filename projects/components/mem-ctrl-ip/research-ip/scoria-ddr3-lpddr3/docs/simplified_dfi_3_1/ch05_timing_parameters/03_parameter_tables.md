# Parameter Tables

This table lists every timing parameter named in the DFI 3.1 inventory,
with a plain-English meaning and the interface it belongs to.

| Parameter | Interface | Meaning |
| --- | --- | --- |
| `tcmd_lat` | Control | Cycles from `dfi_cs_n` assertion to associated CA signals driven. |
| `tctrl_delay` | Control | Cycles from control signal change to that change reaching the DRAM interface. |
| `tphy_wrlat` | Write data | Cycles from write command to `dfi_wrdata_en` assertion. |
| `tphy_wrdata` | Write data | Cycles from `dfi_wrdata_en` assertion to `dfi_wrdata` driven. |
| `twrdata_delay` | Write data / Idle | Cycles from `dfi_wrdata_en` assertion to completion of write data transfer on DRAM bus. |
| `tphy_wrcslat` | Write data | Cycles from write command to `dfi_wrdata_cs_n` assertion. |
| `tphy_wrcsgap` | Write data | Additional cycles between commands when changing target write chip select. |
| `tphy_crcmin_lat` | Write data / CRC | Min cycles from CRC data on `dfi_wrdata_en` to CRC error on `dfi_alert_n`. |
| `tphy_crcmax_lat` | Write data / CRC | Max cycles from CRC data on `dfi_wrdata_en` to CRC error on `dfi_alert_n`. |
| `trddata_en` | Read data | Cycles from read command to `dfi_rddata_en` assertion. |
| `tphy_rdlat` | Read data | Max cycles from `dfi_rddata_en` assertion to `dfi_rddata_valid` assertion. |
| `tphy_rdcslat` | Read data | Cycles from read command to `dfi_rddata_cs_n` assertion. |
| `tphy_rdcsgap` | Read data | Additional cycles between commands when changing target read chip select. |
| `tctrlupd_min` | Update | Minimum cycles `dfi_ctrlupd_req` must be asserted. |
| `tctrlupd_max` | Update | Maximum cycles `dfi_ctrlupd_req` may be asserted. |
| `tctrlupd_interval` | Update | Maximum cycles between `dfi_ctrlupd_req` assertions. |
| `tphyupd_type0` | Update | Max cycles for PHY-initiated update type 0. |
| `tphyupd_type1` | Update | Max cycles for PHY-initiated update type 1. |
| `tphyupd_type2` | Update | Max cycles for PHY-initiated update type 2. |
| `tphyupd_type3` | Update | Max cycles for PHY-initiated update type 3. |
| `tphyupd_resp` | Update | Max cycles from `dfi_phyupd_req` to `dfi_phyupd_ack`. |
| `tinit_start` | Status / Init | Max cycles for PHY to acknowledge frequency-change request. |
| `tinit_complete` | Status / Init | Max cycles for PHY to re-assert `dfi_init_complete` after `dfi_init_start` de-asserts. |
| `tdram_clk_disable` | Status / Clock | Cycles from `dfi_dram_clk_disable` assertion to DRAM clocks held constant. |
| `tdram_clk_enable` | Status / Clock | Cycles from `dfi_dram_clk_disable` de-assertion to first valid DRAM clock edge. |
| `tparin_lat` | Status / Parity | Cycles from command to associated `dfi_parity_in`. |
| `tphy_paritylat` | Status / Parity | Max cycles from `dfi_parity_in` to `dfi_alert_n` assertion. |
| `trdlvl_en` | Training / Read | Min cycles from read training enable to first read/MRR command. |
| `trdlvl_resp` | Training / Read | Max cycles from `dfi_rdlvl_req`/`dfi_rdlvl_gate_req` to enable assertion. |
| `trdlvl_max` | Training / Read | Max cycles the MC waits for `dfi_rdlvl_resp`. |
| `trdlvl_rr` | Training / Read | Min cycles between read training reads/MRRs. |
| `twrlvl_en` | Training / Write | Min cycles from write leveling enable to first `dfi_wrlvl_strobe`. |
| `twrlvl_resp` | Training / Write | Max cycles from `dfi_wrlvl_req` to `dfi_wrlvl_en`. |
| `twrlvl_max` | Training / Write | Max cycles the MC waits for `dfi_wrlvl_resp`. |
| `twrlvl_ww` | Training / Write | Min cycles between `dfi_wrlvl_strobe` assertions. |
| `tcalvl_en` | Training / CA | Min cycles from `dfi_calvl_en` to `dfi_cke` de-assertion. |
| `tcalvl_capture` | Training / CA | Cycles from calibration command to `dfi_calvl_capture` pulse. |
| `tcalvl_resp` | Training / CA | Max cycles from `dfi_calvl_req` to `dfi_calvl_en`. |
| `tcalvl_max` | Training / CA | Max cycles the MC waits for `dfi_calvl_resp`. |
| `tcalvl_cc` | Training / CA | Min cycles between calibration commands. |
| `tphylvl` | Training / PHY request | Max cycles `dfi_phylvl_req_cs_n` stays asserted after acknowledge. |
| `tphylvl_resp` | Training / PHY request | Max cycles from PHY training request to MC acknowledge. |
| `tlp_resp` | Low power | Max cycles from low-power request to `dfi_lp_ack`. |
| `tlp_wakeup` | Low power | Max cycles from request de-assertion to `dfi_lp_ack` de-assertion. |
| `terror_resp` | Error | Max cycles from affected transaction to `dfi_error` assertion. |

: Complete DFI 3.1 timing parameter table

## Programmable parameters

| Parameter | Meaning |
| --- | --- |
| `phycrc_mode` | `0` = MC generates CRC; `1` = PHY generates CRC. |
| `phydbi_mode` | `0` = MC handles DBI; `1` = PHY handles DBI. |
| `phyrdlvl_en` | PHY supports read data eye training. |
| `phyrdlvl_gate_en` | PHY supports gate training. |
| `phywrlvl_en` | PHY supports write leveling. |
| `phycalvl_en` | PHY supports CA training. |

: DFI 3.1 programmable parameters

**Source:** DFI Specification v3.1 sections 3.1-3.8, Tables 5-22
