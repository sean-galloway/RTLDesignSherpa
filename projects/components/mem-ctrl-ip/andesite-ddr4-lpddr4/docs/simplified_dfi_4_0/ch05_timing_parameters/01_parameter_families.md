# Timing Parameter Families

DFI 4.0 timing parameters are named `dfi_t*` or simply `t*` in the spec. They are divided into
families by what they constrain and by which side of the interface defines them.

## Naming convention

- `t` prefix: a timing parameter.
- Middle letters identify the interface: `cmd`, `ctrl`, `phy_wr`, `phy_rd`, `rd`, `wr`, `lp`, `calvl`, `rdlvl`,
  `wrlvl`, `wdqlvl`, `ctrlupd`, `phyupd`, `dram_clk`, `init`, `par`, `phy_mstr`, etc.
- `_min`/`_max` suffixes: minimum or maximum bounds.
- `_type0`..`_type3`: per-class timing for update and PHY master.

## Who defines each parameter

| Source | What it controls | Example parameters |
| --- | --- | --- |
| MC | Controller-side scheduling commitments | `tcmd_lat`, `tparin_lat`, `tctrlupd_*`, `trdlvl_resp`, `twrlvl_resp`, `tcalvl_resp`, `twdqlvl_resp`, `tlp_resp`, `tlp_wakeup`, `tinit_start` |
| PHY | PHY-side propagation and response delays | `tctrl_delay`, `tphy_wrlat`, `tphy_wrdata`, `tphy_rdlat`, `tdram_clk_disable`, `tinit_complete`, `tphy_paritylat` |
| System | Agreed timing visible to both sides | `twrdata_delay`, `trddata_en`, `tcalvl_data`, `tcalvl_strobe`, `tphy_crcmin_lat`, `tphy_crcmax_lat` |

: Timing parameter definition ownership

## Parameter families

### Control timing
`tcmd_lat` and `tctrl_delay` define how commands propagate from MC to DRAM.

### Write data timing
`tphy_wrlat`, `tphy_wrdata` and `twrdata_delay` define when write data follows a write command
and when it completes on the DRAM bus.

### Read data timing
`trddata_en`, `tphy_rdlat`, `tphy_rdcslat`, `tphy_rdcsgap` define when the MC asserts read enable,
when valid data returns, and how rank switches are handled.

### Update timing
`tctrlupd_interval`, `tctrlupd_min/max`, `tphyupd_resp`, `tphyupd_type0..3` bound the update
handshake.

### Status/init timing
`tdram_clk_disable`, `tdram_clk_enable`, `tinit_start`, `tinit_complete`, `tinit_start_min`,
`tinit_complete_min`, `tparin_lat`, `tphy_paritylat` bound initialization, frequency change, clock
disable and parity/alert timing.

### Training timing
Each training operation has its own `_en`, `_resp`, `_max`, `_rr`, `_ww`, `_rw` parameters plus the
CA-specific `tcalvl_*` set and the write-DQ-specific `twdqlvl_*` set.

### Low-power timing
`tlp_resp` and `tlp_wakeup` bound the low-power handshake.

### Error timing
`terror_resp` bounds how quickly the PHY reports an error after the offending transaction.

### PHY master timing
`tphymstr_resp`, `tphymstr_rfsh`, `tphymstr_type0..3` bound the PHY master handshake.

### Disconnect timing
DFI 4.0 adds a pair of `t*_disconnect` and `t*_disconnect_error` parameters for every
disconnectable handshake: update, training, and PHY master.

**Source:** DFI Specification v4.0 sections 3.0-3.14, 5.0
