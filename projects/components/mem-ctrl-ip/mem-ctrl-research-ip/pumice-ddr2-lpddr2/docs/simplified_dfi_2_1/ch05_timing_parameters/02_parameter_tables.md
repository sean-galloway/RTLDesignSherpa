# Parameter Tables

The table below lists every timing parameter named in the DFI 2.1 inventory,
grouped by sub-interface, with a plain-English meaning.

## Control

| Parameter | Meaning |
| --- | --- |
| tctrl_delay | Cycles from DFI control transition to the same transition at the PHY-DRAM boundary. |
: Control timing parameter

## Write data

| Parameter | Meaning |
| --- | --- |
| tphy_wrdata | Cycles from `dfi_wrdata_en` assertion to first `dfi_wrdata` beat. |
| tphy_wrdelay | Optional PHY delay between enable and data in ratio systems. |
| tphy_wrlat | Cycles from write command to `dfi_wrdata_en` assertion. |
: Write data timing parameters

## Read data

| Parameter | Meaning |
| --- | --- |
| tphy_rdlat | Maximum cycles from `dfi_rddata_en` to first `dfi_rddata_valid`. |
| trddata_en | Cycles from read command to `dfi_rddata_en` assertion. |
: Read data timing parameters

## Update

| Parameter | Meaning |
| --- | --- |
| tctrlupd_interval | Maximum cycles the MC may wait between `dfi_ctrlupd_req` assertions. |
| tctrlupd_min | Minimum cycles `dfi_ctrlupd_req` must be asserted. |
| tctrlupd_max | Maximum cycles `dfi_ctrlupd_req` may be asserted. |
| tphyupd_type0 | Maximum cycles `dfi_phyupd_req` may stay asserted after ack for type 0. |
| tphyupd_type1 | Same, for type 1. |
| tphyupd_type2 | Same, for type 2. |
| tphyupd_type3 | Same, for type 3. |
| tphyupd_resp | Maximum cycles from `dfi_phyupd_req` to `dfi_phyupd_ack`. |
: Update timing parameters

## Status

| Parameter | Meaning |
| --- | --- |
| tdram_clk_disable | Cycles from `dfi_dram_clk_disable` assertion to DRAM clocks held constant. |
| tdram_clk_enable | Cycles from `dfi_dram_clk_disable` de-assertion to first valid DRAM clock edge. |
| tinit_complete | Maximum cycles from `dfi_init_start` de-assertion to `dfi_init_complete` re-assertion. |
| tinit_start | Maximum cycles for PHY to de-assert `dfi_init_complete` after a frequency change request. |
| tphy_paritylat | Maximum cycles from `dfi_parity_in` to associated `dfi_parity_error`. |
: Status timing parameters

## Training

| Parameter | Meaning |
| --- | --- |
| trdlvl_dll | Minimum cycles from read-leveling delay load to next read/MRR command. |
| trdlvl_en | Minimum cycles from `dfi_rdlvl_en` to first load or command. |
| trdlvl_load | Minimum cycles from delay update to next `dfi_rdlvl_load`. |
| trdlvl_max | Maximum cycles MC waits for a PHY Evaluation read-leveling response. |
| trdlvl_resp | Maximum cycles from `dfi_rdlvl_req` to `dfi_rdlvl_en`. |
| trdlvl_resplat | Maximum cycles from read/MRR command to valid `dfi_rdlvl_resp`. |
| trdlvl_rr | Minimum command-to-command delay during read leveling. |
| twrlvl_dll | Minimum cycles from write-leveling delay load to next `dfi_wrlvl_strobe`. |
| twrlvl_en | Minimum cycles from `dfi_wrlvl_en` to first load or strobe. |
| twrlvl_load | Minimum cycles from delay update to next `dfi_wrlvl_load`. |
| twrlvl_max | Maximum cycles MC waits for a PHY Evaluation write-leveling response. |
| twrlvl_resp | Maximum cycles from `dfi_wrlvl_req` to `dfi_wrlvl_en`. |
| twrlvl_resplat | Maximum cycles from `dfi_wrlvl_strobe` to valid `dfi_wrlvl_resp`. |
| twrlvl_ww | Minimum strobe-to-strobe delay during write leveling. |
: Training timing parameters

## Low power

| Parameter | Meaning |
| --- | --- |
| tlp_resp | Maximum cycles from `dfi_lp_req` to `dfi_lp_ack`. |
| tlp_wakeup | Maximum cycles `dfi_lp_ack` may remain asserted after `dfi_lp_req` de-asserts. |
: Low power timing parameters

**Source:** DFI Specification v2.1.1 sections 3.1 through 3.7
