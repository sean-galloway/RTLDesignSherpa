# Revision Deltas

## What DFI 2.1 added versus DFI 2.0

DFI 2.1 is backward compatible with 2.0, but it added several optional
features. The most important additions are:

| Feature | What changed |
| --- | --- |
| LPDDR2 support | CA bus mapped onto `dfi_address`, `dfi_rddata_dnv` added, read leveling extended for LPDDR2 gate training. |
| Low power control interface | New `dfi_lp_req`, `dfi_lp_wakeup`, `dfi_lp_ack`, plus `tlp_resp` and `tlp_wakeup`. |
| Frequency ratio | Formalized 1:2 and 1:4 ratios with `_pN` phase copies and `_wN` read data copies. |
| Parity interface | `dfi_parity_in` and `dfi_parity_error` for DDR3 DIMM command parity. |
| Frequency change protocol | Optional runtime frequency change via `dfi_init_start` / `dfi_init_complete`. |
| Update interface | Formalized `dfi_ctrlupd_*` and `dfi_phyupd_*` idle-window handshakes. |
| tphy_wrdata | Made the enable-to-data delay programmable instead of fixed at 1. |
| dfi_data_byte_disable | Optional per-byte disable at initialization. |
: DFI 2.1 additions over DFI 2.0

None of these are required for DFI compliance. A 2.1 MC and a 2.0 PHY can still
interoperate if they only use the common subset.

## What later revisions changed

DFI 3.1 and subsequent revisions moved the standard toward higher data rates
and more complex memories. The brief preview below is based on the public
direction of later DFI versions; this book is scoped to DFI 2.1.

| Area | Later change |
| --- | --- |
| Error reporting | Added `dfi_error` and `dfi_alert_n` style reporting, plus data CRC handling for DDR4/LPDDR4. |
| Multiple channels | Introduced channel indexing for multi-channel PHYs and byte groups. |
| Richer training | Added DBI training, PHY master mode, and more per-bit/per-byte training controls. |
| CA parity | Extended command parity to LPDDR4 CA buses. |
| Frequency change | Refined the frequency change handshake and added gear ratio programming. |
: Brief preview of later DFI revisions

For the pumice DDR2/LPDDR2 controller these later additions are out of scope.
The controller targets only the DFI 2.1 command, write-data, read-data, and
init-status sub-interfaces.

**Source:** DFI Specification v2.1.1 sections 1.0, 3.4, 3.5, 3.6, 3.7, 4.7, 4.8, 4.9, 4.10, 4.11
