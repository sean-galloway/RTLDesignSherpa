# Update Behavior

Updates are short pauses in normal traffic that let the PHY perform
calibration or timing adjustments. DFI 3.1 supports both MC-initiated and
PHY-initiated updates.

## MC-initiated update

The MC asserts `dfi_ctrlupd_req` whenever it knows the DFI bus will be
idle. The PHY may acknowledge with `dfi_ctrlupd_ack` or ignore the
request. The request must last at least `tctrlupd_min` and no more than
`tctrlupd_max` cycles, and the MC must issue a new request at least every
`tctrlupd_interval` cycles.

While the request (and any acknowledge) is asserted, the DFI bus remains
idle except for update-related activity.

## PHY-initiated update

The PHY asserts `dfi_phyupd_req` with a valid `dfi_phyupd_type` when it
needs idle time. The MC must respond with `dfi_phyupd_ack` within
`tphyupd_resp` cycles. The request stays asserted until the update is done
and must de-assert before the selected `tphyupd_typeX` expires.

The MC must not assert `dfi_ctrlupd_req` and `dfi_phyupd_ack`
simultaneously. If both request signals are asserted at once, the PHY may
withdraw its own request.

## Idle-bus definition

The DFI bus is idle when:

- The control interface is not sending commands.
- All read data has been transferred to the MC.
- All write data has been transferred on the DFI bus and completed on the
  DRAM bus.
- No pages are open.

The `twrdata_delay` parameter defines how long after `dfi_wrdata_en` the
write data is guaranteed to have completed on the DRAM bus. This prevents
an update from cutting off a write burst.

## Update after self-refresh exit

After exiting self-refresh, the MC must assert `dfi_ctrlupd_req` before
resuming normal read or write traffic. This gives the PHY a chance to
re-calibrate after the low-power state.

**Source:** DFI Specification v3.1 sections 3.4, 4.6
