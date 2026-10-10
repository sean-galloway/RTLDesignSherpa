# Update Interface

The update interface lets either side ask the other to pause normal traffic so
that internal PHY or MC settings can be updated. There are two protocols: an
MC-initiated update and a PHY-initiated update. Both require the DFI bus to be
idle of control, read, and write traffic while the update is in progress.

## Update signals

| Signal | Direction | Width | Default | What it does |
| --- | --- | --- | --- | --- |
| dfi_ctrlupd_req | MC -> PHY | 1 bit | 0x0 | MC-initiated update invitation; asserted for tctrlupd_min..tctrlupd_max cycles. |
| dfi_ctrlupd_ack | PHY -> MC | 1 bit | 0x0 | PHY acknowledges the MC-initiated update; may remain low to ignore. |
| dfi_phyupd_req | PHY -> MC | 1 bit | 0x0 | PHY-initiated update request; must be acknowledged by the MC. |
| dfi_phyupd_type | PHY -> MC | 2 bits | no default | Selects one of four PHY update time types. |
| dfi_phyupd_ack | MC -> PHY | 1 bit | 0x0 | MC acknowledges the PHY-initiated update. |
: DFI 2.1 update interface signals

## MC-initiated update

The MC asserts `dfi_ctrlupd_req` when it knows the DFI will be idle. The PHY is
free to acknowledge or ignore the request. If it acknowledges by asserting
`dfi_ctrlupd_ack`, the request stays asserted as long as the acknowledge is
high, and the bus remains idle for update-related traffic only. If the PHY
ignores the request, `dfi_ctrlupd_ack` stays low and the MC may de-assert the
request any time after `tctrlupd_min` and before `tctrlupd_max`.

The DFI specification requires the MC to issue update requests and sets a
maximum interval `tctrlupd_interval` between requests. The MC must also assert
`dfi_ctrlupd_req` at the end of initialization to signal that init is complete.

## PHY-initiated update

The PHY asserts `dfi_phyupd_req` when it needs the bus quieted. The request is
accompanied by `dfi_phyupd_type`, which selects one of four timing parameters:
`tphyupd_type0` through `tphyupd_type3`. The type value must remain constant
while the request is asserted.

The MC must acknowledge by asserting `dfi_phyupd_ack` within `tphyupd_resp`
cycles. The PHY keeps `dfi_phyupd_req` asserted until the update completes, then
de-asserts it; the MC de-asserts `dfi_phyupd_ack` on the following cycle. The
entire acknowledged window is bounded by the selected `tphyupd_typeX`.

## Concurrent requests

If both `dfi_ctrlupd_req` and `dfi_phyupd_req` are asserted at the same time,
either side may acknowledge the other's request. The unacknowledged request may
then be de-asserted. This is the only situation in which the PHY is permitted to
de-assert `dfi_phyupd_req` without first receiving an acknowledge.

## Update timing parameters

| Parameter | Meaning |
| --- | --- |
| tctrlupd_interval | Maximum cycles the MC may wait between ctrlupd_req assertions. |
| tctrlupd_min | Minimum cycles `dfi_ctrlupd_req` must be asserted. |
| tctrlupd_max | Maximum cycles `dfi_ctrlupd_req` may be asserted. |
| tphyupd_type0..3 | Maximum cycles `dfi_phyupd_req` may remain asserted after ack, per type. |
| tphyupd_resp | Maximum cycles from `dfi_phyupd_req` to `dfi_phyupd_ack`. |
: Update interface timing parameters

**Source:** DFI Specification v2.1.1 sections 3.4, 4.5
