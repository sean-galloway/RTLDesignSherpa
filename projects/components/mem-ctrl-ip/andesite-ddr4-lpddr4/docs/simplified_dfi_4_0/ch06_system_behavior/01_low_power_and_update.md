# Low-Power Handshake and Update Mechanism

## Low-power control

The low-power control interface lets the MC request that the PHY enter a low-power state. It is split
into separate control and data requests (`dfi_lp_ctrl_req` and `dfi_lp_data_req`) so the two sides
can power down independently.

The MC asserts a request and holds `dfi_lp_wakeup` constant while awaiting acknowledge. The
PHY may acknowledge (`dfi_lp_ack` within `tlp_resp`) or ignore the request. If acknowledged, the
PHY de-asserts `dfi_lp_ack` within `tlp_wakeup` cycles after the request de-asserts.

The andesite design point exposes `dfi_lp_ctrl_req` and `dfi_lp_data_req` but does not consume
acknowledges; an unacknowledged request times out and reports rather than blocking. This is the
same dormant-pair disposition used by its predecessor.

### Wakeup encoding

| `dfi_lp_wakeup` | Target max cycles |
| --- | --- |
| 0000 | 16 |
| 0001 | 32 |
| ... | doubling each step |
| 1110 | 262144 |
| 1111 | Unlimited |

: Low-power wakeup encoding

## Update mechanism

### MC-initiated update

The MC asserts `dfi_ctrlupd_req` for between `tctrlupd_min` and `tctrlupd_max` cycles. The PHY
may acknowledge with `dfi_ctrlupd_ack` before `tctrlupd_min` expires. While the request is
asserted, the DFI bus stays idle.

DFI 4.0 adds a requirement that a `dfi_ctrlupd_req`/`dfi_ctrlupd_ack` handshake complete
immediately before any self-refresh exit command. This guarantees a clean re-entry point.

### PHY-initiated update

The PHY asserts `dfi_phyupd_req` and drives `dfi_phyupd_type` to select one of four time classes.
The MC must acknowledge with `dfi_phyupd_ack` within `tphyupd_resp`. The PHY holds
`dfi_phyupd_req` for up to `tphyupd_typeX` cycles after the acknowledge. The DFI bus idles while
the request is asserted.

### DFI idle definition

The DFI bus is considered idle when no control, write data, read data, or update activity is in
progress. Some training and low-power sequences require the bus to be idle before they begin.

**Source:** DFI Specification v4.0 sections 3.4, 3.7, 4.7, 4.8, 4.13
