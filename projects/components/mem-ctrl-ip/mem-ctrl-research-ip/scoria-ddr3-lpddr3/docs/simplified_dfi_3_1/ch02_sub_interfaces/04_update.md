# Update Interface

The update interface lets the PHY and MC pause the DFI bus to perform
calibration, timing adjustments or other maintenance. The DFI bus must be
idle during an update: no commands in flight, all read and write data
finished, and write data fully retired on the DRAM bus.

## MC-initiated update

| Signal | From | Width | Default | What it does |
| --- | --- | --- | --- | --- |
| `dfi_ctrlupd_req` | MC | 1 bit | 0x0 | MC tells the PHY that the DFI bus will be idle and the PHY may update. |
| `dfi_ctrlupd_ack` | PHY | 1 bit | 0x0 | Optional PHY acknowledge. If asserted it must be before `tctrlupd_min` expires. |

: MC-initiated update signals

`dfi_ctrlupd_req` must be asserted for at least `tctrlupd_min` cycles and no
more than `tctrlupd_max` cycles. The maximum interval between assertions is
`tctrlupd_interval`. The PHY is not required to acknowledge, but if it does
the DFI bus stays idle while both request and acknowledge are asserted.

After self-refresh exit, `dfi_ctrlupd_req` must be asserted before read or
write traffic resumes.

## PHY-initiated update

| Signal | From | Width | Default | What it does |
| --- | --- | --- | --- | --- |
| `dfi_phyupd_req` | PHY | 1 bit | 0x0 | PHY requests idle time on the DFI bus. |
| `dfi_phyupd_type` | PHY | 2 bits | none | Selects one of four update types. |
| `dfi_phyupd_ack` | MC | 1 bit | 0x0 | MC grants the request. |

: PHY-initiated update signals

When the PHY needs the bus idle, it asserts `dfi_phyupd_req` with a valid
`dfi_phyupd_type`. The MC must respond with `dfi_phyupd_ack` within
`tphyupd_resp` cycles. The request remains asserted until the update
completes, and must de-assert before `tphyupd_typeX` cycles have elapsed
after the acknowledge. The MC must not assert `dfi_ctrlupd_req` and
`dfi_phyupd_ack` at the same time.

## Update timing parameters

| Parameter | Defined by | Meaning |
| --- | --- | --- |
| `tctrlupd_min` | MC | Minimum cycles `dfi_ctrlupd_req` must be asserted. |
| `tctrlupd_max` | MC | Maximum cycles `dfi_ctrlupd_req` may be asserted. |
| `tctrlupd_interval` | MC | Maximum cycles the MC may wait between `dfi_ctrlupd_req` assertions. |
| `tphyupd_type0` | PHY | Max cycles for `dfi_phyupd_type = 0`. |
| `tphyupd_type1` | PHY | Max cycles for `dfi_phyupd_type = 1`. |
| `tphyupd_type2` | PHY | Max cycles for `dfi_phyupd_type = 2`. |
| `tphyupd_type3` | PHY | Max cycles for `dfi_phyupd_type = 3`. |
| `tphyupd_resp` | PHY | Max cycles from `dfi_phyupd_req` to `dfi_phyupd_ack`. |

: Update interface timing parameters

## Simultaneous requests

If `dfi_ctrlupd_req` and `dfi_phyupd_req` are asserted together, the MC is
forbidden from asserting `dfi_phyupd_ack` at the same time as
`dfi_ctrlupd_req`. The PHY may de-assert its own request in this case, and
the acknowledged request follows its normal protocol.

**Source:** DFI Specification v3.1 sections 3.4, 4.6, Table 12, Table 13
