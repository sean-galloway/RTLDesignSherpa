# System Behavior

This chapter covers three DFI 2.1 housekeeping protocols: low power control,
the update mechanism, and the optional frequency change handshake.

## Low power control

The DFI 2.1 low power interface is an opportunity handshake, not a forced state
transition. The MC tells the PHY that the memory subsystem is idle and how
quickly it may need to resume. The PHY decides whether to enter a lower power
state.

### Entry sequence

1. The MC detects an idle window and asserts `dfi_lp_req`.
2. The MC drives `dfi_lp_wakeup` with the required exit time.
3. The PHY either acknowledges within `tlp_resp` cycles or ignores the request.
4. If acknowledged, both `dfi_lp_req` and `dfi_lp_ack` remain asserted while
the PHY is in the low power state.

### Wakeup time adjustment

After the PHY acknowledges, the MC may increase `dfi_lp_wakeup`, allowing the
PHY to pick a deeper state. It may not decrease the value. The final value at
the moment `dfi_lp_req` de-asserts sets the `tlp_wakeup` exit budget.

### Exit sequence

1. The MC de-asserts `dfi_lp_req` when it needs normal operation to resume.
2. The PHY has `tlp_wakeup` cycles to exit the low power state and de-assert
`dfi_lp_ack`.
3. Normal traffic may resume after `dfi_lp_ack` is low.

### Relationship to DRAM power modes

DFI low power is about the PHY, not the DRAM. The DRAM may already be in
self-refresh, power-down, or a deep power-down state through separate CKE and
command sequencing. The DFI low power interface simply lets the MC and PHY
coordinate so that the PHY does not try to issue traffic while the MC thinks it
is allowed to sleep. The DFI clock must remain valid and at a constant
frequency during the entire handshake.

## Update mechanism

The update mechanism lets the PHY or MC pause ordinary traffic so that internal
settings can be refreshed. Typical reasons include temperature compensation of
delay lines or recomputing ODT settings. Both protocols require the DFI to be
idle of control, read, and write traffic during the update window.

### MC-initiated update

The MC asserts `dfi_ctrlupd_req` for at least `tctrlupd_min` and at most
`tctrlupd_max` cycles. The PHY may acknowledge with `dfi_ctrlupd_ack`, in which
case the request stays asserted as long as the acknowledge is high, or the PHY
may ignore it. The MC is required to offer these update windows periodically,
bounded by `tctrlupd_interval`.

At the end of initialization the MC must assert `dfi_ctrlupd_req` to mark the
end of the init sequence. This is often the first update window the PHY sees.

### PHY-initiated update

The PHY asserts `dfi_phyupd_req` with a stable `dfi_phyupd_type` value. The MC
must acknowledge with `dfi_phyupd_ack` within `tphyupd_resp` cycles. The PHY
keeps the request asserted until the update completes, then de-asserts it. The
MC de-asserts `dfi_phyupd_ack` on the cycle after the request drops.

The selected `dfi_phyupd_type` determines which `tphyupd_typeX` bound applies.
Type 0 is the shortest; type 3 is the longest.

### Why the bus must idle

Updates often change delay lines or termination settings that affect how
traffic is driven or sampled. If a read or write were in flight during the
update, its timing assumptions could change mid-burst. Both protocols therefore
require the MC to place the system in a state where no control, read, or write
traffic is moving across the DFI.

### Concurrent updates

If both request signals are asserted simultaneously, either side may
acknowledge the other's request. The unacknowledged request may then be dropped.
This is the only case where the PHY may de-assert `dfi_phyupd_req` without an
acknowledge.

## Frequency change

DFI 2.1 includes an optional frequency change protocol. It reuses the
initialization handshake signals `dfi_init_start` and `dfi_init_complete`. The
protocol exists in the specification, but it is not required for DFI compliance.

### Acknowledged frequency change

1. During normal operation, with `dfi_init_complete` high, the MC asserts
`dfi_init_start` to request a frequency change.
2. The PHY accepts by de-asserting `dfi_init_complete` within `tinit_start`
cycles.
3. The MC continues to hold `dfi_init_start` while the system changes clocks.
4. The PHY re-initializes on the new frequency and re-asserts
`dfi_init_complete` within `tinit_complete` cycles after `dfi_init_start`
de-asserts.

If the PHY does not de-assert `dfi_init_complete` within `tinit_start` cycles,
the MC must abort the request and release `dfi_init_start`.

### Frequency ratio reset

When `dfi_init_start` is asserted for a frequency change, both sides must reset
their DFI read data word pointers to 0. This ensures that the word suffix
alignment is consistent after the clock change.

### Pumice does not implement it

The pumice DDR2/LPDDR2 controller does not implement the frequency change
protocol. Its `dfi_init_start` is used only during initialization, and the DFI
clock ratio is fixed by the PHY integration. A controller that needs runtime
frequency scaling would need to add the acknowledged-frequency-change state
machine to the DFI layer.

**Source:** DFI Specification v2.1.1 sections 3.4, 3.5, 3.7, 4.5, 4.8, 4.11; `docs/pumice_mas/ch03_interfaces/02_dfi_v21_interface_spec.md`
