# Refresh Interaction

Refresh is a DRAM command issued on the DFI control interface. DFI 3.1
does not define refresh timing itself, but it does constrain when refresh
can be scheduled relative to training, updates and low-power states.

## Refresh and training

The MC must complete all in-flight transactions before starting training.
Refresh therefore competes with training for idle-bus windows. DFI 3.1
adds support for refresh during training, meaning the MC is not required to
disable refresh entirely while a training operation is in progress, but the
details depend on the PHY and DRAM capabilities.

## Refresh and update

An update requires the bus to be idle. A refresh command is a command, so
it cannot overlap an update window. The MC must either:

- Finish the refresh before asserting `dfi_ctrlupd_req` or acknowledging
  `dfi_phyupd_req`, or
- Defer the refresh until the update handshake completes.

## Refresh and low power

In self-refresh, the DRAM handles its own refresh. The DFI low-power
interface only informs the PHY that the controller will be idle. When the
MC exits self-refresh, it must issue `dfi_ctrlupd_req` before resuming
normal traffic.

In power-down, refresh is suspended. The MC must ensure that the power-
down duration does not violate the DRAM refresh requirements.

## Scoria note

The scoria controller does not implement a self-refresh or power-down
engine in the generated core. CKE is controlled by software through a CSR.
Refresh commands are issued by the controller's normal scheduler on the DFI
control interface.

**Source:** DFI Specification v3.1 sections 4.6, 4.11.6, 4.12
