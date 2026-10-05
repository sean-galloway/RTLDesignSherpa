# Low Power Behavior

DFI 3.1's low-power interface is an opportunity request: the MC suggests
that the PHY may save power, but the PHY decides whether to take the
opportunity. The handshake does not directly enter DRAM self-refresh or
power-down; those are DRAM commands issued through the control interface.

## Low-power request split

v3.1 splits the v2.1 `dfi_lp_req` into:

- `dfi_lp_ctrl_req`: no more commands on the control interface.
- `dfi_lp_data_req`: no more activity on the data interface.

This allows the PHY to sleep the command path and data path separately.
For example, a state that still refreshes memory can keep the control path
awake while the data path sleeps.

## Typical sequence

1. The MC issues the DRAM command to enter the desired low-power state
   (power-down enter or self-refresh enter) on the control interface.
2. The MC asserts `dfi_lp_ctrl_req` and/or `dfi_lp_data_req` with an
   appropriate `dfi_lp_wakeup` value.
3. The PHY may acknowledge with `dfi_lp_ack` within `tlp_resp` cycles.
4. The low-power state persists while request and acknowledge are both
   asserted.
5. When the MC needs to resume, it de-asserts the request.
6. The PHY de-asserts `dfi_lp_ack` within `tlp_wakeup` cycles and normal
   operation resumes.

## Relationship to DRAM self-refresh

Self-refresh is a DRAM command, not a DFI state. The DFI low-power
interface merely tells the PHY that the controller will not be sending
commands or data for some time. The PHY may use that information to gate
its own clocks or reduce power, but the DRAM refresh timing is handled by
the DRAM's self-refresh logic once the self-refresh command is issued.

## Scoria note

The scoria controller exposes `dfi_lp_ctrl_req` and `dfi_lp_data_req` for
spec compliance, but the target PHY family does not consume them. CKE is
driven as a CSR bit set during initialization, and the generated core does
not implement a self-refresh or power-down engine.

**Source:** DFI Specification v3.1 sections 3.7, 4.12
