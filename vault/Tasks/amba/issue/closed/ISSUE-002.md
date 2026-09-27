# ISSUE-002: cam_clear inside the reporter's emission window strands the completion packet under aggressive clock gating

**Priority:** P3
**Status:** closed 2026-09-27 (opened 2026-09-26) -- recorded no-action: the sequence is illegal
**Owner:** TBD

## What was observed

On `axi4_slave_rd_mon_cg`, `axi4_slave_wr_mon_cg`, `axil4_slave_{rd,wr}_mon_cg`
and `axil5_slave_{rd,wr}_mon_cg` with `cfg_cg_idle_count = 0`: a transaction
completes, `cam_clear` is pulsed one to two cycles later, and the completion
packet never reaches `monbus_valid` (the MonbusSlave was stalled, so a parked
packet would have been visible). The same sequence on the master wrappers, on
the AXI5 slave wrappers, at `cfg_cg_idle_count = 4`, and on every
`*_monlite_cg` wrapper delivers the packet. Measured 2026-09-26 by the
BFM-driven `val/amba/test_mon_cg_gating.py` before its housekeeping was moved
to after delivery (6 of 32 cells).

## Likely mechanism

The `_mon_cg` liveness terms are `|active_transactions` (CAM occupancy) and
`w_monbus_valid`. Between the completion retiring the CAM entry and the
reporter presenting the packet on `monbus_valid` there are two to four cycles
(retire -> reporter FIFO -> output register). `cam_clear` in that window
empties the CAM, so with idle-count 0 both liveness terms are low for those
cycles and the clock stops with the packet inside the reporter. Nothing left
awake re-starts it. The lite's registered event stage and output queue are
short enough (one to two cycles) that its packet is on the bus before the
clear lands, which is why the `_monlite_cg` wrappers do not show it.

## Why it is filed rather than fixed here

`cam_clear` is a software clear of the transaction table, not a traffic-path
control; issuing it during the emission window of a just-completed
transaction is an unusual sequence. The gating test now delivers the packet
before it clears (the housekeeping it was always meant to be). Whether the
reporter's in-flight packet should count as a liveness term (it did for
`w_monbus_valid`, TASK-070) is the design question this issue holds.

## Resolution (Sean, 2026-09-27): "Clearing the table outside of idle is illegal"

Not a defect. `cam_clear` is legal only while the monitor is idle: no
outstanding transactions and no packet in flight. The observed stranding is
what an illegal clear does, and the RTL need not defend against it. The
contract is now written on the `clear` port of `axi_monitor_base`,
`axi_monitor_filtered` and `axi_monitor_lite`, and under "Configuration
cautions" in `monitor_system_architecture.md`. The gating test already
clears only after the completion packet has been delivered.

## Resolves into (as originally filed)

A task on `axi4_*_mon_cg` (extend the activity term with the reporter FIFO's
non-empty flag, or have `cam_clear` also flush the reporter) or a recorded
no-action if `cam_clear` mid-emission is declared out of contract.
