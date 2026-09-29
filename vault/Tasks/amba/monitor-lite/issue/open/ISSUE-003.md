# ISSUE-003: axis_monitor_lite decides events and counts drops in one cycle: misses 10 ns on Artix-7 by 1.18 ns (16 levels into r_dropped)

**Priority:** P3
**Status:** open
**Owner:** TBD (monitor-lite)
**Found:** 2026-09-28, the monitor characterization sweep (amba TASK-034)

## Observed

`axis4_master_monlite` at its defaults (data 32, ID 8, skid 4), synthesized
and routed out of context by `rtl/amba/fpga/bin/monitor_synth_sweep.sh`:

| Part, period | WNS register-to-register | Worst path |
|---|---|---|
| Kintex-7 325T -2, 6.667 ns | +0.832 ns (meets) | 17 levels into `u_axis_monitor_lite/r_dropped_reg` |
| Artix-7 100T -1, 10 ns | **-1.181 ns** | 16 levels (CARRY4=5) into `r_dropped_reg[13]` |

The AXIS lite decides every event (stall/timeout age compares, ID and DEST
change, STROBE check, START/PAUSE/RESUME) in the cycle it happens and folds
the count of events it could not queue into `r_dropped` in that same cycle
(`w_lost = w_ev_n - take1 - take2`). That is the shape the AXI lite left
behind in monitor-lite ISSUE-002 and TASK-004: there the events are now
registered before the pick and held with their payload, and the AXI lite
meets 10 ns on the Artix-7 with 0.6 ns to spare in the same sweep.

## What to change

Give the AXIS lite the same event stage: register the fired-event vector and
their payloads, pick from flops, and let the drop counter depend on flops
only. The two-push queue and the ordering rules do not change. Verify with
`val/amba/monitor-lite/test_axis_monitor_lite.py` and the eight
`axis{4,5}_{master,slave}_monlite[_cg]` tests from clean,
`formal/amba/axis_monitor_lite` prove + cover, and this sweep on both parts.

## Done when

- [ ] `axis4_master_monlite` meets 10 ns on the Artix-7 register to register in `rtl/amba/fpga` (numbers recorded here)
- [ ] monitor-lite area GATE + FUNC from clean, AXIS lite formal prove + cover
