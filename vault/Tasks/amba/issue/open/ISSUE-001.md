# ISSUE-001: monbus_axil4_axil4_group misses 10 ns on Artix-7 through the s1_beats_to_limit CARRY4 chain

**Priority:** P3
**Status:** open
**Owner:** TBD
**Found:** 2026-09-25, synthesizing the amba/monitor-lite TASK-001 lite fixture

**Observed.** `bridge_1x2_rd_lite_mon` routed out of context on the Artix-7
100T -1 at 10 ns (Vivado 2025.1, `projects/components/bridge/fpga/`) misses
by 0.160 ns. The worst register-to-register path is not in a monitor:

```
Source:      u_mon_axil_group/u_core/r_cfg_base_addr_reg[11]/C
Destination: u_mon_axil_group/u_core/s1_beats_to_limit_reg[0]/D
Logic Levels: 16 (CARRY4=11 LUT4=1 LUT5=1 LUT6=3)
Data Path Delay: 10.105 ns (logic 4.656 ns, route 5.449 ns)
```

`r_cfg_base_addr` feeds a window compare (`s1_in_window`, three CARRY4),
whose result then gates a second subtract (`s1_beats_to_limit`, eight
CARRY4) in the same cycle: two adder chains back to back, eleven CARRY4 deep.
The full-monitor bridge (`bridge_1x2_rd_mon`) on the same part misses by
0.303 ns with its worst path inside `monitor_trans_cam`; this group path is
in that design too, behind the CAM's. On the Kintex-7 325T -2 at 6.667 ns
both bridges meet (+1.09 ns lite, +0.21 ns full).

**Why it is an issue and not yet a task.** The block is shared by every
monitored bridge and by the STREAM monitor builds, which currently close at
their frequencies. Whether 10 ns on an Artix-7 is a requirement for any
consumer of the group is not established; if it is, the fix is to register
`s1_in_window` and take the beats-to-limit subtract a cycle later (the group
core is already staged: `s1_*`).

**Resolves into:** a task if a consumer needs the Artix-7 at 100 MHz with
a monbus group; otherwise a recorded no-action on this page.
