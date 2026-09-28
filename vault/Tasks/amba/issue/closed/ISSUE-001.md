# ISSUE-001: monbus_axil4_axil4_group misses 10 ns on Artix-7 through the s1_beats_to_limit CARRY4 chain

**Priority:** P3
**Status:** CLOSED 2026-09-28 (fixed)
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

---

## CLOSED 2026-09-28 -- fixed in `monbus_group_core`

Sean: "Do the fix." The planner's stage 1 is split in two: stage 0 does the
window compare and picks the geometry address (`r_wr_addr` in window, else
base); stage 1 does one 33-bit subtract, `(limit + 1 - gaddr) >> 3`, with
`limit + 1` registered beside the config so the old subtract-compare-increment
collapses to one carry chain and `limit = 0xFFFF_FFFF` cannot overflow it. The
pipeline is four stages; the settle counter now covers the config register
too (five) and resets on a window-config change, because the group-core proof
found the reset-exit case where a flush committed an address planned against
the not-yet-adopted window (the old three-stage design had the same gap;
config is written before any flush in practice, so nothing saw it).

Re-measured on the same fixture, part and period (`bridge_1x2_rd_lite_mon`,
xc7a100tcsg324-1, 10 ns, Vivado 2025.1, routed out of context):

| Path | Before | After |
|---|---|---|
| `r_cfg_base_addr` -> `s1_beats_to_limit` | -0.160 ns, 16 levels (CARRY4=11), 10.105 ns | +3.456 ns, 12 levels (CARRY4=8), 6.489 ns |
| `r_wr_addr` -> `s0_gaddr` (new stage) | -- | +4.495 ns, 6 levels |

The group planner is no longer the fixture's worst path, or in its failing
list at all. The fixture as a whole now fails by -3.609 ns on a DIFFERENT
path that did not exist on 2026-09-25: the lite's latency-threshold event
reaching `r_dropped` combinationally from the R handshake (21 levels). That
is filed as amba/monitor-lite ISSUE-002 with the routed numbers. With the
design failing that badly the placer also leaves one input-port path through
the group (`cfg_mon_group_axi_error_mask[4]` -> `r_fifo_beats`, -0.335 ns,
10 levels); the same class of path sat at +0.271 ns on the 25th and should be
re-read once ISSUE-002 lands.

Verified: `val/amba` group suites 13/13 GATE, STREAM `test_stream_top_monbus`
1/1 GATE, `formal/amba/monbus_group_core` prove (24 assertions, depth 14) and
cover (14/14) PASS on the final RTL. `docs/markdown/rtl-amba/monitor/monbus_group.md`
describes the four stages.
