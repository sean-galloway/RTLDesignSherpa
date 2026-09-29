# ISSUE-002: the latency-threshold event reaches r_dropped combinationally from the R handshake: 11.7 ns, 21 levels on Artix-7 at 10 ns

**Priority:** P3
**Status:** CLOSED 2026-09-28 (fixed the same day)
**Owner:** TBD (monitor-lite)
**Found:** 2026-09-28, re-synthesizing `bridge_1x2_rd_lite_mon` on the Artix-7 100T -1 at 10 ns for amba ISSUE-001

## Observed

With the group planner path fixed (amba ISSUE-001), the worst
register-to-register path of the lite bridge fixture is inside the lite:

```
Source:      u_cpu_rd_adapter/.../i_r_channel/g_slot[0].r_data_reg[0][36]/C    (the R skid's RRESP)
Destination: .../gen_monitor_lite.axi_monitor_lite_inst/r_dropped_reg[13]/D
Data Path Delay: 12.633 ns (logic 5.036 ns, route 7.597 ns)
Logic Levels: 22 (CARRY4=10 LUT2=1 LUT3=2 LUT4=2 LUT5=2 LUT6=5)
WNS -3.745 ns, 120 failing endpoints, all into r_dropped of the three lite instances
```

`report_timing` on the routed checkpoint, worst path into `r_dropped`:
slack -3.745 ns from the `sram_rd_axi_rid[2]` input, 11.709 ns, 21 levels
(CARRY4=10). For comparison the fixed group planner paths in the same
checkpoint meet with +3.3 ns (stage 1) and +4.3 ns (stage 0).

The fixture met at -0.160 ns on 2026-09-25 with the same part and period;
this path did not exist then. It is the latency-threshold event added on
2026-09-26: `w_lat_evt = w_compl_clean && cfg_threshold_enable && latency > cfg_latency_threshold`
is combinational off the R handshake (`data_resp` into `w_compl_clean`, the
completion slot pick, the `r_now - r_ts0[slot]` subtract and a 32-bit compare)
and feeds `w_lat_lost` -> `w_lost` -> `r_dropped` in the SAME cycle. Every
other event goes through the registered event stage first; this one does not.
On the Kintex-7 325T -2 at 6.667 ns the same fixture still meets.

## What to change

Register the latency event like the others (a `r_e_lat` in the event stage
with its slot and latency), and derive `w_lat_lost` and `r_lat_pend` from the
registered copy. The drop counter then depends only on flops. This is the same
"events registered before the pick" rule the rest of the lite already follows;
the latency event was bolted on after that pass. Combine with monitor-lite
TASK-004 (hold the timeout/latency payload) if that is done first -- both
touch the same event stage.

## Done when

- [x] `make -C projects/components/fabric-gen-ip/bridge/fpga BRIDGE=bridge_1x2_rd_lite_mon PART=xc7a100tcsg324-1 CLK_NS=10.0 synth`
      shows no failing path into `r_dropped` (the worst lite path named and its slack recorded here)
- [x] `val/amba/monitor-lite` GATE from clean, `formal/amba/axi_monitor_lite` prove + cover, `test_axi_monitor_soak_monlite`

---

## CLOSED 2026-09-28 -- fixed

Sean: "add the pipe stages and rerun all of the val/amba tests for all of
these blocks." The latency-threshold compare now runs one stage after the
completion, from the registered completion flag and latency
(`w_lat_hit = r_e_compl && cfg_threshold_enable && r_e_latency > cfg_latency_threshold`),
and the held event carries its own payload (`r_lat_id`, `r_lat_addr`,
`r_lat_latency`) captured while the completed slot still holds it, instead of a
slot index that a reallocation could overtake. `w_lat_lost` and the drop
counter therefore depend on flops only. The event reaches the pick one cycle
later than before; the packet is unchanged.

Same fixture, part and period (`bridge_1x2_rd_lite_mon`, xc7a100tcsg324-1,
10 ns, routed out of context):

| | Before | After |
|---|---|---|
| WNS / failing endpoints | -3.609 ns / 114 | **+0.443 ns / 0** |
| worst reg-to-reg path | R data -> lite `r_dropped`, 11.7 ns, 21 levels | group `s2_beats_planned` -> `r_plan_addr`, 8.6 ns, 11 levels (meets) |

So the whole lite bridge fixture meets 100 MHz on the Artix-7 -1 for the
first time since the lite grew the latency threshold on 2026-09-26.

Verified on the final RTL from clean builds: `val/amba` GATE 839/839,
`val/amba/monitor-lite` GATE 108/108, `formal/amba/axi_monitor_lite` prove +
cover PASS; `val/amba/monitor-lite` FUNC 201/201; `val/amba` FUNC 1055/1055 (25 min, clean build). The AXIS
lite was not changed: its events are shallow handshake and ID terms with no
subtract/compare, and it has no fixture measurement either way.
