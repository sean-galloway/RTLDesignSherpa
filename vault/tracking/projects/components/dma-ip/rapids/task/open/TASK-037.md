# TASK-037: rapids-g firmware as a generic executive plus a policy table

**Priority:** P2
**Status:** open -- 2026-10-22; owner idea, accepted; follows rapids TASK-034
**Owner:** sean galloway

## Why

Owner 2026-10-22: "can we have a simple RTOS that is generic, with a policy layer that handles the
steps?" `rtl/fw_g/sched_g.S` mixes the two today, and both firmware defects found on 2026-10-22 came
from that mix:

- the fast loop and `service` disagreed about who owns an open head: a head that arrived between the
  loop's HEAD_SUM and SUMMARY reads went down `service`'s IDLE / NEXT_DESC path, 314 clocks late
  instead of about 30 (it broke `tile_source_bad_ptype` on 3 of 8 seeds);
- once in `service`, a hart stayed there: `s_xfer` -> `x_armed` -> `prevalidate` re-dispatched itself
  for every following descriptor (about 256 clocks each at 8 harts), so the tight loop won only one
  descriptor in three on `chain_ch8_b64_d16`.

## What

1. Executive (generic, run-to-completion, no preemption: the barrel's harts are the threads). Per
   pass: poll the events in fixed priority (open head first, then SUMMARY / STATUS), pick the slot's
   state with a jump table on the one-hot state (`jalr` through a table, not a branch chain), call
   ONE handler, return to the poll. One image for 1 or 2 slots per hart and either half.
2. Policy layer: one handler per (state, event) in a table -- `judge_head`, `fetch_start`,
   `fetch_error`, `xfer_arm`, `complete_route`, `ext_refill`. A handler does one step and returns;
   none loops or re-dispatches, so no handler can hold a hart.
3. The chain hot path stays a policy hook at the top of the poll (4 instructions from the HEAD_SUM read
   to the CMD write, measured 2026-10-22); the executive must not lengthen it or the 7-instruction
   idle pass.
4. No RTL change expected: STATUS, HEAD_SUM, SUMMARY and CMD already carry what the executive needs.
   The next-address selector (rapids TASK-035) becomes a policy-table entry.

## Done when

The rewritten firmware passes the full rapids-g regression (fub_g / macro_g / top_g) and the firmware
mutation set from clean; the equivalence bench's perf cells and the Genesys 2 gcompare profile are no
slower than the 2026-10-22 image on any point (sim and board, 80/80 windows identical between them);
MAS 5.3 describes the executive and the policy table.
