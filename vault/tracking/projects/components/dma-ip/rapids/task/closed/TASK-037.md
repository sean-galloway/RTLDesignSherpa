# TASK-037: rapids-g firmware as a generic executive plus a policy table

**Priority:** P2
**Status:** closed -- 2026-10-23; opened 2026-10-22; owner idea, accepted; follows rapids TASK-034
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

## Closed 2026-10-23

`rtl/fw_g/sched_g.S` is an executive plus a policy table. The one-slot poll keeps its 4-instruction
chain hook and 7-instruction idle pass; `step` reads STATUS and jumps through `ptab` (64 entries
on the one-hot state, `jalr zero, t3, %lo(ptab)`, kept below 2 KB and checked by the generator).
Every row does one step and returns. The old hand path (`xfer_arm`, `complete_route`, `fetch_go`)
was unreachable and is replaced by one `fw_fault` row: an error word carrying STATUS, then CH_ERROR.

- Full gate from `make clean-all`, 2026-10-23 (one run, every area at the full level):
  rapids fub_g 192, macro_g 270, top_g 183 (16-channel cells now run, 0 skipped; `test_rapids_g_regpath`
  failed 3/3 in that run because the new jump-table check in `bin/gen_rapids_g_fw.py` also applied to
  that test's own program; the check was scoped to the scheduler image and the test re-run 3/3 passed),
  fub 1,740, fub_beats 1,302, macro 843, macro_beats 774, top 183, top_beats 54; STREAM fub 510,
  macro 684 (+5 skipped: the 1-channel cells of the multi-channel test, by design), top 69. 0 failed.
- Mutation set re-run on this image: 11/11 killed. FM1 lives only at two slots per hart, so the
  equivalence bench gained a NUM_HARTS axis; RM1 is killed by the edge test; FM2's code is gone.
- Bench perf (8 channels, 8 harts) against the 2026-10-22 image: linear points equal, EXT 2.4-4.3%
  faster, 64 KB 9,412 vs 9,529 clocks. A +23-clock point under a full run came from poll phase;
  run alone (`PERF_ONLY`) both images give identical cycles.
- Genesys 2 (build gexe, WNS +0.061): 45/45 pass, sim == board 85/85, identical to the gfin image on
  85/85 windows (`byte_perf_gcompare_gexe_rc.json`).
- MAS 0.83 Section 5.3 (executive, Table 5.3.3 policy, Figures 5.3.1/5.3.2); handbook
  `design/firmware-in-rtl.md` holds the three traps.
