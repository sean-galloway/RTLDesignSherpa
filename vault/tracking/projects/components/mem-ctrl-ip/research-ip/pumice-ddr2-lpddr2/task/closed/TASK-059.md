# TASK-059: ASAP7 re-baseline on the fixed intake (granite and pumice); page-policy and age-promotion compile-outs measured; the board smoke is a make target

> Source: owner, 2026-10-24, on the list closing TASK-058: "1/2/3 please" --
> 1 re-measure the ASAP7 planes against the fixed read intake as the baseline,
> 2 the page-policy engine (2 516 cells) and the pick arbiter function, as
> policy measurements with a proxy lane and a board smoke each, 3 run the
> board smoke on every build whose area goes in a report. Related: BUG-031
> (the read intake fix), TASK-058, TASK-055 (the engine measured without and
> kept), the store's age flag ("assessed, not taken" in TASK-052).

**Priority:** P2
**Status:** closed 2026-10-24 (ASAP7 baseline for granite + pumice; HAS_AGE=0 default: -491 LUT / -336 FF on the board, cycle-identical; PP_TIMEOUT_CLOSE measured and rejected (-8 % on column streams); make smoke; board 5 140 LUT / 3 196 FF smoked and charred)
**Owner:** TBD

## Scope

1. ASAP7 planes-kept flow on `granite_top_geared` and `pumice_top_geared`
   at the fixed intake: the per-plane table every later trade is measured
   against. Only the read intake moved (1 045 -> 1 210 cells on granite).
2. Compile-time knobs, each measured on the proxy (1 and 8 threads, mixed)
   and on the board (build, program, smoke, char), flipped only if the
   streams stay cycle-identical:
   - page-policy engine: what of its 2 516 cells the shipping mode
     (fixed_open, tr_init 0) actually uses;
   - age promotion in the store and pick (`sched_age_thresh`, `r_aged`): the
     CSR `order_mode = age_threshold` hook, about 250 FF / 200 LUT in the
     store, and the aged-first select in the pick.
3. `make smoke` in the FPGA flow: program the bitstream just built and run
   init + write_read + memtest through the area's runner; the number quoted
   for a build is the one whose smoke passed (BUG-031 was five builds quoted
   without one).

## What landed

- **ASAP7 baseline on the fixed intake** (report 5.19): granite and pumice
  per plane, same flow and geometry as 5.12. Granite 21 220 cells / 3 899
  flops, pumice 46 227 / 5 028; the scheduler plane is where they differ
  (pick 2 492 against FR-FCFS 22 633), storage is level in cells (6 317 FIFO
  store against 6 162 for two CAMs).
- **`HAS_AGE`** (`mc_bank_fifo_store`, granite default **0**): the age
  promotion hook (`SCHED_POLICY.age_thresh` -> per-slot 16-bit ages, a shared
  counter, 16 subtract-compares -> the pick's aged-first select) compiles out.
  No host configuration has ever programmed `age_thresh`; the RDL field now
  says it is inert in granite (CSR regenerated, docs only).
- **`PP_TIMEOUT_CLOSE`** (`mc_page_policy` HAS_TIMEOUT_CLOSE, via the
  plane; granite default **1**, a knob): measured and REJECTED, below.
- **`PP_TELEMETRY`** (`mc_page_policy` HAS_TELEMETRY): granite_core passes 0
  because it wires no *_STATS CSRs. No board change (Vivado already pruned
  the open outputs); the ASAP7 engine goes 2 516 -> 770 cells, 688 -> 192
  flops, which is the honest ASAP7 number for granite from now on.
- **`make smoke`** (make/fpga_flow.mk): `program` + `SMOKE_SEQUENCES` through
  the area runner with `RUN_ARGS`; granite sets `--controller granite` and
  `init write_read memtest`. Handbook `fpga/cmn-infra/build-flows.md`: a
  quoted utilization is a smoked bitstream.
- `GRANITE_STORE_BACKEND` as a board knob (used by the BUG-031 bisect).
- Harness bridge regenerated under the current generator (one line in the
  sizing report, `xbar_slot_depth`); the prebuild drift check had refused
  the build.

## Measured

Proxy, board geometry, against the committed grid (and the cap-6 default
for mixed), mismatched 0 everywhere:

| knob | 1 thread (4 cells) | 8 threads (4 cells) | mixed |
|---|---|---|---|
| `HAS_AGE=0` | identical | identical | identical (106.5) |
| `PP_TIMEOUT_CLOSE=0` | col_ilv wr **460.8 -> 421.3** (-8.6 %), 3 identical | col_major **459.7 -> 422.4 wr** (-8.1 %), col_ilv wr +0.8, 2 identical | **106.5 -> 103.7** (-2.6 %) |

The idle-timeout close is load-bearing: the open_page configuration the
host programs for every granite measurement writes `tr_init` 1, so a row
with no demand closes one idle cycle later and the next bank's ACT finds it
precharged. (The "tr_init 0" in TASK-055's note was the CSR reset value,
not the measured configuration.) With the timers compiled out the whole
engine vanishes in granite (4 cells): its drain mask feeds only pumice's
FR-FCFS arbiter and its auto-precharge outputs are constant in fixed_open,
so for granite the engine IS the idle-timeout close and nothing else is
left to remove from it.

ASAP7, granite_top_geared, planes kept, against the telemetry-off baseline
19 507 cells / 3 403 flops: `HAS_AGE=0` 18 042 / 3 339 (store 6 287 ->
4 844, -1 443 cells, -64 flops); `PP_TIMEOUT_CLOSE=0` 18 930 / 3 211
(scheduler plane 5 824 -> 5 077, -747 cells, -192 flops) -- rejected.

Board, Nexys A7-100T, final text (`HAS_AGE` 0): granite_core **5 631 ->
5 140 LUT, 3 532 -> 3 196 FF**, WNS +0.177 ns, 0 failing endpoints, 0
multi-driven reports. `make smoke`: leveled init PASS, write_read PASS
mismatched 0, 128 MB memtest PASS 32 / 32. char (open_page, bl8): rd 577.8 /
wr 576.2 MB/s incremental, 333.0 / 291.8 column-major -- identical to the
BUG-031 fixed baseline (577.8 / 576.0).

## Gates

Verilator lint on `granite_top_geared` at default, `HAS_AGE=0` and
`PP_TIMEOUT_CLOSE=0` (3 pre-existing warnings only); granite suite 6 / 1
xfail at `HAS_AGE=0`, at `PP_TIMEOUT_CLOSE=0`, at both, and at the final
defaults (clean-all each); proxy lanes age0 / to0 5 cells each plus the
final-default std_n1, cycle-identical where claimed; ASAP7 base / age0 /
to0 / pumice; board build + `make smoke` + char on the final text;
task-tracker PASS.
