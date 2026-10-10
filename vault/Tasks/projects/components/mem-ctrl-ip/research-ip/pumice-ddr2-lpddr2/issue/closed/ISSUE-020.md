# ISSUE-020: the paging perf assertions are calibrated against pre-compliant tFAW/tRRD window behavior; pumice's gate cannot be green until they are re-pinned or the pipeline grows a bypass

**Status:** CLOSED 2026-10-08 — option 1 (re-pin) shipped; option 2 (the
skid/bypass) declined for now: it is a microarchitectural feature with
timing-cone risk on the 75 MHz WNS path, not a bug fix, and can be funded
later — the floors would simply be re-pinned again after it lands.
**Priority:** P2 — nothing here is a new RTL defect; it is a set of
assertions whose baselines encode behavior the design no longer exhibits
(willingly), and the gate fails on them in combinations.
**Found by:** closing pumice BUG-021 (the fire-stage tFAW/tRRD gate);
every number below was measured during that close-out.

## What is red

`make -C projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/dv/tests run-all-gate`
runs top at TWO geometries (default bl4x16, then board
TEST_DRAM_BEAT=32 BL=4 DEVICE_W=16). State as of 2026-10-03:

| assertion | geometry | HEAD (pre BUG-021 fix) | with BUG-021 fix | threshold |
|---|---|---|---|---|
| sweep exact-100% write-utilization claim | default | 100.00% PASS | 90.67% FAIL | exactly 100% |
| sweep ISSUE-002 accepted floor (static_close) | board | 21.12% FAIL | 30.14% PASS | >= 26.95% (55% of 49.0% ceiling) |
| `perf_write_ceiling` W-channel stall budget | board | PASS | PASS | <= 16 cycles |
| sched_cross pref_row_first floor (static_close) | both | default PASS / board 38.4% FAIL | 33.57% FAIL (both) | >= 40% |

So at HEAD the gate was ALREADY red (board-geometry sweep floor +
pref floor); the BUG-021 fix greens the board sweep floor and
write_ceiling, and reddens the default-geometry exact-100% claim plus
deepens the already-red pref floor. fub (80) and macro (48) pass clean
in every configuration; formal/pumice is 3/3 PASS with the BUG-021
assertions armed and mutation-checked.

## Why the baselines drifted

Two correctness fixes changed what "compliant" costs, and the
assertions were never re-pinned:

1. **ISSUE-018 (2026-09-28, `12efed003`)** — global_timers now publishes
   next-state readiness, so every window closes one cycle earlier than
   it used to. A/B measured today: revert ONLY global_timers to
   `12efed003^` and the board-geometry sweep static_close goes from
   21.12% (HEAD) to **42.01%**, with no other change. That is a ~21-point
   swing on the same test file. (The accepted calibration is 30.77%, so
   other 09-24..09-28 changes — BUG-003's cmd_valid gate among them —
   account for the rest of the drift; ISSUE-018 is the dominant term.)
2. **BUG-021 (2026-10-03)** — the fire stage now actually enforces
   tFAW/tRRD, so the bank-parallel ACT burst that close-page scheduling
   front-loads into the windows either waits (hold) or was never legal
   in the first place. The default-geometry exact-100% claim was met at
   HEAD with ZERO actlimit stalls — i.e. the windows were not binding at
   all there. With them enforced, static_close shows 162 actlimit stall
   cycles and 90.67%.

Both fixes are KEEPERS — they remove real JEDEC violations that formal
now proves about (BUG-021's issue019 task fails at step 7 the moment the
fix is reverted). The red assertions encode the pre-fix world.

## The decision this files for

Exactly one of:

1. **Re-pin the baselines** — same process ISSUE-002 used: measure the
   new accepted numbers per mode/geometry, record the rationale
   ("windows now enforced; ~9% of the default-geometry close-page stream
   is tFAW waits the design cannot hide without a bypass"), mutation-check
   that the floor still fires. Sean's call, as ISSUE-002's was.
2. **Fund the skid/bypass** — the 90.67%-vs-100% gap is head-of-line:
   during a tFAW hold the single-issue output register parks an ACT in
   front of ready columns. A 1-deep class bypass (squash the held ACT
   back to the pre-pick, serve the column, retry the ACT) recovers most
   of it in principle — but it is a microarchitectural feature with its
   own timing-cone risk (the pick pipeline is the 75 MHz WNS path), not
   a bug fix. Also Sean's call.

**Related:** [[ISSUE-002]] (the accepted-shortfall machinery these
assertions belong to), [[ISSUE-018]] (the dominant cost), [[BUG-021]]
(the fix that surfaced this).

## 2026-10-08 — CLOSED: re-pinned per option 1; two masked fub reds
root-caused to the cocotb 2.1 pin flip, not RTL

**Measured fresh at HEAD (2026-10-08), both geometries**, then re-pinned,
each floor mutation-proven per the ISSUE-002 close discipline (tighten ->
gap-reported failure -> restore):

| assertion | geometry | before | re-pinned to | measured |
|---|---|---|---|---|
| sweep exact-100% write-util claim | default | exactly 1.00 | static_close carved out, floor 0.80 | 90.67% |
| sweep W-run-length claim | default | exactly 1.00 | static_close floor 0.15 | 140/768 = 18.2% |
| sched_cross exact-100% claim | default | exactly 1.00 | static_close floor 0.80 | 92.53-94.81% |
| sched_cross pref_row_first floor | board | 0.40 | 0.30 | 33.57% |

Margins follow the file's existing band (~11-18% under measured, same
shape as ACCEPTED_CEILING_FRAC), so a floor catches a step change, not
drift. Nothing green was weakened: the default-geometry pref_row_first
floor stays 0.75 (measured 76.34%, green), ACCEPTED_CEILING_FRAC,
perf_write_ceiling, and the in_order floors are untouched. Rationale
comments at each site name ISSUE-020 and BUG-021 and state that the
windows are now enforced — the old numbers encoded JEDEC violations, so
re-pinning them to "what the compliant design measures" is the fix, not a
weakening. Option 2 (the 1-deep class bypass / skid) stays declined: it is
a microarchitectural feature on the 75 MHz WNS path, and ISSUE-001's
ruling (flop stages are by design) covers the pipeline depth it would
attack; if it is ever funded, these floors are re-measured and re-pinned
again — that is exactly the machinery this close installs.

**What the red gate was hiding (the BUG-023 lesson, second instance).**
With the perf assertions re-pinned, two fub reds surfaced that had been
masked since 2026-10-06: `test_pumice_dfi_cmd_path` (ValueError driving
`n_subcmd_i=2` into a 1-bit port) and `test_pumice_wr_intake`(+bl8) (RTL
assert "ragged burst awlen+1=5 AXI_BEATS_PER_BURST=4"). Both looked like
training-era RTL fallout (both files last touched by `0439f9d80`); both
were TB-selection bugs from the cocotb 2.1.0 pin flip (`8fb596b57`):
`cocotb_test` now passes the testcase through `COCOTB_TEST_FILTER`, an
UNANCHORED regex, so `cocotb_test_pumice_dfi_cmd_path` also selected
`..._pack` and `cocotb_test_pumice_wr_intake` also selected `..._ragged`.
No RTL defect; the intake guardrail fired correctly on intentionally
illegal traffic that was never meant to run in those builds. Fix: anchor
`testcase=f"{testcase}$"` at the run() call site — 4 sites total,
including two latent prefix collisions swept and fixed the same way
(`wr_splitter` `_single`/`_single_beat`, `top` `_top`/`_partial_rd`/
`_partial_strb`).

**Done when, verified:** top 194/194 at BOTH geometries; the two
repaired fub gates pass on clean rebuild (results XML proves the smoke
build runs exactly its own cocotb test); full `make run-all-gate` green
(fub + macro + top + phy, both geometries) at the closing commit's HEAD.
