# ISSUE-022: two tREFI soft violations per perf-proxy run on the BANK_PICK core (none on FRFCFS)

**Priority:** P2
**Status:** closed 2026-10-22 (bug, fixed in mem-ctrl recovery Phase 3)
**Owner:** TBD
**Filed:** 2026-10-22 (mem-ctrl recovery Phase 2 report, section 5)
**Repro:** `cd projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2_char_framework/dv/tests && TEST_TREFI=585 TEST_TXN=256 TEST_FAMILIES=col_major python3 -m pytest test_ddr2_char_perf.py -v -s` (after `source env_python`): the calibrated DFI checker reports `tREFI: 2` in `model_violations`. Same run with `TEST_SCHED_CORE=0` reports none.

## Observation

Every BANK_PICK perf run -- one or four generators, any family set, txn 256
or 1024, the default or the tRTP=1 profile -- ends with exactly 2 `tREFI`
soft violations (the model's tREFI MAXIMUM exceeded between two refreshes).
Zero on the FRFCFS core in the identical harness. Data is golden in every
run (mism 0) and the pumice refresh suite (refresh_credit, refresh_collide,
refpb) passes at both geometries, so this is a model-reported spacing
excursion, not a functional failure.

## Suspects

- The first refresh interval after init: the per-bank core's REF all-idle
  gate waits on the LIVE activate-ready bits (tRP / tRC exact) where FRFCFS
  used its registered row image; if the first REF after bring-up lands a few
  cycles later than the model's deadline, that is one of the two.
- The drain-to-grant distance under a column stream: the override drains
  rows with PREs decided from the registered image and grants when every
  bank is activate-ready; a stream that keeps re-opening banks between the
  refresh request and the drain could push one episode past tREFI.
- Constant count = two specific episodes, not a rate: log the model's
  violation cycles (`PERF_CMD_TRACE=1` gives the ACT/PRE/RD/WR fire cycles;
  add the REF strobe) and read them against the refresh controller's
  `obs_refi_cnt_o`.

## Resolves into

A bug if an episode exceeds tREFI by more than the refresh controller's
postpone credit allows; a no-action note with the two cycles cited if it is
the bring-up interval.

## Resolution (2026-10-22, recovery Phase 3)

It was the first suspect, and a real bug, not the bring-up interval.
`mc_bank_pick` pulsed `refresh_grant_o` for ANY REF / REFpb it fired through
its override, and the DDR2 init sequence's two refreshes pass through that
same override (`init_cmd_*` while `!init_done_i`). `mc_xddr2_refresh_ctrl`
banks a grant with no backlog as a PULL-IN credit (JEDEC pull-in), and a
banked credit silently consumes the next tREFI tick instead of raising a
request. Two init-time credits, two skipped ticks, two tREFI maxima exceeded
at the model -- on every run, any length, exactly 2. The FRFCFS core's grant
is a registered request-side pulse (`r_grant`), so it never counted the init
refreshes: none on FRFCFS.

Fix: `refresh_grant_o` is gated on `init_done_i` (one term,
`mc_bank_pick.sv`). Verified: the perf proxy's `model_violations` on the
Phase 3 text is `{'tWR': 255}` (the pre-existing Phase 0 §5 note) with no
`tREFI` entry; `refresh_credit` / `refresh_collide` pass at both geometries.
The same credits were why `refresh_credit`'s strict arm saw 2 instead of 3
REFs once the Phase 3 core ran the stretch at 16.5 cycles per burst instead
of Phase 2's 27 (the third request landed after the window).
