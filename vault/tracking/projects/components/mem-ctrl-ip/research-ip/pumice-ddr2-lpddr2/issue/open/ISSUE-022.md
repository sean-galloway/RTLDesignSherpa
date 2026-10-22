# ISSUE-022: two tREFI soft violations per perf-proxy run on the BANK_PICK core (none on FRFCFS)

**Priority:** P2
**Status:** open
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
