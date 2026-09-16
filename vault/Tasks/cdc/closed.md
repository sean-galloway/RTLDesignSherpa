<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# cdc — Closed (done)

_None._

---

## CDC-FORMAL-STALE — the 4-phase handshake formal proof ran against a pre-rename DUT copy
**Status:** CLOSED 2026-09-16 — all three work items done. The proof now reads
the shipped RTL and covers both parameters it could not previously see, and
doing so immediately found a real defect ([[CDC-002]]).

**Item 1 (refresh the forked copy) was overtaken and done better.** The fork
`cdc_handshake_formal.sv` is gone rather than refreshed: the 2026-09-11 sweep
deleted every hand-copied DUT in the repo and moved the tasks onto sv2v, so
`formal/cdc/cdc_4_phase_handshake/` flattens and proves
`rtl/cdc/cdc_4_phase_handshake.sv` itself. The old `formal/cdc/cdc_handshake/`
directory no longer exists. (A copy survives in the stale
`pumice-ataglance-modes` worktree; that checkout is ~677 commits behind and
corrects itself when it takes main.)

**Items 2 and 3 (properties for the two parameters, and re-run).** sv2v keeps
`TIMEOUT_CYCLES` and `FAST_PATH` as real parameters in the flat file, so each
configuration is driven by `chparam` from its own sby task -- the same shape
`wb4_slave`/`wb4_master`/`wb4_retry` already use. Six tasks now:

| task | config | result |
|---|---|---|
| prove / cover | defaults | PASS |
| prove_timeout / cover_timeout | `TIMEOUT_CYCLES=4` | PASS |
| cover_fast | `FAST_PATH=1` | PASS |
| prove_fast | `FAST_PATH=1` | **FAIL — CDC-002, left red on purpose** |

New properties: `ap_no_lost_transfer` (checked in every configuration -- the
source may only accept a new transfer once the destination has actually taken
the previous one), `ap_timeout_quiet_when_idle`, `ap_timeout_fires` (a
transfer stalled past the programmed count MUST raise `src_timeout`, so the
counter cannot silently do nothing), plus covers `cp_timeout` and
`cp_fastpath_taken`. The covers matter: `cover_fast` reaching
`cp_fastpath_taken` proves the fast branch is genuinely exercised, so the
`prove_fast` failure is not vacuous.

**The timeout path is sound.** It was the other "most likely to carry a bug"
candidate and it holds: the count is cleared in `S_IDLE`, never fires before
anything is sent, and always fires once a transfer stalls past the threshold.
