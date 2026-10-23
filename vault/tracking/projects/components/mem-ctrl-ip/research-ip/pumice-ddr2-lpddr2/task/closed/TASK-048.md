# TASK-048: the idle-timeout default above one thread -- `tr_init` resets to 0

> Source: owner, 2026-10-23 ("Do 1"), on the Phase 3 report's section 6
> item: `tr_init` 2 was tuned on one thread (TASK-013, 2026-09-27, before
> close-on-drain existed) and at eight threads it was the whole of the
> FR-FCFS core's remaining write gap to the per-bank core (TASK-045).
> Related: TASK-013 (why the timer came in), BUG-030 (its veto), TASK-044 /
> TASK-045 (the armed close-on-drain that now carries the row walk).

**Priority:** P2
**Status:** closed 2026-10-23
**Owner:** TBD

## Measured (perf proxy, board geometry, 75 MHz, FR-FCFS core, TASK-045 text, wr / rd MB/s)

| threads | family | `tr_init` 2 (old reset) | `tr_init` 0 (new reset) | delta wr / rd |
|---|---|---|---|---|
| 1 | incremental | 564 / 559 | 564 / 565 | 0 / +6 |
| 1 | row_major | 568 / 568 | 574 / 562 | +6 / -6 |
| 1 | col_interleave | 458 / 501 | 457 / 501 | -1 / 0 |
| 1 | col_major | 309 / 351 | 309 / 348 | 0 / -3 |
| 2 | incremental | 566 / 564 | 569 / 568 | +3 / +4 |
| 2 | row_major | 571 / 569 | 568 / 569 | -3 / 0 |
| 2 | col_interleave | 506 / 525 | 498 / 524 | -8 / -1 |
| 2 | col_major | 458 / 504 | 458 / 502 | 0 / -2 |
| 4 | incremental | 557 / 566 | 565 / 566 | +8 / 0 |
| 4 | row_major | 559 / 569 | 567 / 568 | +8 / -1 |
| 4 | col_interleave | 495 / 522 | 497 / 523 | +2 / +1 |
| 4 | col_major | 458 / 506 | 457 / 505 | -1 / -1 |
| 8 | incremental | 539 / 560 | 555 / 560 | +16 / 0 |
| 8 | row_major | 539 / 561 | 556 / 561 | +17 / 0 |
| 8 | col_interleave | 516 / 537 | 524 / 540 | +8 / +3 |
| 8 | col_major | 459 / 507 | 458 / 507 | -1 / 0 |
| 8 | mixed (total) | 311 | 319 | +8 |

`tr_init` 8 at eight threads is identical to 2 (the timer closes at any
lull; its length is not the variable). Timer off never costs more than 8
MB/s in one cell (1.6 percent, two-thread col_interleave writes) and gains
up to 17 at eight threads. One thread is a tie: the armed close-on-drain
(TASK-044/045) now closes a row walk's rows by auto-precharge on the last
visible column, which is what the timer bought there in September.

## What landed

- `pumice_csr.rdl`: `PAGE_TIMEOUT_CFG.tr_init` resets to 0 (was 2);
  `policy_mode` stays 3. Mode 3 with `tr_init` 0 is NOT open page: the
  drain-close arming is keyed on the mode, not the timer. CSR block
  regenerated (reset value in `pumice_csr.sv`, regmap default, docs).
- `csr_reset_parity.py` note, design-requirements, MAS page-policy chapter,
  pumice CLAUDE.md trap 6, the bank-prep bench default: all restated. The
  2026-09-27 board measurement that introduced the timer is kept in the
  MAS as the record of why, marked as pre-close-on-drain.

## Not this task

- granite keeps its own RDL and reset (BANK_PICK's numbers with the timer
  are the per-bank reference in the report).
- The timer itself stays as a runtime knob; nothing is removed.
