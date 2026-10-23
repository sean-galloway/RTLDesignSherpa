# TASK-045: FR-FCFS core -- bank preparation (the row command rides inside the column run)

> Source: owner, 2026-10-23, after TASK-044 closed: "Pumice is supposed to
> be the research uber performant model ... every vendor in the world and
> many research papers say FR-FCFS is highest performing. So either our
> FR-FCFS design is broken or everyone is wrong", then "In these cases
> FR-FCFS should match per bank." Both right. Related: TASK-044 (the hops
> and the close were brought to the floor; the class priority was left
> column-first), TASK-002 (the characterized `access_pref` modes and the
> 100 percent cross gate), TASK-046 (the family where the window matters),
> TASK-047 (dual issue: making the row command's slot free, not just well
> placed), granite's `mc_bank_pick` header (the alternation this ports).
> Phase 3 report section 5.6 has every number below with its trace.

**Priority:** P2 (research SKU parity)
**Status:** closed 2026-10-23 (see Result; board: +0.019 ns, 0 / 108 344, LUT 42 888 / FF 34 026, built text == committed text)
**Owner:** TBD

## Why

Column-first class priority is textbook FR-FCFS and free exactly when the
command bus has slack. At the board point (BL4 on x16, DFI 1:2, one
command per 75 MHz cycle) one column per cycle fills the data bus AND the
command slot, so every row command costs a column slot and column-first
spent it at the worst moment: after the run, with tRCD in the open. On the
bank walk (col_interleave) that was 12 command slots per 8-column row
against the 9 a prepared bank needs; 383 vs 455 MB/s one thread, 469 vs 502
eight threads. The per-bank core had this right (its ACT/PRE-vs-column
alternation), which is the whole of why it was "beating" the research
core on the streams.

## What landed (common-ip, so scoria / andesite / granite-FRFCFS get it too)

1. **`mc_cmd_arbiter`: `access_pref` 0 = bank preparation.** After a column
   a ready row command takes the slot (an ACT to an idle bank, the demand
   PRE of a drained one); after a row command, columns; one class pending
   falls through (`r_last_was_col`, updated on output-register acceptance).
   A row command never takes a column's ELIGIBLE slot -- it follows the
   column that just fired, inside that column's tCCD -- which is what
   row_first (2) gets wrong (TASK-002's "one slot in five"). At tCCD >= 2
   the alternation and column-first measure the same. Column-first is kept
   as encoding 1 and is now the 11th row of the TASK-002 cross gate
   (`pref_col_first`). 2 row_first and 3 precharge_first unchanged.
2. **`mc_cmd_arbiter`: the fire stage owns the close.** The close-on-drain
   candidate (age-youngest same-row column) assumed strictly oldest-first
   column issue; with a row command interposing, the pre-pick column drops
   back to classify and re-issues behind its younger sibling, so the
   candidate was demoted (sibling in window) and the true last column had
   no flag: 61 of 128 read rows left open, a demand PRE each two slots
   later. Now a firing column with no same-(bank,row) entry anywhere in the
   live window (valid or pending, either direction), on a bank the page
   policy has armed, closes (`w_ap_last`, promote as well as demote;
   `cmd_op_o` follows `w_ap_fire` both ways). Holding the pre-pick column
   instead was tried and made it worse (115 rows): the refused STAGE-1b
   selection was masked as in flight all the same.
3. **`mc_scheduler_plane` (FR-FCFS branch): pending writes are demand** for
   the idle-timeout veto (`wr_sch_pend_i`). **`mc_page_policy`: drain-close
   also arms on a demand precharge followed by an ACT to a different row**
   (`!r_to_closed`). Both measured inert on the proxy families (305 fewer
   explicit PREs per eight-thread run, bandwidth within 3 MB/s); kept
   because they are the correct predicate.
4. **`mc_cmd_arbiter`: registered-only guard for the idle-timeout close
   branch** (`w_guarded_to`). The complete text built to -0.200 ns at 75 MHz,
   bit-identical across two builds (the flow is deterministic), on the
   arbiter's `r_rd_pop -> arg_sel -> in-flight shadow -> guard -> r_bank`
   path; an out-of-context run at the board generics showed the new text
   did not deepen that path (19 vs 20 LUT levels, 3.08 vs 3.40 ns logic),
   so the loss was placement, and the cure is a shorter cone: the timeout
   branch now reads the pre-pick and output-register shadows only, not the
   STAGE-1b selection of the same cycle (an ACT is selected at 1b for an
   open bank only while it is closing, which a timeout target is not; a
   column or demand PRE for that bank would meet the closed row at its fire
   stage and be rejected there). Refresh / ZQ drain guards unchanged. Proxy
   numbers bit-identical before and after.
5. **Bench and knobs.** `dv/tests/top/test_pumice_core_bankprep.py`: the
   isolated core against the JEDEC-timed DFI slave, one 8-column row per
   burst hopping banks (`TEST_BANKS` 1 = the col_major shape), every fire
   logged, cycles per row and explicit PREs per phase, a per-cycle arbiter
   trace (`ARB_TRACE_START/_N`) that lists the same-row siblings the fire
   stage sees. 40 s a run; this is where both mechanisms were found. Perf
   proxy: `TEST_ACCESS_PREF`, `PERF_ARB_TRACE` (rows to `<dump>.arb.txt`).
   CSR desc, MAS (scheduler chapter, CSR map, family config bits),
   design-requirements, AT-A-GLANCE, tracker names updated; pumice CSR
   block regenerated (docs only changed).

## Result

Isolated bench, board geometry, bench timings (tRCD 3 / tRP 3), 128 rows:

| text | wr slots per row | rd slots per row | rd rows left open |
|---|---|---|---|
| column-first (was default) | 12 | 10-18 (3 / 17 / 18 pattern) | 0 |
| alternation only | 9 | 9 / 11 | 61 |
| alternation + pre-pick hold | 9 | 11 | 115 |
| alternation + fire-stage close (shipped) | 9 | 9 | 0 |

Perf proxy, wr / rd MB/s (granite BANK_PICK for reference):

| threads | family | TASK-044 | TASK-045 | BANK_PICK |
|---|---|---|---|---|
| 1 | incremental / row_major | 560 / 559, 568 / 569 | 564 / 559, 568 / 568 | 568 / 568, 576 / 572 |
| 1 | col_interleave / col_major | 383 / 457, 309 / 351 | 458 / 501, 309 / 351 | 461 / 451, 311 / 358 |
| 8 | incremental / row_major | 510 / 538, 511 / 539 | 539 / 560, 539 / 561 | 557 / 555, 558 / 557 |
| 8 | col_interleave / col_major | 469 / 508, 385 / 460 | 516 / 537, 459 / 507 | 538 / 532, 460 / 458 |

Reads at or above the per-bank core everywhere; writes match at one thread
and trail by 3-4 percent at eight. That residual is the idle timer
(`tr_init` 2) closing banks whose generator has nothing in the 16-entry
window -- 761 ACTs per 16 384 incremental columns against 523, where the
walk needs one row per 2 048 -- a policy default question (report 5.2 /
section 6), not the pick core: `tr_init` 8 is identical to 2 (539 / 560, 540 / 562, 516 / 538), `tr_init` 0 (timer
off) gives 555 / 560, 556 / 561, 524 / 540, 458 / 507 -- the streaming writes
land on the per-bank core's 557 / 558 and col_interleave closes to 524 vs
538. So the FR-FCFS core matches at eight threads too once the idle close
is not taking its free slots; what the default should be above one thread
is the policy question already filed in section 6.

On the family where the window matters (TASK-046 `mixed`, eight
generators): FR-FCFS 311 MB/s total, BANK_PICK 82.

Gates: pumice 218 / 218 both geometries, TASK-002 cross gate with the new
row, BUG-027 cells and close_drain both geometries, granite 6 / 1 xfailed,
common-ip 25 / 3 xfailed, formal prove PASS from clean, area lint clean
(pumice / scoria / andesite). Board: arbiter-only text -0.156 ns (15
endpoints, 7 arbiter / 8 harness, route-dominated), LUT 42 842 / FF 33 956;
complete text: +0.019 ns, 0 / 108 344, LUT 42 888 / FF 34 026, built text == committed text

## Not this task

- Making the row command's slot free rather than well placed: TASK-047.
- The `tr_init` default at thread counts above one (section 6 of the
  report; a paging-mode policy decision).
- The per-bank core's own window blindness on `mixed` (82 MB/s): the head
  record is oldest-first by design; a row-hit-first head would be a
  granite task.
