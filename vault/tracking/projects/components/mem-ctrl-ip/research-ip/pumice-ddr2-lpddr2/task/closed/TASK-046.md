# TASK-046: a perf-proxy family where the scheduling window matters (`mixed`)

> Source: owner, 2026-10-23 ("Do 1/2/3"), item 2. The four stride
> families (incremental, row_major, col_major, col_major_interleaved) are
> streams: all page hits or all page misses, one direction per phase. None
> of them exercises what a scheduling window is FOR -- re-ordering a mix of
> hits and misses from several requestors -- so "BANK_PICK beats FR-FCFS"
> had only been established on shapes where window depth cannot matter.
> Related: TASK-045 (the FR-FCFS parity work this was the control for),
> Phase 3 report section 5.6.

**Priority:** P2
**Status:** closed 2026-10-23 (landed and measured on both cores)
**Owner:** TBD

## What landed

`projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2_char_framework/dv/tests/perf_mixed_family.py`,
one module imported by BOTH proxies (`test_ddr2_char_perf.py` for pumice,
`test_granite_char_perf.py` for granite) so the two measure the same thing.
`TEST_FAMILIES=mixed`, needs `TEST_NUM_GEN >= 2`.

- Generators are PAIRED on a bank: generator g and g + n/2 both walk bank
  (g mod n/2), one row apart. Each walks its own row row_major (page hits
  inside a thread), so between the two threads of a pair every burst is a
  row conflict. A row-hit scheduler groups a thread's same-row bursts; an
  oldest-first per-bank picker alternates the rows.
- Reads and writes run CONCURRENTLY from one GO (`drv.go(wr_mask,
  rd_mask)`); the read region sits `REGION_ROWS` = 8 rows above the write
  region in the same banks, so the window also carries read/write
  turnarounds and cross-direction bank conflicts.
- The read region is written first, untimed, so the data check holds
  (`mismatched` must be 0; a read of never-written DRAM mismatches by
  construction).
- Reported: each direction's own window as the other families do, plus
  `mixed_cycles` / `mixed_bw_mb_s` over the union window (total bytes of
  both directions / (last stamp of either - first stamp of either)). No
  JEDEC floor and no gate: it is compared across cores, not against a
  number.

## Result (pumice harness, board geometry, 75 MHz, 8 generators, txn 256, blen 8)

| core (`TEST_SCHED_CORE`) | total MB/s | wr / rd MB/s | wr / rd mean latency (cycles) | mismatched |
|---|---|---|---|---|
| FR-FCFS (0, bank preparation, TASK-045 text) | 311.3 | 155.6 / 155.7 | 112.5 / 190.3 | 0 |
| BANK_PICK (1) | 81.9 | 41.0 / 41.0 | 687.4 / 423.0 | 0 |

The per-bank core's head record is the OLDEST schedulable entry of the
bank, and the two threads of a pair interleave in age, so it alternates the
two rows on every column: a PRE + ACT per column, ~15 cycles a column,
which is the 41 MB/s per direction. The FR-FCFS core picks the oldest READY
column across the window, so a thread's 8 same-row columns go out together
behind one ACT. Peak is 600 MB/s; both cores are far below it on this shape
because every row switch costs tRP + tRCD and the directions turn around,
but the ratio is the window.

## Not this task

- LiteDRAM on the same family (its proxy, `test_litedram_char_perf.py`,
  has its own family loop; add the import when a three-way number is
  wanted).
- A board run (the GO register's eight start bits per direction are
  TASK-043).
