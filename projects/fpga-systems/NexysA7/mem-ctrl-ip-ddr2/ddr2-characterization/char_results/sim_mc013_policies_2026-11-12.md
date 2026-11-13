# Four scheduling policies priced on the Ramulator 2 DDR2 model (memory-controllers MC-013 items 2-5, 2026-11-12)

MC-013 item 1 named the command slot (`sim_mc013_command_slot_dual_issue_2026-11-12.md`)
and MC-014 built the row lane for it. These are the other four items, each a model
number beside a measured or simulated granite number. Model cells are write / read
MB/s at the 100 MHz MC clock (DDR2-400 x16, peak 800) at the board's transaction
counts; `open32` is the 2026-11-11 ideal (pooled FR-FCFS, 32-deep queues, AllBank
refresh) and every other column is one knob away from it (`char_model.py`, the
`CONFIGS` table; CSVs `model_ramulator2_ddr2_<config>_2026-11-12.csv` beside this
file). Granite cells are the sku100 board of 2026-11-09.

## Item 2: write drain -- the hysteresis is worth +4 / +8 percent, and granite already sits at the deep end

Ramulator's controller drains writes when the write queue crosses `wr_high_watermark`
(or no read waits) and returns to reads below `wr_low_watermark`. On `mixed` (four
writers and four readers from one GO, rows 8 apart in shared banks):

| config | lo / hi | mixed wr / rd MB/s | rd hits / misses / conflicts | row_thrash | random |
|---|---|---|---|---|---|
| open32 | 0.20 / 0.80 | 337 / 337 | 707257 / 147206 / 169537 | 779 / 743 | 767 / 760 |
| open32_wm03_97 | 0.03 / 0.97 | **350 / 350** | 715252 / 153768 / 154980 | 779 / 743 | 767 / 760 |
| open32_wm05_25 | 0.05 / 0.25 | 313 / 313 | 679894 / 111168 / 232938 | 779 / 743 | 767 / 760 |
| open32_wm40_90 | 0.40 / 0.90 | 333 / 333 | 703574 / 141470 / 178956 | 779 / 743 | 767 / 760 |
| open32_wm70_95 | 0.70 / 0.95 | 312 / 312 | 677748 / 121231 / 225021 | 779 / 743 | 767 / 760 |
| open8 | 0.20 / 0.80 | 295 / 295 | 767998 / 2 / 256000 | 781 / 782 | 709 / 746 |
| open8_wm03_97 | 0.03 / 0.97 | **320 / 320** | 827077 / 6564 / 190359 | 781 / 782 | 709 / 746 |
| open8_wm05_25 | 0.05 / 0.25 | 235 / 235 | 695067 / 4466 / 324467 | 781 / 782 | 709 / 746 |
| open8_wm40_90 | 0.40 / 0.90 | 279 / 279 | 640041 / 3763 / 380196 | 781 / 782 | 709 / 746 |
| open8_wm70_95 | 0.70 / 0.95 | 240 / 240 | 585497 / 5353 / 433150 | 781 / 782 | 709 / 746 |

Granite sku100 `mixed_bl8`: defaults 251 / 283, open_page 263 / 330.

- The single-direction families do not move at all (the drain never engages).
- On `mixed` the curve is monotonic in drain depth: the deepest drain (enter at
  0.97 full, leave at 0.03) is +4 percent over Ramulator's default on the 32-deep
  queue and +8.5 percent on the 8-deep one; a shallow drain costs 7 / 20 percent.
  Row conflicts, not misses, are what a shallow drain adds (each direction switch
  closes the other direction's rows).
- Granite has no watermark (`SCHED_WR_WM` is inert on the pick core, see the CSR);
  its direction register holds the bus while the owning direction has work, capped
  at `GRANITE_DIR_BATCH_MAX` = 255 column fires. That IS the deep end of this
  curve. **Verdict: a drain threshold is not worth a CSR on granite**; the policy
  it already has is the best point the model finds, and the remaining mixed gap is
  a different mechanism (item 4 and item 5 below).

## Item 3: refresh placement -- 1.7 percent is the tRFC floor, 0.6 percent is recoverable, nothing is worth a CSR

| scenario | open32 | open32_noref | open32_scatter | open32_refburst8 | granite best |
|---|---|---|---|---|---|
| incremental_bl8 | 781 / 783 | 800 / 800 | 781 / 783 | 786 / 786 | 775 |
| row_major_bl8 | 781 / 783 | 800 / 800 | 781 / 783 | 786 / 786 | 778 |
| col_major_bl8 | 465 / 570 | 474 / 582 | 465 / 570 | 466 / 572 | 520 |
| col_major_interleaved_bl8 | 781 / 782 | 800 / 800 | 779 / 782 | 786 / 786 | 688 |
| row_thrash_bl8 | 779 / 743 | 800 / 800 | 779 / 750 | 786 / 751 | 688 |
| random_bl8 | 767 / 760 | 786 / 778 | 767 / 760 | 773 / 764 | 661 |
| mixed_bl8 | 337 / 337 | 345 / 345 | 337 / 337 | 339 / 339 | 330 |

- Refresh costs 2.4 percent on a saturated row-hit stream (781 vs 800). The part's
  tRFC is 127.5 ns = 26 CK of every 1560 CK tREFI = 1.67 percent, a floor no
  scheduler moves: 786.7 MB/s. The other 0.7 percent is the row close before each
  REF and the reopen after it.
- `AllBank(scatter_interval)` staggers the refresh-scope NODES; one rank is one
  node, so the knob shifts the phase of the refresh train (first REF at cycle 195
  instead of 1560) and changes nothing else -- the 0.1 MB/s differences are that
  phase. Not a placement policy at this geometry.
- `open32_refburst8` is eight REFs back to back every 8 tREFI (the DDR2 postpone
  credit, JESD79-2F clause 3.9.4, spent as one burst; modelled as nRFC and nREFI
  both x 8): 786 / 786, the tRFC floor, i.e. the whole 0.6 percent reopen cost
  recovered, +5 MB/s. Granite's `REF_CTRL.refresh_burst` field exists and is tied
  off. **Verdict: below "a few percent"; no RTL task.** If it is ever wanted, the
  field is there and this is its number.

## Item 4: per-bank FIFOs with a rotor vs the pooled queue -- the pure streams tie, `mixed` pays 5 to 12 percent

`BankFIFO-RR` is a new scheduler in the overlay
(`overlay/src/ramulator/controller/scheduler/impl/bank_fifo_rr.cpp`): the oldest
request per bank is that bank's head (no reordering inside a bank -- granite's
bank-FIFO store with one head), the ready heads are offered round robin from the
bank after the last pick, `column_first` lets a ready column beat a ready row (the
pick core's select). `open32_rowhit` is upstream's FRFCFS-RowHit, the pooled queue
that never preempts an open row's hits.

| scenario | open32 (pooled FR-FCFS) | open32_rowhit | open32_bankrr | open32_bankrr_col | open8 | open8_bankrr | open8_bankrr_col | granite defaults | granite open_page |
|---|---|---|---|---|---|---|---|---|---|
| incremental_bl8 | 781 / 783 | 781 / 783 | 781 / 783 | 781 / 783 | 781 / 783 | 781 / 783 | 781 / 783 | 772 / 773 | 772 / 775 |
| row_major_bl8 | 781 / 783 | 781 / 783 | 781 / 783 | 781 / 783 | 781 / 783 | 781 / 783 | 781 / 783 | 775 / 778 | 775 / 778 |
| col_major_bl8 | 465 / 570 | 465 / 570 | 465 / 570 | 465 / 570 | 465 / 570 | 465 / 570 | 465 / 570 | 416 / 520 | 416 / 520 |
| col_major_interleaved_bl4 | 780 / 781 | 781 / 782 | 757 / 768 | 780 / 782 | 781 / 782 | 780 / 782 | 781 / 782 | 617 / 615 | 615 / 619 |
| col_major_interleaved_bl8 | 781 / 782 | 781 / 782 | 780 / 782 | 781 / 782 | 781 / 782 | 780 / 780 | 781 / 782 | 684 / 686 | 688 / 688 |
| col_major_interleaved_bl16 | 781 / 783 | 781 / 783 | 780 / 782 | 781 / 783 | 781 / 783 | 741 / 743 | 781 / 783 | 721 / 729 | 729 / 730 |
| row_thrash_bl8 | 779 / 743 | 781 / 782 | 780 / 782 | 780 / 782 | 781 / 782 | 779 / 779 | 781 / 782 | 688 / 688 | 688 / 688 |
| random_bl8 | 767 / 760 | 774 / 772 | 769 / 772 | 775 / 780 | 709 / 746 | 701 / 734 | 709 / 746 | 628 / 657 | 635 / 661 |
| mixed_bl8 | 337 / 337 | **360 / 360** | 312 / 312 | 320 / 320 | 295 / 295 | 268 / 268 | 271 / 271 | 251 / 283 | 263 / 330 |

Read row hits / misses / conflicts:

| scenario | open32 | open32_rowhit | open32_bankrr | open32_bankrr_col |
|---|---|---|---|---|
| row_thrash_bl8 | 688752 / 207255 / 127993 | 891082 / 5149 / 127769 | 891083 / 5147 / 127770 | 891032 / 5110 / 127858 |
| random_bl8 | 763885 / 148054 / 112061 | 901406 / 10607 / 111987 | 900782 / 10591 / 112627 | 900966 / 10464 / 112570 |
| mixed_bl8 | 707257 / 147206 / 169537 | 856388 / 5854 / 161758 | 844150 / 1962 / 177888 | 846179 / 2211 / 175610 |

- Single-direction streams: per-bank FIFOs with the rotor are within 1 MB/s of the
  pooled queue everywhere once a ready column beats a ready row (`_col`); the plain
  rotor loses 3 percent on `col_major_interleaved_bl4` (it issues a bank's PRE
  while another bank's column waits).
- `row_thrash` and `random` reads: the pooled FR-FCFS (arrival-order tie-break) is
  the WORST policy here, 743 / 760, because it preempts a bank's open row with a
  ready miss elsewhere -- 207k misses where the other three take 5k. Both the
  row-hit-first pooled queue and the per-bank FIFOs reach 782 / 772-780. The
  2026-11-11 compare used `open32` as the ideal; on these two families the ideal is
  `open32_rowhit`, 782, not 743, and granite's lane result (775 reads) is 1 percent
  under it, not 4 percent over it.
- `mixed`: the pooled row-hit-first queue is the best policy, 360; strict per-bank
  FIFOs give 320 with the column preference (-11 percent) and 312 without; at
  8-deep queues 271 vs 295 (-8 percent). The FIFO head blocks: a row conflict at a
  bank's head holds the hits queued behind it (177k conflicts vs 162k). Granite's
  store has TWO heads per bank (`HEAD2_EN`, the second record peeks past the
  first), so the RTL sits between these two columns; the model's strict FIFO is a
  lower bound on it. **Filed as memory-controllers MC-016** (P3): model the two-head
  store, then decide whether a cross-bank row-hit-first pick is worth its logic on
  `mixed` -- the only family where the queue shape costs more than a few percent.

## Item 5: the trace from the cocotb side -- the rebuilt streams are confirmed exactly, except `mixed`

`perf_axi_trace.py` (ddr2_char_framework tests) writes the controller's accepted
AXI request stream as a `TimedLoadStoreTrace` per measured pass, off the
controller's own AXI slave port, one line per beat (`PERF_AXI_TRACE=<dir>` on the
granite perf proxy); `char_model.py run-trace` replays it. Sim at the sku100 point,
lane off, TEST_TXN 1024 per injector (the probe is passive: the sim's own cells are
the 2026-11-12 ones to the MB/s):

| scenario | sim granite (lane off) | model on captured: open32 | rebuilt: open32 | captured: open32_mc2 | rebuilt: open32_mc2 | captured: bankrr_col | rebuilt: bankrr_col |
|---|---|---|---|---|---|---|---|
| col_major_interleaved_bl8 | 681 / 686 | 782 / 783 | 782 / 783 | 781 / 782 | 781 / 782 | 782 / 783 | 782 / 783 |
| row_thrash_bl8 | 684 / 687 | 780 / 744 | 780 / 744 | 779 / 781 | 779 / 781 | 780 / 782 | 780 / 782 |
| random_bl8 | 626 / 656 | 766 / 758 | 765 / 758 | 769 / 771 | 768 / 771 | 776 / 780 | 772 / 779 |
| mixed_bl8 | 262 / 331 | **363 / 363** | 337 / 337 | 370 / 370 | 327 / 327 | 342 / 342 | 318 / 318 |

- `col_ilv_wr`: 8192 ST beats in 1024 bursts, accepted over 9560 cycles; `_rd` 8192 LD over 9515
- `row_thrash`: 32768 beats per direction in 4096 bursts, accepted over 38275 (wr) / 38125 (rd) cycles
- `random`: 32768 per direction, 41844 (wr) / 39949 (rd) cycles
- `mixed`: 32768 ST + 32768 LD in 8192 bursts, accepted over 100090 cycles

- The three single-direction streams replay to the same MB/s as the rebuilt ones
  under every policy (random within 4 MB/s, its LFSR a stand-in by design). MC-012's
  stride-table rebuild is confirmed by the controller's own port.
- `mixed` does not match: the captured stream is 8 percent better for every policy.
  The rebuilt trace alternates write and read BEATS; the port accepts whole bursts
  (eight write beats on W, a read burst on AR) and the two channels run in parallel,
  so the accepted order is burst-grained and the model's one-request-per-tick
  frontend sees fewer direction switches. The MC-012 statement "mixed: the 2 CK
  column reproduces granite to 2 MB/s" was on the rebuilt stream; on the captured
  one the 2 CK model is 370 against granite's 331 reads / 262 writes, a 10 percent
  scheduling gap on `mixed` after all. For `mixed` use the captured trace from now
  on; the single-direction families may keep the rebuild.

## Method and recipe

Overlay rebuild after the scheduler (`fetch.sh` from scratch, or in place:
copy `overlay/src/.../bank_fifo_rr.cpp` into the clone, apply the CMake hunk of
`vendor-registration.patch`, `make -j` in `vendor/ramulator2/build`; the build's
codegen step writes `python/ramulator/scheduler/bank_fiforr.py`). Then, with
`env_python` sourced and `PYTHONPATH=vendor/ramulator2/python`:

    M=projects/components/mem-ctrl-ip/references/ramulator2/bin/char_model.py
    for c in open32_wm03_97 open32_scatter open32_refburst8 open32_rowhit open32_bankrr_col ...; do
      python3 $M run --config $c --suite all --out <char_results>/model_ramulator2_ddr2_${c}_2026-11-12.csv; done
    # captured traces: granite perf proxy at the sku100 point with PERF_AXI_TRACE=<dir>
    TEST_FPGA_CLK_HZ=100000000 TEST_T_PHY_WRLAT=1 TEST_TREFI=772 TEST_TXN=1024 TEST_LEVEL=FUNC \
      TEST_DUAL=0 TEST_FAMILIES=row_thrash TEST_NUM_GEN=4 PERF_AXI_TRACE=<dir> \
      python3 -m pytest test_granite_char_perf.py::test_granite_char_perf
    python3 $M run-trace --config open32 --name row_thrash_bl8 --wr <dir>/row_thrash_wr.trace --rd <dir>/row_thrash_rd.trace --out <csv>
    python3 $M run --config open32 --suite all --only row_thrash_bl8 --txn 1024 --out <csv>   # the rebuilt stream at the sim's count

Each model configuration runs the full suite in about 30 s.
