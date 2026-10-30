# TASK-003 — granite at 100 MHz, and ahead of LiteDRAM through the same harness

**State:** active (opened 2026-10-26, owner's direction: "I want granite to
converge at 100 MHz and kick LiteDRAM's ass performance wise").
**Depends on:** TASK-002 (age-FIFO store, landed 3a1479820).

## The two halves, measured before anything was changed

### Timing: the current design at 100 MHz (GRANITE_SYS_100=1, 2026-10-26)

| build | WNS | failing endpoints | of which granite_core |
|---|---|---|---|
| 17-18 Oct pushes (old entry store + old scheduler), best of seven | -0.730 ns | 1,333 | nearly all |
| current design (age-FIFO store, bank pick), first try | **-0.686 ns** | **953** | **132** (store 103, scheduler plane 29) |

The harness owns 821 of the 953: the char engines' address generators
(585), the DFI monitor RAM's AXI-Lite read path (143), the chargen register
block and shim (52), the W skid (18). It has to close at 100 MHz before the
board can measure anything there; that is a char-framework item, not granite.

Inside granite the 132 failures are two cones:

1. **Push cone** (100 endpoints, worst -0.511 ns, 14 levels, 73 percent
   route): the write intake's AW meta FIFO is a mux-read `gaxi_fifo_sync`,
   so the push's bank index is combinational from the FIFO's read pointer and
   the store does the free-slot find, the per-bank count compare, the bank
   cap and the queue write in the same cycle. Fix: a registered push at the
   plane edge (REGISTERED=1 on that FIFO, exposed as a plane parameter
   because the intake is shared with pumice, or a staging register in the
   store's admission). One cycle of write latency, no throughput change.
2. **Fire cone** (32 endpoints, worst -0.569 ns, 11-13 levels): the hold mux
   selects the effective winner, the fire stage muxes its record out of 16
   and runs the class / timer / block checks, and the fire fans into the
   pick's registers, the page policy's per-bank state (the "bank_timers ->
   page_policy" class is this same cone: the policy is fed by the fire) and
   the store's pops. Fix: compute class_ok / timer_ok / blocked per pair in
   stage 1 (16 pairs x 3 classes, all inputs are registers or ports) and let
   the winner select one precomputed bit; the wide record mux leaves the
   critical path. No policy change.

The 75 MHz routed build's own census (report_timing -cell u_core, 400 worst
unique endpoints) had every one above 10 ns with the hold bit at the root of
the twelve worst; the 100 MHz constraint already pulled most of that in.

### Performance: current design on the board at 75 MHz (2026-10-26)

Same harness, same operating point as the LiteDRAM A/B (75 MHz, 1:2, 300
MT/s DDR2, peak 600 MB/s). CSVs: `char_results/char_granite_agefifo75_*_2026-10-26.csv`.

| MB/s, peak 600 | LiteDRAM | pumice | granite 15 Oct | granite 26 Oct |
|---|---|---|---|---|
| col_major BL8 wr / rd (page thrash) | 304 / 386 | 193 / 195 | 188 / 205 | **292 / 333** |
| concurrent 1w+1r, incremental, combined | 248 | 553 | - | **54** |
| concurrent 1w+1r, row_major, combined | 286 | 571 | - | **45** |
| concurrent 1w+1r, col_major, combined | - | - | - | 213 |
| multigen 1w+2r, incremental, combined | - | - | - | 113 |
| multigen 1w+2r, row_major, combined | 316 | 570 | - | 68 |
| open_page streams BL8 wr / rd: incremental | 569 / 575 | 555 / 562 | 286 / 277 | **576 / 578** |
| open_page streams BL8 wr / rd: row_major | 582 / 580 | 570 / 572 | 290 / 291 | **578 / 580** |
| open_page col_major_interleaved BL8 wr / rd | 298 / 366 | 236 / 262 | 207 / 200 | **512 / 514** |
| read latency, open_page stream, cycles | 42 | 49 | 96 | 50 |

The `close_page` preset on granite reads 58-75 MB/s at 192 cycles latency on
every family (the preset maps to a static-close mode granite serves with a
separate PRE per burst); not the product point, noted, not chased here.

Read latency under 1w+1r: 634 to 768 cycles. The page-thrash case has
caught up (within 4 percent of LiteDRAM on writes, 14 on reads); the mixed
case is a collapse, and the simulated `mixed` family (pairs of threads on
one bank one row apart) shows the same thing at 106 MB/s combined.

**Mechanism** (read from the select order in `mc_bank_pick`): the class
alternation "after a column prefer a row command" sits above the direction
register. With a writer streaming row A and a reader waiting on row B in the
same bank, every write column is followed by the reader's PRE (a row
command, preferred), its ACT, its column (direction flips), then the
writer's PRE / ACT / column: one full tRC per burst, 44 cycles each, which
is exactly 1,410,331 cycles for 16,000 bursts.

## What this task changes (in order)

1. **Direction stickiness + the hold yield in the pick's select** (done
   2026-10-26, measured on the board): (a) a column of the other direction
   is taken only when the current direction has no column pending, where
   "pending" is the registered request with its sink open, the stale masks
   NOT applied, plus a one-cycle flop per direction carrying the fired
   candidate's behind_same_row across the decode gap; the direction register's
   runs-dry test uses the same term; the read-only batch cap (16) releases
   it; (b) a held cross-direction column waiting on the turnaround timer
   yields when the current direction has a column pending again. Two flops
   and a few gates, no new policy inputs. The row gate tried first
   (defer the idle direction's row command while its sibling pair streams)
   was measured cycle-identical on every family once (b) was in and was
   dropped.
2. Push cone: registered push at the AXI plane edge.
3. Fire cone: per-pair precompute of the fire checks.
4. Harness at 100 MHz (char framework; separate owner).
5. Within-class age tie-break, then CSR weights on the select (the
   cost-function form the owner asked about), tuned on the board. This
   absorbs TASK-002's residual (closed 2026-10-29): the age-FIFO store
   exposes the oldest-in-pool bit per head; thresh at the TOP of the
   select was measured and rejected (mixed halves, stream reads -10
   percent at 8 threads), so `HAS_AGE` stays 0 until the within-class
   placement is measured. The owner's call on the pick core.
6. DFI 1:4 at 100 MHz with BL8: LiteDRAM's stock Nexys point is 100 MHz
   1:4 (800 MT/s, 1.6 GB/s peak); at 1:4 a BL4 burst is half a cycle and
   one command per cycle caps at 50 percent, so the 1:4 product point is BL8.

## Results log

- **2026-10-26, row gate (step 1) measured and NOT the mechanism.** Board,
  gated bitstream (75 MHz, WNS +0.445 ns, 0 failing): concurrent incremental
  27.2 -> 31.9 MB/s a side, every other concurrent / multigen / stream cell
  identical to 0.1 MB/s; sim 1- and 8-thread proxies cycle-identical to the
  ungated build on every family; granite FUNC 6 passed / 1 xfail, common-ip
  30 passed / 3 xfail. The row_major concurrent cell (the worst, 22.5 a side,
  768-cycle read latency) has its writer and reader in DIFFERENT banks
  (regions of one page each), so no row conflict exists there at all. The
  gate stays in for now (sound, +17 percent on the one cell it touches) but
  the collapse is a per-burst direction flip with a large fixed cost.
- **2026-10-26, the board's cell reproduced in simulation.** New proxy
  families `conc_rows` (adjacent regions: same banks, different rows) and
  `conc_banks` (next bank, same row), one writer + one reader from one GO
  (`perf_mixed_family.measure_conc`, hooked into `test_granite_char_perf`):

  | 1w+1r, MB/s a side | board (gate) | sim proxy (gate) |
  |---|---|---|
  | same banks, different rows (conc_rows / incremental) | 31.9 / 31.9 | 34.5 / 33.7 |
  | next bank, same row (conc_banks / row_major) | 22.5 / 22.5 | 21.5 / 21.5 |

  `conc_banks` is 111 cycles per write+read pair in sim (57,131 cycles for
  2 x 256 bursts) while either stream alone is one column per cycle. tRTW is
  6 and tWTR 4 on granite (CSR defaults), so a flip per burst explains at
  most 12 of those 111 cycles: the rest is the thing to trace (VCD of the
  pick's decisions, `pick_trace.py`).
- **2026-10-26, the trace, and two sticky-direction passes.** VCD of the
  pick in `conc_banks` (24 bursts): in the concurrent phase every write
  column is followed by a read column 5 cycles later (tWTR+1) and the next
  write column 22 cycles after that (the PHY-floor tRTW): one direction flip
  per column, 216 cycles per 8-column burst. The sequence at the flip (cycle
  63342 write fires; 63343 req = the read pair alone, because decode lags the
  fire by a cycle and the writer's next entry is not yet visible; the read is
  picked and HELD through tWTR while the writer's column is back from 63344;
  63347 read fires, r_dir flips; the writer's column is then held through
  tRTW). Pass 1 (hold the direction while r_req shows pending columns, gate
  the fall-through and the runs-dry test, release at the batch cap 16):
  conc_banks unchanged at 21.5, conc_rows 34.5 -> 39.1, 2-thread mixed 67 ->
  332 combined, 8-thread proxies cycle-identical, board build +0.440 ns.
  Pass 2 (register the fired candidate's behind_same_row per direction for
  the decode gap): proxy unchanged; board (build +0.390 ns, 0 failing):
  concurrent incremental 27 -> 41 a side, row_major still 22.5, multigen and
  every stream cell unchanged. So the pending test still misses the cycle:
  the fired candidate has NO same-row entry behind it when the writer's next
  burst has not been pushed yet, the read is picked legitimately, and the
  HOLD then keeps it through the timer while the writer's column arrives.
  Pass 3 (running): a held cross-direction column waiting on the turnaround
  yields when the current direction has a column pending again.
- **Pass 3, the hold, IS the mechanism (proxy, 2026-10-26).** A held
  cross-direction column waiting on the turnaround timer now yields when
  the current direction has a column pending again (`w_win_xdir_col` drops
  `w_hold_next`; the select re-runs and takes the current direction's
  column). The proxy, 1w+1r from one GO, MB/s combined, peak 600:

  | proxy, 2 threads | before | pass 1+2 | pass 3 (hold) | pass 3 at N=32 |
  |---|---|---|---|---|
  | conc_banks (next bank, same row) | 43.0 | 43.0 | **571.6** | 571.6 |
  | conc_rows (same banks, different rows) | 67.4 | 75.7 | **556.0** | 557.9 |
  | mixed (pairs one row apart, both directions) | - | 332.0 | 332.0 | 332.0 |
  | incremental, single direction | 568 / 570 | same | same | same |

  pumice's board number for the same cell is 571; LiteDRAM's 286. The
  pool-depth worry written above was wrong: N=32 changes nothing, because a
  direction keeps the bus while its columns keep coming and the host refills
  the eight slots faster than the columns drain them. The 2-thread `mixed`
  family stays at 332: that one is a within-bank reorder (two rows of one
  direction interleaved in an in-order bank queue), which the FIFO store
  does not do by design.
- **Pass 3 on the board (2026-10-26, build WNS +0.259 ns, 0 failing;
  CSVs `char_granite_agefifo75hold_*_2026-10-26.csv`).** MB/s, peak 600:

  | 75 MHz, same harness | LiteDRAM | pumice | granite before | granite + hold |
  |---|---|---|---|---|
  | concurrent 1w+1r incremental, combined | 248 | 553 | 54 | **568** |
  | concurrent 1w+1r row_major, combined | 286 | 571 | 45 | **576** |
  | concurrent 1w+1r col_major_interleaved, combined | - | - | 98 | **393** |
  | concurrent 1w+1r col_major, combined | - | - | 213 | 213 |
  | multigen 1w+2r incremental, combined | - | - | 113 | **385** |
  | multigen 1w+2r row_major, combined | 316 | 570 | 68 | **509** |
  | read latency under 1w+1r row_major, cycles | - | - | 768 | **79** |
  | open_page streams, all four families | - | - | unchanged | unchanged (to 0.1) |

  Zero mismatches in every cell. Mixed traffic went from a tenth of
  LiteDRAM to twice it, level with pumice on the two page-friendly cells;
  the remaining gap to pumice is multigen (1w+2r, 509 vs 570) and the
  thrash cells, which are page-policy and within-bank-order questions, not
  the direction logic.
- **Row-gate attribution and the final RTL (2026-10-26).** With the hold
  yield in, removing the row gate is cycle-identical on all nine proxy
  families at 2 and 8 threads (conc_rows 556.0, conc_banks 571.6, mixed
  332.0 / 365.5, streams unchanged), so it is dropped: the final pick change
  is the sticky direction plus the hold yield, 53 lines in, 4 out. Final
  RTL: lint clean at HAS_AGE 0 and 1, granite FUNC 6 passed / 1 xfail,
  common-ip 30 passed / 3 xfail, both on clean builds. Final 75 MHz board
  build of this exact RTL: WNS +0.299 ns, 0 failing; board run
  (`char_granite_agefifo75final_*_2026-10-26.csv`) within noise of the
  hold-fix run on every cell (1w+1r incremental 568, row_major 576,
  col_major_interleaved 402 combined; 1w+2r row_major 516; streams
  unchanged; zero mismatches).
- **2026-10-27, 100 MHz build of the final RTL (sticky direction + hold
  yield, ring merge inputs tied off): does NOT close.** `GRANITE_SYS_100=1`,
  reports kept at `targets/granite/fpga/reports_sys100_2026-10-27/`
  (bitstream not kept; it fails timing). WNS **-0.753 ns**, TNS -275 ns,
  **756** failing endpoints of 106,478; hold and pulse width clean; 40,356
  LUT (64 percent). Census by endpoint owner:

  | owner | failing endpoints | worst | what |
  |---|---|---|---|
  | harness | 654 | -0.753 | char engines' address generators (LFSR -> `r_s1_offset`, 32 per generator x 16 generators), chargen shim cpuif (31), rd engines, AW/W channels, meters, CSR |
  | granite_core | 102 | -0.728 | below |
  | - bank pick | 18 | -0.728 | `r_spec_taken` -> `r_pick_cls` / `r_stale_pick`, 11 levels: the fire cone, now through the hold-yield select |
  | - page policy / bank timers | 8 (+12 global timers) | -0.706 | `r_row_valid` -> `r_keep_open`, 14-15 levels: the fire fans into the policy's per-bank state (same cone) |
  | - DFI plane CDC | 24 | small | `rd_fire_o` -> read-return async FIFO RAM write enables |
  | - FIFO store | 40 | -0.346 | push cone: AW meta FIFO read pointer -> per-bank queue `wr_full` / `rd_empty`, 12 levels (the mux-read push, as described above) |

  Against the 2026-10-26 build of the pre-hold RTL (-0.686 ns, 953 / 132):
  the harness count fell 821 -> 654 and the core 132 -> 102 (the store's push
  cone 103 -> 40), but the fire cone got 0.16 ns deeper because the hold
  yield adds a term to the winner select. Owner, same day: "the levels are
  fine; it's the routing that's killing us" -- measured: the worst path is
  1.8 ns of LUT and 8.8 ns of wire (83 percent), the 102 core paths average
  2.5 / 7.3 ns (74 percent); the first hop off `r_spec_taken` (24 loads)
  is 1.2 ns, the AW meta FIFO address net (45 loads) 1.3 ns, and the pick
  is placed across twelve slice rows. Any fix is a fanout / placement fix
  (replicate the high-fanout control bits, pblock the pick and the store,
  get the harness off the fabric the core needs), not a depth fix. The two core fixes listed under
  "Steps" (registered push at the plane edge; per-pair precompute of the fire
  checks) are still the ones; the harness (654) has to close on its own
  before a 100 MHz board number exists.
- **2026-10-27, flow-only fixes at 100 MHz: none converge.** Three parallel
  builds of the same RTL from scratch copies of the flow (reports under the
  session scratchpad `g100_fo` / `g100_eto` / `g100_end`; the flow already
  runs AltSpreadLogic_high + AggressiveExplore phys_opt + Explore route +
  post-route phys_opt, and the XDC records four pblock attempts on this cone
  that all backfired):

  | build | WNS | failing | core / harness | worst core path |
  |---|---|---|---|---|
  | baseline (AltSpreadLogic_high) | -0.753 | 756 | 102 / 654 | pick `r_spec_taken` -> `r_pick_cls`, 8.8 ns wire |
  | MAX_FANOUT 6-12 on `r_spec_taken`, `r_req`, AW meta FIFO pointer, `r_last_row`, `r_row_valid` | -0.712 | 811 | 176 / 635 | CSR field -> `r_keep_open` -0.683; the same pick cone now from `r_stale_pick` -0.612; push cone WORSE (-0.580, 15 levels) because the replicated pointer copies spread the RAM address |
  | PLACE_DESIGN ExtraTimingOpt | -0.650 | 900 | 263 / 637 | pick `r_req` -> `r_stale_pick` -0.620; push cone -0.608 |
  | PLACE_DESIGN ExtraNetDelay_high | -0.692 | 1041 | 261 / 780 | same cones |

  Replicating a register takes its name off the worst path and the next
  input to the same cone takes its place at the same depth of wire; the
  placer directives buy 0.1 ns on the worst path and triple the core's
  failing count. The wire per hop on this part at this fill is 0.6-0.8 ns,
  so a cycle at 100 MHz affords about nine hops after clock-to-Q and setup;
  the fire cone has 11-15 and the push cone 12-15. Nothing in the flow
  changes that: what is left is fewer hops per cycle (a register in the
  cone, which halves the wire per cycle as well as the LUTs), less fanout
  spread (a narrower fire cone), or a less full part (the harness's sixteen
  address generators share the fabric and own 635-780 of the failures).
- **2026-10-27 (evening), RTL fixes at 100 MHz: three cones out, the pick
  cone stays; best WNS -0.583 ns, not closed.** Owner-approved edits to the
  shared common-ip blocks, every one behaviour-preserving on the published
  outputs, all gates green (granite full 8/8 + 1 marked xfail; the
  store/arbiter contract test on both cores and both stores 12/12 + the 3
  strict FR-FCFS xfails; `formal/mc_common/mc_global_timers` PASS; pumice
  top func 218/218). Reports kept beside the morning's as
  `targets/granite/fpga/reports_sys100_2026-10-27_rtl_*`.

  | change | block | what it does | its cone at 100 MHz |
  |---|---|---|---|
  | B. admission hold | `mc_bank_fifo_store` | AW / AR push lands in a one-entry register, admitted from it a cycle later (ready = empty or draining, registers only); pops decode by comparing the fired slot with each queue's live head instead of `r_*_bank[slot]`; the same-row bit no longer carries the same-cycle pop term (read at positions 1-2 only). +1 cycle AXI handshake -> record | push cone (-0.346, 40) GONE |
  | C. `PRED_CMD_REG` | `mc_page_policy` (+ one parameter line in `mc_scheduler_plane`, BANK_PICK only) | the mistake predictor and the telemetry read the issued command through a register; the idle timers and the close request keep the live stream | `r_keep_open` (-0.706, 8) GONE |
  | D. registered tFAW pick | `mc_global_timers` | the claimed slot is a register; two argmins run from the slot registers (all four / all but the current pick) and the ACT only selects. Published windows identical (every output is a function of the slot VALUES) | tFAW slots (-0.241, 12) GONE; the register's own D path is -0.270, 1 endpoint |
  | A. pick select rewrite | `mc_bank_pick` | one find-first-set carry chain over {sel, sel_above}; pair index and class as AND-OR of the one-hot; speculation/pick stale masks resolved at the load | NO GAIN: still 11 LUT hops (class vectors -> OR-reduce -> select -> mask -> chain -> fold -> class), WNS -0.907 with it. REVERTED |

  | build (same harness, 64 % LUT) | WNS | failing | core / harness | worst core path |
  |---|---|---|---|---|
  | morning baseline | -0.753 | 756 | 102 / 654 | pick `r_spec_taken` -> `r_pick_cls`, 11 LUT, 8.8 ns wire |
  | A + B + C + D | -0.907 | 858 | 115 / 743 | pick `r_cls` -> `r_pick_cls`, 11 LUT, 7.6 ns wire + 3.2 ns logic; fire cone -> timers / idle-timer CE / store RAM -0.47..-0.13 (84 % route) |
  | B + C + D (in the tree now) | -0.583 | 766 | 72 / 694 | pick `r_stale_spec` -> `r_stale_pick` -0.583 (13); fire cone -> policy idle-timer CE -0.376 (25); fire cone -> store flags -0.40 (2); timers CE -0.24..-0.02 |

  Mean failing core path: baseline 2.5 ns LUT / 7.3 ns wire (74 %), B+C+D
  2.0 / 7.8 (79 %). The 0.17 ns of WNS gained is the three cones; the pick's
  arbiter cone is the floor and it is 11 hops however the select is
  written (A proved that: the encoder and the class lookup it replaced were
  not the serial depth, the class-vector OR-reductions and the priority
  select are). Eleven hops at 0.7 ns of wire each do not fit 10 ns on this
  part at this fill. What would: a pipeline split of the pick (register the
  class vectors and the any-flags, LA = 3, with the bank timers' lookahead,
  the hint eligibility and the speculation retuned -- a redesign of the
  pick's timing contract, not an edit), or a less full fabric. Owner's
  call; B, C, D stay in the tree uncommitted as measured, behaviour-preserving
  improvements.

### 2026-10-28, the harness's address generators pipelined: WNS -0.234 ns, 67 failing, 11 core

The 694 harness endpoints of the -0.583 build split by class: 490 were the
eight injector engines' `dma_address_gen` first stage (the LFSR / counter
mux, the idx1_shift split and the lo mask, then an unregistered DSP48
multiply and the wrap mask, 6 LUT levels + 3.7 ns of DSP, 10.5 ns in one
clock), 80 the read engines' beats-mismatched compare into a clock enable,
the rest APB readback and skid pointers. Fix: `dma_address_gen` gained
`INPUT_REG` (default 0, a flop on the request before the multiplier,
latency 2 -> 3, throughput unchanged); `axi4_master_wr_injector` and
`axi4_master_rd_crc_check` build all four generators with it set. STREAM's
`stream_run_addr_gen` and amber's injector keep the default.

| build (100 MHz, same harness) | WNS | failing | core | harness |
|---|---|---|---|---|
| store hold + policy register + timers (2026-10-27 evening) | -0.583 | 766 | 72 | 694 |
| + address generators with INPUT_REG | -0.234 | 67 | 11 | 56 |

The address-generator class is gone (0 endpoints). What is left: the pick's
`r_stale_pick` -> `r_stale_pick` / `r_pick_cls` cone (11 endpoints, 30 %
logic, 7.0 ns of route on the worst), the read engines' beats-mismatched
clock enable (44, 15-19 levels, -0.191) and the chargen shim's APB readback
mux off the FIFO pointer gray counter (12, -0.187). LUTs 39,873 (62.9 %).
Reports: `targets/granite/fpga/reports_sys100_2026-10-28_addr_gen_reg/`.

Gates: `dma_address_gen` unit test now runs INPUT_REG 0 and 1 on both
widths; `val/amba` write injector 147, read checker 168, pair 12 passed.
One test fix: `gap_no_aw_ahead` stopped sampling at the sixth wlast and so
missed a sixth AW that the slave accepted 20 cycles later (AXI lets W data
reach the port before its AW; the check is AW-not-ahead-of-W, which held);
it now waits for both counts.

The misc area suite (12) and the ddr2_char_framework suite (222 passed, 2
pre-marked xfail, 31 min) also passed on that tree.

### 2026-10-28 pm, the last two harness classes registered: WNS -0.114 ns, 7 failing, all in the core

Both remaining harness classes were one register each, same shape as the
morning's:

- The read engines recomputed each beat's byte address as
  `base + (r_beats_in_burst << r_axi_size)` on every beat, and that adder
  was the front of the beat counter -> hash -> 64-bit compare ->
  `o_beats_mismatched` cone (18 levels, 9.9 ns, 44 endpoints).
  `axi4_master_rd_crc_check` now keeps the next beat's address in
  `r_beat_addr` (first beat at the generator's base, then plus one beat
  per handshake): the adder feeds a flop, the compare still happens on the
  R handshake, nothing moves by a cycle.
- The chargen shim's APB readback ran from the CDC command FIFO's RAM read
  through `peakrdl_to_cmdrsp`'s idle bypass, `chargen_regs`' decode and its
  readback mux into `r_rsp_prdata` in one cycle (9 levels, 8.6 ns of wire,
  12 endpoints). `peakrdl_to_cmdrsp` gained `INPUT_REG` (default 0: the
  bypass every other consumer builds; 1: every request issued from the
  registered command one cycle after acceptance, the cmd inputs never reach
  the register block); `apb4_to_peakrdl` sets it. One cycle per APB access,
  behind a CDC.

| build (100 MHz, same harness) | WNS | failing | core | harness | LUTs |
|---|---|---|---|---|---|
| + address generators with INPUT_REG (morning) | -0.234 | 67 | 11 | 56 | 39,873 |
| + beat address register, shim INPUT_REG | -0.114 | 7 | 7 | 0 | 36,578 |

The seven: the pick's `r_stale_fire` / `r_req` -> `r_stale_pick` /
`r_pick_cls` select (5, 11 levels, worst -0.114: 1.8 ns of logic, 8.2 ns
of route), bank timer `r_rp` -> the read ring's issue-queue `rd_empty`
(-0.030) and page policy `r_keep_open` -> bank timer `r_rc` (-0.025). The
harness has no failing endpoint left; what remains is the pick's wire,
the pblock / placement question above. Reports:
`targets/granite/fpga/reports_sys100_2026-10-28_harness_regs/`.

Gates: `val/amba` read checker 168 and pair 12 (full, parallel); the
converter grid now runs INPUT_REG 0 and 1 at every level (6 passed) and
`formal/converters/peakrdl_to_cmdrsp` proves at the default; the converters
area and ddr2_char_framework full suites (results in the commit). One test
fix on the way: the converter TB released reset and sent its first command
two cycles later, inside the block's three-stage reset synchronizer; the
command was taken by a reset-valued `cmd_ready` and dropped. INPUT_REG = 1
hung on it; INPUT_REG = 0 had passed only because the bypass presented the
dropped command and the response FSM acked it. The TB now waits the
synchronizer out.

### 2026-10-28 evening, the seven: placer sweep, the pick's tail, fanout, and the bank timers' loads

The seven failing endpoints are all route (11-12 levels, 1.8 ns of logic
against 8.2 ns of wire on the worst). Four levers tried in order, each on
one build, baseline directive `AltSpreadLogic_high` unless stated.

**Placer directive sweep (same RTL as the -0.114 build).** Not the lever:
the cone is placement-bound and the four directives land inside one
build's noise band, which is about half a nanosecond.

| directive | WNS | failing | worst class |
|---|---|---|---|
| AltSpreadLogic_high (the flow's default) | -0.114 | 7 | `r_req` -> `r_pick_cls`, 11 levels |
| ExtraTimingOpt | -0.228 | 8 | `r_hold` (134 loads) -> `r_pick_cls`, 11 levels |
| ExtraPostPlacementOpt | -0.227 | 8 | `r_stale_pick` -> `r_stale_pick` |
| Explore | -0.575 | 14 | `r_spec_taken` -> `r_stale_pick` |

**Trimming the pick's tail.** The full trim (stage-1 pre-decode of
`r_req_col` / `r_req_row` / per-direction "columns pending", AND the class
behind the encoder as an AND-OR over the one-hot winner instead of an index
mux) measured WORSE: -0.817, 26 failing, 13 levels to `r_pick_cls` through
the one-hot's carry chain against 11 through the mux, and phys_opt had split
`r_spec_taken` into three copies with a copy still on the worst path. The
one-hot class is reverted (comment in the RTL). The pre-decodes alone stay in
the text as the "reduced trim": lint clean, granite_core 2 passed, common-ip
fub + macro 34 passed / 3 xfail, granite top FUNC 6 passed / 1 xfail, and
the char perf proxy cycle-identical to the 11:43 baseline on all four
families (fixed seed 2882343476: incremental 2164 / 2157, row_major 2154 /
2141, col_ilv 2672 / 2717, col_major 3972 / 3464 wr / rd cycles, 0
mismatches). Its build is in the table below.

**Could replicating flops help ("the same info goes to disparate places")?**
Measured on the -0.114 routed checkpoint (pre phys_opt, so slacks sit about
0.2 ns under the final report): 89 paths within 0.3 ns of failing, grouped
45 page policy `r_keep_open` -> bank timer counters and idle timers, 14
bank timer `r_rp` -> idle timers, 12 the pick's own select, 4 timer -> ring
issue queue / command FIFO, 9 harness (all above +0.07). Register-driven
nets with 13 or more loads on those paths: only three in the core.

| flop | loads | first hop | on |
|---|---|---|---|
| pick `r_hold` | 134 | 0.69 ns | 6 pick paths, the worst in the set |
| pick `r_spec_taken` | 24 | 1.2 ns (earlier build) | 1 pick path |
| global timers `r_slot_pick` | 24 | n/a | 2 paths, both positive |

The wide nets on the 59 timer-cone paths are LUT outputs ten levels into
the fire cone: `evt_bank` 58 loads (1.05 ns), `set_act` 32 (1.1 ns), the
issue-queue valid 36 (0.75 ns), the pick's select intermediates 17-25.
Replicating those means duplicating the cone that drives them, which is
what phys_opt's `_comp` / `_repN` copies already are. The 2026-10-27 forced
MAX_FANOUT run (`r_spec_taken` 6, `r_req` 8, AW meta FIFO pointer 12) is the
same story: two paths left the worst list and 74 entered it. The start
flops of the seven have fanout 1-6; their 0.75-0.96 ns first hops are
distance. So: replication as a flow knob is worth exactly one build, on
`r_hold` (`MAX_FANOUT 32`, scratch XDC, baseline RTL), expected ceiling a
few hundred ps on the pick paths alone; replication as a DESIGN move is to
make the wide nets flops, which is the next item.

**The bank timers' loads come off a register (`mc_bank_timer` `SET_LAG`).**
The counter loads were 59 of the 89 cusp endpoints: every `r_rcd` / `r_ras`
/ `r_rc` / `r_rp` / `r_preblk` D input hung off `evt_* && (evt_bank == b)` at
the end of the fire cone. With `SET_LAG` each bank registers its four
`set_*` strobes and loads the counters one cycle later at (t - 2) instead
of (t - 1), saturating at 0; "safe at count == 0" still lands at C + t.
The readiness outputs stay EXACT: in the one cycle between the strobe and
the load, every counter read goes through an "effective" view that folds
the pending load in -- for tRCD / tRAS / tRC / tRP "zero" is masked by the
pending load (a 0- or 1-cycle value of those is no DRAM timing; the mask
keeps the zero-detect one LUT6), for preblk it is exact (`t_rtp <= 1` IS the
board value at some clocks), the lookahead twins use `t <= LA + 1` for a
pending load and the auto-precharge wait uses `t - 1`, and the self-close
`w_ap_fire` reads the same view. The row image (`r_row_valid`, `r_open_row`,
the AP bit) stays on the LIVE strobe, so the decode, the page policy and the
refresh drain see the command when they always did; nothing observable
moves by a cycle. `mc_bank_timers` `EVT_REG` -> the plane's `BANK_EVT_REG`,
default `SCHED_CORE == BANK_PICK` (the FR-FCFS core and pumice unchanged);
`granite_core` / `granite_top_geared` carry `BANK_EVT_REG` (default 1) and
the top tests read `GRANITE_BANK_EVT_REG` so the OFF state runs on the same
bench. `mc_global_timers` stays on the live events (its registered-ok form
already folds the event at the D input; its paths were positive).

Lint clean at SET_LAG 0 and 1 (leaf, wrapper, plane with both cores,
granite_core at BANK_EVT_REG 0 and 1, geared top, pumice_core: only the
pre-existing warnings). granite_core func: ON 2 passed, OFF 2 passed.
Full gates and the three builds (reduced trim; `r_hold` MAX_FANOUT on the
baseline text; reduced trim + SET_LAG) below as they land.

| build (100 MHz, AltSpreadLogic_high) | WNS | failing | core | worst class | levels |
|---|---|---|---|---|---|
| baseline (reports_sys100_2026-10-28_harness_regs) | -0.114 | 7 | 7 | `r_req` -> `r_pick_cls` | 11-12 |
| reduced trim (pre-decoded request flops) | -0.219 | 20 | 20 | `r_spec_taken_replica` -> `r_stale_pick` (7), `r_stale_fire` -> `r_pick_cls` (2), `wr_head2_o[vld]` -> timer CE (6), `r_pre_rdy` -> ring issue-q / cmd FIFO flags (4) | 11-13 |
| baseline + `r_hold` MAX_FANOUT 32 (scratch XDC) | -0.297 | 34 | 34 | `r_stale_win` -> `r_pick_cls` (2), `wr_head_o[vld]` -> page policy `r_idle` CE (16), `r_hold_rep__1` -> `r_stale_pick` (6, the replica still on the path), `policy_mode` -> `r_idle` (8) | 9-14 |
| reduced trim + bank timer SET_LAG | -0.014 | 2 | 2 | `r_stale_pick` -> `r_stale_pick` (1), `r_spec_taken` -> `r_pick_cls` (1, -0.001); no timer, ring or page-policy endpoint left | 11, 13 |
| baseline pick + bank timer SET_LAG | +0.004 | 0 of 107,847 | 0 | (hold +0.025) | -- |

The bank timers' loads were the lever: with the counters off the fire cone
the placer no longer has to pull sixteen banks' worth of counters toward the
pick, and the pick's own select closes with them (0 failing, 36,681 LUTs,
+103 over the baseline). The reduced trim of the pick is REVERTED: on its own
it measured -0.219 / 20 (noise against -0.114 / 7, no level gain), and with
SET_LAG it left two pick endpoints at -0.014 where the untrimmed pick leaves
none. The committed text is the baseline pick + `SET_LAG`; reports kept as
`targets/granite/fpga/reports_sys100_2026-10-28_timer_set_lag/`.

### 2026-10-29, does the close hold: a repeat and a perturbed placer

Two more builds of the committed text (b8665155e), nothing changed in the
tree. The first is the same build again (default filelist, default
directives) to see what build-to-build noise does to a +0.004 close. The
answer is that there is no such noise on an identical netlist: Vivado
2025.1 is deterministic, and the repeat reproduced the closing build line
for line (WNS +0.004, 0 of 107,847, 36,681 LUTs, hold +0.025; the only
report lines that differ are the date stamps). The ~0.5 ns spread this log
has been calling noise is the spread between different netlists, not
between runs of the same one. So a repeat says the close is reproducible;
it says nothing about margin.

The second build changes the placer directive to ExtraTimingOpt, keeping
everything else, as a margin probe:

| build (100 MHz, committed b8665155e) | WNS | failing | core | worst class | levels |
|---|---|---|---|---|---|
| repeat, AltSpreadLogic_high (default) | +0.004 | 0 of 107,847 | 0 | identical to the closing build | -- |
| PLACE_DIRECTIVE=ExtraTimingOpt | -0.072 | 4 | 4 | `r_stale_pick[9]` -> `r_stale_pick[11,13]` (2), `r_spec_taken` -> `r_pick_cls[0,1]` (2); 36,679 LUTs, hold +0.014 | 11-14 |

The margin is thin, as the +0.004 said. Under the other placer the four
endpoints that miss are all in the pick's own select, the same
`r_stale_pick` / `r_spec_taken` -> `r_pick_cls` pair that the trimmed-pick
build left at -0.014, and the worst path is 71% route (9.975 ns data path,
2.855 logic, 7.120 route). No timer, ring, harness or page-policy endpoint
appears in either build: the SET_LAG change is holding; what is left is the
pick's select at 11-14 levels, which the directive sweep already showed
cannot be placed away. The default directive remains the one the flow
ships, and its bitstream closes. The design moves that would buy real
margin are the ones recorded above as not mine to take alone: the LA=3
pick pipeline split, or a scheduler-plane pblock.

### 2026-10-29, the 100 MHz bitstream on the board: not a board point

The closing bitstream (repeat build of b8665155e, WNS +0.004) programmed
and ran init, but read leveling found no (bitslip, tap) eye at all and the
write_read smoke mismatched every beat (512 of 512; memtest not reached).
The clock plan is the cause, not the controller: `GRANITE_SYS_100` keeps
sys2x at 150 MHz (DDR2-300) under a 100 MHz sys, a 3:2 ratio, and the
LiteDRAM a7ddrphy serializers run with `CLKDIV = sys_clk, CLK = sys2x_clk`
(OSERDESE2 DDR, width 4), which requires sys2x to be exactly 2x sys and
phase-locked. The 75 MHz plan has that (150 = 2 x 75); the 100 MHz plan
does not, so the PHY cannot capture anything. The pumice harness already
says this of its own 100 MHz profile ("a timing build, not a board point:
no DDR2 calibration tuple exists for it") and pairs 100 MHz with a 200 MHz
sys2x (DDR2-400, VCO 800).

So the 100 MHz close is a controller-timing result; a board number at
100 MHz sys needs the DDR2-400 clock plan (sys2x 200 MHz, idelay /4), a
build that closes the PHY and DFI-adapter paths at 5 ns, a DDR2-400 init
(CL3 at 200 MHz is legal for the MT47H64M16HR-25E; the host's cycle
derivation takes the MC clock and ck_per_mc=2), and a fresh calibration
tuple. The peak moves from 600 to 800 MB/s, so it is a different operating
point from the 75 MHz LiteDRAM A/B, not a faster version of the same one.
Not started: the harness clock plan is the framework owner's, and the
measurement point is a decision. Smoke log in the session scratch
(`board100/smoke.log`).

### 2026-10-29, the committed RTL (SET_LAG) on the board at 75 MHz: unchanged, as the proxy said

Fresh 75 MHz build of the tree at e88a0e2d9 (the b8665155e timer change in,
default plan, DDR2-300): WNS +1.235 ns, 0 of 107,853, 36,386 LUTs. Smoke
(init, write_read, memtest) passed on the cached 75 MHz leveling; four
profiles, zero mismatches in every cell. CSVs
`char_granite_setlag75_{open_min,concurrent,multigen,paging_grade}_2026-10-29.csv`.
The LiteDRAM mixed-traffic rows below are the 2026-10-04 CSVs scaled by 0.75
(they were logged against a constant 100 MHz; the board clock was 75), the
same correction as the 2026-10-26 table; its streams are the 2026-10-13 soak.

| MB/s, 75 MHz, peak 600 | LiteDRAM | granite 26 Oct (final) | granite 29 Oct (committed) |
|---|---|---|---|
| open_page streams wr / rd: incremental | 554 / 564 | 576 / 578 | 576 / 578 |
| open_page streams wr / rd: row_major | 569 / 579 | 578 / 580 | 578 / 580 |
| open_page streams wr / rd: col_major (thrash) | 304 / 386 | 292 / 333 | 292 / 333 |
| open_page streams wr / rd: col_major_interleaved | 277 / 280 | 512 / 514 | 512 / 514 |
| stream read latency, cycles | 48 | 50 | 50 |
| concurrent 1w+1r combined: incremental | 248 | 568 | 569 |
| concurrent 1w+1r combined: row_major | 286 | 576 | 576 |
| concurrent 1w+1r combined: col_major | 248 | 213 | 213 |
| concurrent 1w+1r combined: col_major_interleaved | 246 | 402 | 400 |
| concurrent read latency, cycles (incremental / row_major) | 190 / 107 | 78 / 79 | 80 / 79 |
| multigen 1w+2r combined: incremental | 279 | 385 | 385 |
| multigen 1w+2r combined: row_major | 316 | 516 | 509 |
| multigen 1w+2r combined: col_major | 281 | 246 | 246 |
| multigen 1w+2r combined: col_major_interleaved | 247 | 270 | 270 |

Every cell is within noise of 2026-10-26 (multigen row_major 509 vs 516 is
the widest, 1.4 percent), which is what the cycle-identical perf proxy
predicted for SET_LAG. Against LiteDRAM: ahead on every streaming cell but
the page-thrash read (333 vs 386), ahead 1.3 to 2.3x on the page-friendly
mixed cells, and behind on the two thrash cells under mixed traffic
(col_major 213 vs 248 at 1w+1r, 246 vs 281 at 1w+2r): those are the
within-bank-order / page-policy cells, not the direction logic.

### 2026-10-29, the 100 MHz board point: DDR2-400, measured

Owner's go: "do the DDR2-400 build after 75 finishes". `GRANITE_SYS_100`
now selects the DDR2-400 plan (VCO 800, sys 100, sys2x and DQS 200, idelay
200 = /4, pumice's `PUMICE_SYS_100` block), the 3:2 plan is gone from the
top, README and `create_project.tcl`. Build of the tree: WNS **+0.021 ns**,
0 of 107,862, hold +0.053, 36,695 LUTs; reports kept as
`targets/granite/fpga/reports_sys100_2026-10-29_ddr400/`.

**Bring-up.** Leveling with the 75 MHz read-path tuple found no eye (the
smoke's 512 of 512 again). A joint probe on the board (the pumice
`host_bringup_joint_probe` with the granite regmap and the JEDEC timings
derived at 100 MHz, wrlat 0..3 x rddata_delay 0..15 x bitslip 0..7 at tap
16, t_rddata_en 1) found exactly one clean cell, **wrlat 1 / rden 1 /
rddata_delay 1**, with its two diagonal neighbours one beat off (wrlat 0 /
delay 2; wrlat 2 / delay 0): at DDR2-400 the data-vs-valid offset is 0
cycles where the 75 MHz plan has 1. Two host plumbing fixes were needed to
run on it: (1) `pumice_master.A7Leveling` and `SimpleTest` hardcoded
`t_rddata_en = 6` for the leveling pass, so the test's env override never
reached it and leveling ran on (6, 1); both constructors now take
`TEST_T_RDDATA_EN` with the default unchanged; (2) the char path derives
its JEDEC cycle counts from `PUMICE_MC_CLK_HZ` (default 75e6), separate
from the measured clock the smoke uses, so the first char pass ran a 100
MHz controller on 75 MHz counts (tRC 5, tRFC 11) and was discarded; the
run was repeated with `PUMICE_MC_CLK_HZ=100000000` (tRC 7, tRAS 5, tRFC 14,
tREFI 780, tFAW 5). Leveling on (1, 1): bitslip 1, tap 16, eye 2..30 (28
taps; the 75 MHz eye is 9). Smoke init, write_read and memtest passed;
level cache in the session scratch. Env for the run:
`TEST_T_PHY_WRLAT=1 TEST_T_RDDATA_EN=1 TEST_RDDATA_DELAY=1
PUMICE_MC_CLK_HZ=100000000`.

**Results**, zero mismatched beats in every cell of every profile at both
clocks. CSVs `char_granite_sys100ddr400_{open_min,concurrent,multigen,
paging_grade,half_threads}_2026-10-29.csv` and
`char_granite_setlag75_half_threads_2026-10-29.csv` (the 75 MHz
multi-thread run of the same RTL, within 0.1 MB/s of 2026-10-27 on all 32
cells). LiteDRAM columns as in the entry above (mixed rows x 0.75; its
half_threads is the 2026-10-27 CSV, its host has no close_page config).

| MB/s | LiteDRAM 75 (peak 600) | granite 75 (peak 600) | granite 100 / DDR2-400 (peak 800) |
|---|---|---|---|
| streams wr / rd: incremental | 554 / 564 | 576 / 578 | 772 / 774 |
| streams wr / rd: row_major | 569 / 579 | 578 / 580 | 775 / 777 |
| streams wr / rd: col_major | 304 / 386 | 292 / 333 | 390 / 445 |
| streams wr / rd: col_major_interleaved | 277 / 280 | 512 / 514 | 688 / 688 |
| stream read latency, cycles (incremental) | 48 | 50 | 50 |
| 1w+1r combined: incremental | 248 | 569 | 761 |
| 1w+1r combined: row_major | 286 | 576 | 773 |
| 1w+1r combined: col_major | 248 | 213 | 287 |
| 1w+1r combined: col_major_interleaved | 246 | 400 | 539 |
| 1w+1r read latency, cycles (row_major) | 107 | 79 | 71 |
| 1w+2r combined: incremental | 279 | 385 | 516 |
| 1w+2r combined: row_major | 317 | 509 | 691 |
| 1w+2r combined: col_major | 281 | 246 | 325 |
| 1w+2r combined: col_major_interleaved | 246 | 270 | 384 |
| open_page half_pair wr / rd, 1 thread | 243 / 286 | 288 / 240 | 387 / 320 |
| open_page half_pair wr / rd, 2 threads | 71 / 72 | 287 / 288 | 385 / 386 |
| open_page half_pair wr / rd, 3 threads | 70 / 71 | 257 / 281 | 344 / 376 |
| open_page half_pair wr / rd, 4 threads | 70 / 71 | 214 / 249 | 286 / 334 |
| open_page half_oct wr / rd, 1 thread | 243 / 286 | 288 / 239 | 387 / 320 |
| open_page half_oct wr / rd, 2 threads | 71 / 72 | 287 / 288 | 385 / 386 |
| open_page half_oct wr / rd, 3 threads | 70 / 71 | 256 / 281 | 344 / 377 |
| open_page half_oct wr / rd, 4 threads | 70 / 71 | 214 / 249 | 288 / 334 |
| close_page half_pair wr / rd, 1 / 2 / 3 / 4 threads | - | 30/37, 49/59, 73/87, 96/96 | 40/44, 66/87, 97/129, 129/129 |
| close_page half_oct wr / rd, 1 / 2 / 3 / 4 threads | - | 30/37, 49/59, 73/87, 96/96 | 40/44, 66/87, 97/129, 129/129 |

Threads 5 to 8 clamp to 4 (four injectors per direction) and repeat the
4-thread cell. Every 100 MHz cell is the 75 MHz cell times 4/3 to within
rounding: the controller is cycle-identical across the two plans, as the
proxy is, and the DDR2-400 point simply moves the whole table up. Streams
reach 96.6 percent of the 800 MB/s peak; 1w+1r on the page-friendly
families reaches 761 to 773 combined, three times LiteDRAM at 75 MHz; the
page-thrash and mixed-thrash cells remain the gap (col_major read 445 vs
LiteDRAM's 386 at 75, so now ahead in absolute terms, still the lowest
fraction of peak).

The `half_threads` profile exits 2 at both clocks (16 of 32 cells at 75,
14 at 100) on the latency histogram's 1:1 note (7 to 40 returns short of
the host count at >= 2 threads, `mismatched` 0, bandwidth reproducible):
harness accounting, identical on granite and pumice on 2026-10-27, filed as
pumice ISSUE-025; the bandwidth columns are valid.

### 2026-10-29, where LiteDRAM still leads, and the area

Same 75 MHz point, from the tables above. LiteDRAM is ahead by more than
noise in four places, all page-thrash or single-thread half-burst reads:
the col_major read stream (386 vs 333, 16 percent), 1w+1r col_major (248
vs 213 combined), 1w+2r col_major (281 vs 246), and the one-thread
half-burst read (286 vs 240). Its stream read latency is 2 cycles better
(48 vs 50), which is not a lead. Its stock Nexys point is 100 MHz at 1:4
(800 MT/s, 1.6 GB/s peak), which granite does not build yet (item 6).

Area, routed, hierarchical (`reports_sys100_2026-10-29_ddr400/utilization_hier.txt`
against the LiteDRAM 2026-10-13 depth-8 report in
`char_results/area_granite_vs_litedram_2026-10-17.xlsx`):

| controller only, same board, same PHY (420 LUT) | LUTs | FFs | RAMB36 | RAMB18 | DSP |
|---|---|---|---|---|---|
| granite `u_ctrl` (core + CSR), 2026-10-29 | 5,654 | 4,267 | 2 | 0 | 0 |
| LiteDRAM controller proper (`u_core` minus VexRiscv) | 2,435 | 2,069 | 12 | 1 | 0 |
| LiteDRAM `u_core` as shipped (with the calibration CPU) | 4,358 | 3,348 | 13 | 9 | 4 |

Granite by block: age-FIFO store 2,204 (39 percent), scheduler plane 1,753
(pick 726, bank timers 568, page policy 203, global timers 165), AXI plane
1,097 (read-return ring 506), DFI plane 284, CSR 200. Against the 10-17
FRFCFS snapshot (3,666) the pick core and the age-FIFO store cost +2.0k
LUT and bought the mixed-traffic column. LiteDRAM's controller is 2.3x
smaller in LUTs but holds its queues in 12 block RAMs where granite holds
them in logic by policy (2 RAMB36 for the whole core).

### 2026-10-29, item 5: the aged class as a within-class tie-break with a starvation bound

Owner: "003: finish this one." Three changes, all measured:

1. **Placement.** `mc_bank_pick`'s select no longer puts the aged requests
   at the top; the direction / alternation / hint choice runs first and an
   aged pair among what it left in the set goes ahead of the rotor (a hint
   is a single pair, so it is kept or left alone). With the ages compiled
   out `r_aged` is zero and the select is unchanged.
2. **The bound.** The store's `sched_age_thresh` field was an enable only
   (its magnitude unread), and the FIFO's thresh bit marks the oldest
   entry in the pool, which always exists: the class fired on every pick.
   Now one saturating counter per queue head counts the cycles the oldest
   head has been passed over, and the head joins the aged class at
   `thresh - 1` cycles (1 = the moment it is oldest, the old form).
3. **Timing.** The first `HAS_AGE=1` board build missed by 1.528 ns (682
   endpoints, all `g_q[*].u_rq -> g_q[*].u_*q` age registers, 19 levels,
   75 percent route): each queue's `youngest` was a max tree over its
   entry array, then the 16-queue max, then +1, then every entry's age
   write. The store now tracks each queue's tail age in its own register
   (it is the pool writer: push loads the age, age_dec steps it, empty
   reads 0; exact, the FIFO's tree is left unconnected). Rebuilt: WNS
   +0.064 ns, 37,287 LUT / 32,541 FF against 36,386 / 33,715 without the
   ages. Still the thinnest margin in the design at 75 MHz; not a 100 MHz
   form.

Proxy, eight threads (wr / rd cycles, the four stream families, ages
off = 17640 / 17646, 17625 / 17626, 18430 / 18073, 21434 / 21443):

| thresh | incremental | row_major | col_ilv | col_major |
|---|---|---|---|---|
| 1 (oldest-first always) | 19324 / 20028 | 19530 / 20034 | 19510 / 20365 | 21437 / 21443 |
| 8, 32, 128 (the bound) | 17645 / 17646 | 17622 / 17634 | 18356 / 18074 | 21381 / 21443 |

Thresh 1 is 9 to 12 percent down on every stream, as bad as the
top-of-select form (the oldest head always wins and the rotor's spread is
lost); from 8 up the families are back to the ages-off cycles. The
store's tracked tail age is cycle-identical to the FIFO's max tree at
eight threads (thresh 1, all four families); at one thread the two differ
by about 20 cycles on three families, the same families and size as the
proxy's own run-to-run drift below, so not attributed.

Board, granite 75 MHz, `HAS_AGE=1` bitstream, `CHAR_AGE_THRESH` 0 / 1 / 16
/ 64 (`char_granite_age{0,1,16,64}_75_*_2026-10-29.csv`), 49 cells each,
all clean. Against thresh 0 (= ages off; itself within 0.9 percent of the
`setlag75` baseline on every cell):

| thresh | mean delta | worst cell | cells > 2 percent down |
|---|---|---|---|
| 1 (oldest-first always) | -2.1 percent | 1w+1r col_major_interleaved 200 -> 139 (-30), col_major 106 -> 92, incremental 282 -> 262; mixed latencies +20 to +40 percent | 15 of 64 |
| 16 | +0.2 percent | none down; open_page half_pair thr3 285/285 vs 255/280 (up) | 0 |
| 64 | -0.0 percent | incremental 1w+1r 282 -> 276 | 2 |

So the aged class has no bandwidth upside at any setting and costs the
mixed cells when it fires on every pick; with the bound at 16 or more it
is a starvation guarantee at no measured cost. Decision taken here:
`HAS_AGE` stays 0 as the product default (area and the 0.064 ns margin),
the bound form is what `HAS_AGE=1` builds get, and a product that wants
the guarantee sets `age_thresh` >= 16. The "CSR weights on the select"
half of item 5 is NOT built: with the tie-break neutral at the bound and
nothing to buy on the bandwidth side, a weight form has no measured
target; the owner's call whether to pursue it for latency-tail fairness
(the profiles measure average latency only).

**Proxy determinism, settled the same day.** Three runs of the HAS_AGE 0
proxy on 2026-10-29 gave three col_major read counts (3464, 3443, 3448)
and two row_major write counts (2154, 2133), which looked like the
tie-break or the store edit moving cycles. They are not: an A/A pair
(same tree, same env) is identical on all four families; the store edit
swapped for HEAD's is identical; the progress probe on vs off moves
col_major read by 5. What changed between the runs was the HOST's command
sequence before and during a run (the BUILD_CONFIG reads
`set_jedec_timings` now does for the clock ratio, the probe's meter reads),
and every host transaction takes simulated UART time, so the phase's start
moves against the refresh counter (tREFI 585) and a refresh lands inside
or outside the measured window: the moves are 2 to 21 cycles, one tRFC.
Rule for this proxy: "cycle-identical" is only meaningful between runs
with the same host sequence; a host-side change re-baselines, an RTL A/B
must hold the host fixed (as the store A/B above did).

### 2026-10-29, item 6: DFI 1:4 built, timed and brought up to one defect

Owner: "003: finish this one." The 1:4 point exists in the tree and on
the board; it is NOT characterized, for one reason given at the end.

**What is in.** Two four-phase a7ddrphy netlists
(`rtl-vivado/a7ddrphy/a7ddrphy_nph4_{75,100}_generated.v`, LiteDRAM
2024.12, `bin/elaborate_a7ddrphy_nph4.py --nphases 4 --sys-clk`; they
differ in rdphase / wrphase / tap constants, so one per sys clock),
`GRANITE_DFI4` (75 MHz sys, CK 300, DDR2-600, peak 1.2 GB/s) and
`GRANITE_DFI4_100` (CK 400, DDR2-800, 1.6 GB/s) plans in
`granite_char_top` (sys4x / sys4x_dqs from the MMCM, DFI_RATE 4, BL8,
and a 128-bit host AXI: the proxy at 1:4 with the 64-bit port wrote
streams at 589 MB/s, the port's own ceiling at 75 MHz), the stub with
both clock port sets, the project script selecting netlist and define,
and the host deriving ck_per_mc from BUILD_CONFIG and CL from MR0 with
DFI / PHY phase and write-bitslip env knobs on every flow.

| build, 75 MHz | WNS | LUT | FF |
|---|---|---|---|
| 1:4 BL8, 64-bit host | +0.763 | 44,149 | 43,413 |
| 1:4 BL8, 128-bit host (GEAR-1, converters bypassed) | +1.177 | 39,833 | 35,449 |

**Board.** The 1:4 bitstreams initialize (`dfi_rate=4 gear=2 bl=8
beat=32b clk=75.00MHz`), the init sequence completes, writes land. The
joint probe (fixed for the 128-bit stride; its first form strode by the
64-bit beat and overlapped its own transactions, a 3-of-8 floor that
cost an hour) finds the read gate at wrlat 1 / t_rddata_en 1 /
rddata_delay 1 or 2, controller read phase 1 with bitslip 0 (phase 0
with bitslip 6, 2 with 2, 3 with 4: one phase = two bitslips), tap eye
14 to 30. In every one of those cells exactly ONE 128-bit beat per read
transaction is wrong, at a transaction boundary: a run of two adjacent
transactions has 1 wrong beat, the same transaction read three times in
one run (stride 0) has 3, a junk transaction followed by a real one has
4 + 1, and a single transaction read alone has 1 whether it is the first
or the second written. Not moved by: read phase 0..3, read bitslip 0..7,
PHY rdphase CSR 0..3, write bitslip 0..3, IDELAY tap 0..30, tWR +1..+8,
tRP +2/+4, seed, transaction count 1..16, lane-asymmetric bitslip
(worse). The tap sweep says the analog eye is real and wide; the beat is
digital. Also seen: a burst-length-2 (and 1) write transaction hangs the
write engine at the 128-bit geometry (burst-length 4 runs). The 1:4
proxy sim (TEST_DFI_RATE=4 TEST_DRAM_BL=8 TEST_DRAM_BEAT_BYTES=4
TEST_DRAM_DEVICE_BYTES=2) writes every family at the port ceiling and
returns NO read data for any t_rddata_en 2..6 (the UART smoke: `act 0,
valid False`), no slave-model warnings.

**Next step, not taken today:** a waveform of the DFI read return at
DFI_RATE 4 / BL_WORDS 1 in the sim (the proxy's read hang is the cheaper
reproduction) and, on the board, which beat of the transaction is the
wrong one (the harness has no first-mismatch index register; adding one
to `char_gen_unit` is the small change that would have shortened this).
Both symptoms point at the same place: the rd aligner's one-word capture
window at 1:4 (EN_CYC = BL_WORDS = 1) against a PHY whose read valid is
one cycle wide but whose last word for a run arrives after the strobe
goes idle. Until that is fixed the 1:4 numbers do not exist; the 1:2
DDR2-400 point (800 MB/s peak, 772 / 774 measured) stands as granite's
100 MHz board point.

Scratch for the next session: `board75_dfi4w/` (bitstreams, probes
`probe_fixed.py`, `exp_which.py`, `exp_tap.py`, logs), `board75_dfi4/`
(64-bit host), `litex/venv310` (the LiteX environment).

**Item 6 root cause, found 2026-10-29 afternoon (sim trace).** A cocotb
trace of the 1:4 UART smoke's read return showed the controller issuing RD
on phase 0 and asserting `dfi_rddata_en` as `0011`: two of four phases.
`granite_top_geared` hard-wired `GEAR_RATIO = 1` ("the A7 build is fixed
at 1:2") into the DFI plane's `gear_i`, whose active-phase mask ANDs the
write and read enables, so every DFI_RATE=4 build drove the PHY's enables
on half its phases: no read data in the proxy (the slave model gates on
the enables), and on the board the a7ddrphy's rddata_en comes from one
phase, which is why reads were only one beat per transaction off. The
parameter now follows `DFI_RATE` (`$clog2`). The 1:4 UART smoke passes;
the 1:4 128-bit board bring-up is rebuilding with it.

**After the gear fix (2026-10-29, 14:10).** Sim: the 1:4 UART smoke passes
(reads return); the 1:4 proxy with the 64-bit host writes at the port
ceiling but reads at 135 MB/s (9,100 cycles for 16 KB: one read at a time),
and with the 128-bit host reads run at 569 MB/s but 1020 of 1024 beats
mismatch on the two streaming families while the two page-miss families
are clean -- the aligner probe counts 2048 valid words for 1024 reads, two
per BL8 burst where `BL_WORDS` is 1, so back-to-back returns pair the
second word of burst N with read N+1. The RDS-DV slave infers rate 4 and
two device words per phase from the bus widths, so which side emits the
second word (the model's legacy read service or the controller's enable
window) is the next thing to settle; a spaced read drops it on credit and
is correct. Board, 128-bit host, gear fixed: build WNS +1.280, the probe
lands the same cells (wrlat 1 / rddata_delay 2 or 3 / bitslip 2 at read
phase 0, bitslip 4 at phase 1) and still one 128-bit beat per read
transaction wrong. The two symptoms may be the same mechanism seen through
different return timings (the PHY's valid is one cycle per enable cycle;
the slave's is not). Not resolved today; the 1:2 DDR2-400 point remains
granite's 100 MHz number.

### 2026-10-29 evening, item 6: both residuals read off the bus

**The proxy's "two valids per read" was the host.** The perf proxy's
stream families programmed every beat at `AXI_SIZE_8` (the 64-bit
convention); on the 1:4 build's 128-bit host that is a NARROW transfer,
two per 16-byte line, and each one is its own BL8 read: 2048 RD commands,
2048 enables, 2048 valids for 1024 lines, nothing duplicated at the PHY
(the aligner's probe and the smoke's cycle timeline agree: one RD, one
enable, one valid, one capture per read). With the beat size derived
from `TEST_AXI_DATA_WIDTH` (full-width beats, as on the board) the 1:4
proxy is clean on all four stream families:

| 1:4 proxy, 128-bit host, 75 MHz sys / CK 300 (peak 1200 MB/s) | wr / rd MB/s |
|---|---|
| incremental | 1135 / 1151 |
| row_major | 1148 / 1148 |
| col_major_interleaved | 918 / 913 |
| col_major | 666 / 713 |

mismatched 0 everywhere, held WRITEs 0. The narrow-beat case is a real
defect of its own (adjacent narrow reads of one line return wrong data;
the 64-bit host's 4-byte beats do not) and is filed as **TASK-007**.
`TEST_AXI_SIZE` keeps it reproducible.

**The board's one wrong beat is the PHY's first word of a read run.** An
ILA on the DFI boundary of the 1:4 128-bit bitstream (`make bitstream-ila`,
depth 4096, trigger on `dfi_rddata_valid`), driven by the same 2 x 4-beat
write and read the probes use, on the best cell found by a fresh scan
(ctrl rd_phase 0 / bitslip 2 / rddata_delay 2 at wrlat 1, rden 1, tap 16:
1 of 8 beats wrong; rd_phase 1 / bitslip 4 is the other 1-of-8 cell, every
other cell 8 of 8):

| cycle | bus | what |
|---|---|---|
| -9 .. -2 | RD b0 col 0x0, 0x8, ... 0x38 | eight BL8 reads, one per cycle, one run |
| -8 .. -1 | rddata_en = f | one enable cycle per read |
| -2, -1 | PHY rddata = W0 (low device word 0x2fff, written 0x1db6), W1 | data two cycles ahead of valid (rddata_delay 2 slides it under) |
| 0 .. 7 | rddata_valid = f; delayed rddata = W0' W1 W2 W3 W4 W5 W6 W7 | the controller's input: all eight words in order under the valid, W0 with its first device word wrong |
| +6, +7 (PHY side) | 0x0fd9 (W7's last device word) then 0 | the ISERDES holding the last captured bits after DQS stops |

Written vs read, controller side: words 1..7 identical, word 0's lowest 16
bits (the FIRST device word on DQ of the run) 0x2fff for 0x1db6. The low
byte all ones is the bus before the DRAM drives it. So: the first DQ beat
of every read run is sampled before the device's first data bit on this
cell, every later beat is inside a wide eye (the tap sweep's 14..30), and
the controller, aligner and return path carry exactly what the PHY gives
them. One wrong word per RUN, not per transaction: two adjacent
transactions were one 8-read run here and cost one word, as `exp_which`
found; its "3 for three same-transaction reads" were three runs (the
same address re-read serializes).

Not a controller defect, and not reachable from the controller: the data is
wrong on `w_dfi_rddata` before the harness's delay line. The 1:2 points
(DDR2-300 at 75, DDR2-400 at 100) do not show it. Candidates, in order,
all board experiments on the `board75_dfi4ila` bitstream: (1) the DRAM's
output drive and ODT (EMRS1: full vs reduced drive, RTT off / 75 / 150 --
the host needs an EMRS1 override like `TEST_MR0`), (2) the FPGA-side DQ
termination (`IN_TERM UNTUNED_SPLIT_50` in the XDC) against a first bit
that starts from high-Z, (3) a first-word-aware leveling pattern (the
cell scan compares the whole burst; LiteDRAM's own calibration does too,
but LiteDRAM has never been run at nphases 4 on this board -- its 75 MHz
build is CK 150), (4) the `a7ddrphy_nph4` read path's bitslip/rdphase
pairing (one phase = two bitslips, so the first-word position is quantised
to half a word).

Also seen on the 1:4 bitstream: a write started after a mismatching read
(full-width or narrow) hangs the write engine until a soft reset. Logged
under TASK-007 to attribute (harness latched error vs controller).

Scratch: `board75_dfi4ila/` (ILA bitstream, `cap_rd.py`, `cap_wr.csv`,
`cap_rd.csv`, `cap.log`), `sims_dfi4b/` (the smoke timeline, the
full-width and narrow proxy runs).

### 2026-10-29 evening, the STORE_MERGE_EN default does not close at 100 MHz

Two builds of HEAD (b8b08375c) on the DDR2-400 plan (`GRANITE_SYS_100=1`):

| build | WNS | failing | LUT / FF |
|---|---|---|---|
| STORE_MERGE_EN=1 (the new default) | **-2.544 ns** | 3,242 of 106,699 | 37,811 / 32,221 |
| STORE_MERGE_EN=0 | +0.011 ns | 0 of 105,519 | 36,381 / 31,773 |

The failing cone is the TASK-006 pick-to-store path: `u_bank_pick/r_held_pair`
-> `u_fifo_store/r_wr_fdone`, the per-bank queues' `rd_empty` / `wr_full`
and the fill-order FIFO, 12.5 ns with **78 percent route** (9.7 ns of
wire, 15-16 levels), 786 endpoints in the store, 456 in the read-return
ring, and the harness's W channels and skid dragged in behind them
(placement spread, not logic). At 75 MHz the same cone is the +0.002 ns
margin. So the 100 MHz board point stays STORE_MERGE_EN=0 (the merge-off
bitstream `board100c/ddr2_char_granite_100mhz_nomerge_2026-10-29.bit` is
what the 100 MHz sweep runs on), and a merge build that closes at 100 is
TASK-004 material: register the pick's fire into the store (one cycle of
commit latency), or keep the fill-pending check out of the fire path by
qualifying it a cycle earlier, then re-floorplan the store beside the
pick.

### 2026-10-29 night, the page policy against LiteDRAM's: the lookahead close is already on

Owner: "LiteDRAM's hybrid page policy, wouldn't that help?" Read against
the RTL and then measured. LiteDRAM's bank machine keeps a row open and
sets auto-precharge on a column only when its one-entry lookahead holds a
different row for that bank. granite's pick has the same rule as
`CLOSE_ON_DRAIN` (a column carries AP when no same-row entry sits behind
it in its bank), and it is ACTIVE on the board: every host preset writes
`policy_mode` 0 (legacy), where the pick's AP is `page_policy_or == CLOSE
|| (CLOSE_ON_DRAIN && !behind_same_row)`. Proof: the `defaults` preset
(page_policy_or 0) and `open_page` (1) are the same mode and measured
bit-identical on 54 + 6 + 32 + 4 cells
(`char_granite_pagepol75_{every,windows,half_threads,concurrent}_2026-10-29.csv`).
The adaptive modes that were removed (4 adapt_time, 5 adapt_access, 6/7
rbl, the HYBRID override encoding) were predictors on top of this, retired
on measurement (mode 4 redundant to fixed_open, 6 lost 26 percent, 7
converged to open page) or by decision (5, mis-plumbed into AP).

granite's remaining page lever is mode 3 `fixed_open` (idle-timeout
PRE; it turns the drain-AP off). On `every`, tr_init 1 / 2 / 4 identical:

| cell, MB/s wr/rd | open_page (drain AP) | fixed_open | LiteDRAM |
|---|---|---|---|
| col_major_bl8 | 292/333 | 311/360 | 304/386 |
| col_major_bl16 | 387/426 | 404/442 | 396/464 |
| col_major_interleaved_bl8 | 512/514 | 459/459 | 277/280 |
| incremental / row_major | 576/578, 578/580 | 574/575, 578/580 | 554/564, 569/580 |

So the timeout buys 6 to 8 percent on the all-miss walk and costs 10
percent on the bank-hop walk; neither closes the col_major READ gap to
LiteDRAM (360 vs 386), which is the pick's per-hop pipeline latency on a
dependent PRE -> ACT -> RD chain (TASK-044's "gap 9 vs the floor of 6"),
not the policy. A combined form (drain AP plus idle timeout in one mode)
does not exist today; it is the one untried page-policy variant.

### 2026-10-30, the untried page variant tried: drain AP + idle timeout (mode 4)

Owner: "the one untried variant: try this." `mc_page_policy` mode 4
`drain_timeout` keeps `ap_mode_en` low (so the pick's CLOSE_ON_DRAIN
auto-precharge stays on) and runs the fixed_open idle timeout as well;
host presets `drain_timeout_tr{1,2,4}`; directed test
`test_granite_core_page_mode[0,1,3,4]` tells the four modes apart by
exact (ACT, PRE, AP) counts on one fill-lag stimulus. Bitstream WNS
+0.212, 37,315 LUT. Board, granite 75 MHz, MB/s wr/rd:

| cell | open_page (drain AP) | drain_timeout tr1 / tr2 / tr4 | fixed_open tr2 | LiteDRAM |
|---|---|---|---|---|
| col_major_bl8 | 292/333 | 292/333 (all three) | 311/360 | 304/386 |
| col_major_interleaved_bl8 | 512/514 | 512/514 | 459/459 | 277/280 |
| row_thrash / random | 512/514, 468/481 | same | 462/462, 446/460 | 271/278, 286/298 |
| half_oct_thr4 | 215/249 | 214/249 | 283/283 | 70/71 |
| half_pair_thr4 | 268/289 | 268/290 | 289/291 | 70/71 |
| concurrent col_major_bl8 | 106/106 | 106/106 | 166/166 | 124/124 |
| incremental / row_major | 576/578, 578/581 | same | 574/575, 578/580 | 554/564, 569/580 |

Mode 4 is bit-identical to open page on all 96 cells, for a mechanical
reason: with the drain AP on, the only row ever left open is one with a
same-row follower already behind it, and that follower carries the AP
when it fires; an idle timeout has nothing left to close. The variant is
measured, kept (cheap, tested) and answered.

What the same run shows instead: fixed_open (timeout PRE, drain AP off)
beats the drain AP on every cell where a bank's next access is a
different row -- col_major +7 percent, concurrent col_major +57 percent
(106 to 166), half_oct 4 threads +14 / +32 percent -- and loses 10
percent on the bank-hop and thrash walks. A background PRE two cycles
after the last column lets the next ACT come sooner than the same close
folded into the column as auto-precharge, which means the bank timers'
AP accounting (tWR + tRP after a write with AP, tRTP + tRP after a read
with AP) is conservative against the explicit PRE path by about two
cycles. That is a scheduler-timing lead, not a page-policy one, and the
next item on the col_major gap to LiteDRAM.

### 2026-10-30, the combiner's timing, taken apart build by build

Owner: the original combiner was "very simple, not adversarial to timing";
was a new mechanism introduced? Partly: the 2026-10-29 corruption fix
exported the store's live per-slot fill-pending vector into the pick's
fire term (a store-to-pick-to-store loop in one cycle), which the task's
own scope had excluded ("not this task: anything on the pick core"). It
is gone: the race it closed (a merge admitted into a filled entry in the
one cycle its registered head record still says schedulable) is closed in
the store instead, by masking the merge target out of the head record in
the admission cycle (`h.vld && !(w_aw_merge && w_mg_slot == s)`), store
registers only, ending in the record register. Refusing the merge
instead was tried first and merged nothing (0 of 1024 pairs: the first
half's fill completes before the second half is admitted). With the
mask: proxy pair walk 1024 / 1024 merged, 0 held writes, 289.8 MB/s;
common-ip 37 passed, granite top 14, pumice top 217.

| build, merge default | 75 MHz WNS | 100 MHz WNS | 100 MHz failing |
|---|---|---|---|
| merge off (same tree) | +0.756 | +0.011 | 0 |
| combiner, first form (store only) | +0.358 | not built | |
| + the three corruption fixes, live pick check | +0.002 | -2.544 | 3,242 |
| pick check removed, admission refused | | -2.153 | 2,189 |
| pick check removed, record mask (this) | +0.135 | -1.609 | 2,105 |

So the pick path was 0.9 ns of the 100 MHz miss and the combiner itself
is the other 1.6: the failing cone runs from the bank timers through the
pick's fire into the store's bank-queue pointers (755 endpoints) and the
read ring's shadow-source registers (390), 12 ns with 75 percent route,
the cone the TASK-003 placer sweep and pblock attempts already found
"not the lever". The lever at 100 MHz is a registered commit stage (the
fire into the store pop and the ring allocation, one cycle), which moves
the tCCD=1 cadence unless the pick speculates across it -- the owner's
call (2026-10-30, asked). Until then: 75 MHz ships the merge default
(+0.135), 100 MHz ships merge-off (+0.011).

### 2026-10-30, merge default at 100 MHz: the cones taken out one by one

Owner: "Merge default stays on; build 100mhz." Every step below is the
same merge rate on the proxy pair walk (1 thread 256/256; 4 threads 1019 /
1024 writes, 1024 / 1024 reads; 0 mismatched, 0 held writes) and clean
common-ip / granite top, except where noted.

| step | 100 MHz WNS | failing | what it removed |
|---|---|---|---|
| record mask (the TASK-006 fix, store-local) | -1.609 | 2,105 | the pick's live fill-pending check |
| merge searches exclude the pick's HELD candidate, not the live commit | -0.296 | 132 | bank timers -> fire -> merge -> queue pointers / ring |
| + registered AR decode stage in mc_rd_intake (AR_STAGE_REG) | -0.233 | 92 | ADDR_MAP CSR -> AR decode -> read merge -> ring |
| candidate as coordinates (bank, record 1/2), resolved in the store | -0.256 | 90 | the record-slot round trip (no gain: not the long part) |
| + ring shadow marking one cycle late (MERGE_MARK_REG) + AW waits when its match is the candidate | -0.462 | 80 | merge -> ring r_src; candidate -> AW allocation |

Tried and rejected on merge rate: a store-local "fireable head" set in
place of the candidate (-0.119 / 19 failing, but 4-thread merges fell from
1019 to 6 of 1024: with several threads the target is usually a fireable
head).

At the last step no combiner cone tops the report: the worst two paths are
the pick's own tail (`r_stale_pick` / `r_cls` -> `r_pick_cls`, -0.46), the
cone the placer sweep above put in a half-nanosecond noise band on the
merge-off RTL; the combiner's worst is the held AW's address match into the
bank-queue count, -0.24, registers only. Next: placer directives on this
RTL; then, if needed, a registered AW match (a second AW stage with
forwarding from the AW allocated in the previous cycle).
