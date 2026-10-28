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
   cost-function form the owner asked about), tuned on the board.
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
