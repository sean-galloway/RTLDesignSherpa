# TASK-007: batch same-direction columns to amortise the R/W turnaround
> **Was `PUMICE-039` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

### 2026-09-23: batching had a READ-STARVATION defect; fixed, and the old validation was geometry-bound

**The "+25-30% recovery, clean" record below was measured with a broken
feature.** SCHED_WR_WM latched the drain at wr_high_wm and cleared it only at
wr_low_wm, so a CONTINUOUS writer held occupancy above low_wm forever, the
drain never released, and READS NEVER ISSUED. It could not self-correct: the
drain overrides prio_sub entirely and SCHED_POLICY.age_thresh is 0 by default,
so sch_age_exceed_o is inert -- there was no anti-starvation path on that
branch at all.

Fixed in `fc83c1b3c` by BOUNDING the batch (WR_BATCH_MAX, now the CSR field
SCHED_WR_WM.wr_batch_max, default 16): after N write columns the drain yields
and r_rd_owed blocks re-arming until a read column actually fires. tRTW
amortises ACROSS the batch, so 20 cycles over 16 writes is 1.25 each and an
unbounded drain buys no further amortisation.

Bisected by DOUBLE TOGGLE, since the range contains the feature switched on,
off and on again: 16119318a ON -> BAD, bc36f2d28 OFF -> GOOD, 1f6a3bfdf ON ->
BAD. Corroborated by bank_gap_sweep going 242 failures -> 0 with
TEST_WR_HIGH_WM=0.

**Why the original validation missed it, which matters more than the bug.**
"210 concurrent runs, 0 failures; 1008 matrix cells, 1 unattributed beat" is
real, and all of it ran BL8 through the char harness. None of it ran bl4x16
through pumice_top, where one AXI beat is one DRAM burst and a single writer
can hold the CAM above the watermark indefinitely. `bc36f2d28` reverted
batching over ONE failing cell and `1f6a3bfdf` (mine) put it back arguing 1008
clean cells outweighed that. The reverter was right with less evidence. This is
[[PUMICE-028]]'s thesis in one incident: a conclusion valid in the geometry the
suite could express, with a hole exactly where it could not.

[[BUG-001]] ("one unattributed mismatched beat in 1008 cells") was the
evidence used to justify that re-enable. It should be re-examined now that
batching is known to have starved reads -- the beat may not be unattributed.

**The +25-30% board figure is NOT restated here.** It was measured with the
unbounded drain. Re-measure against the 16-write cap before quoting it.

**Status:** CLOSED 2026-09-25 — corruption fixed (210 clean board runs), wire-level JEDEC audit now gates it. **Priority:** P3
**Corruption FIXED and proven (210 clean board runs). Deferred on timing only --
and that timing is ACCEPTED: Sean 2026-09-17, "this is designed for aggressive
timing." Do NOT re-raise the +16 ps margin as a blocker.**

2026-09-16: the mechanism ALREADY EXISTS -- `SCHED_WR_WM` in
pumice_cmd_arbiter.sv, shipped with high_wm=0 (disabled) and, until
6ba9dba62, with no host accessor at all. Enabling it on the board recovers
**+25-30% bus bandwidth** (240.7 -> 312.6 MB/s at gap 12), more than the
-17.4% that PUMICE-037's tRTW=20 costs.

It also CORRUPTS: 4 beats/run, 50% all-ones -- PUMICE-037's DQ-collision
fingerprint. Cause is NOT the arbiter (see PUMICE-042): with CMD_HISTORY_EN
armed, check (7) GLOBAL tRTW fired ZERO violations while batching was on with
the watermark readback verified. The scheduler spaces correctly; the DFI cmd
path compresses it.

### 2026-09-16 (later): batching STALLS. Default reverted to disabled.

The clean-and-fast result below was measured at gaps 12 and 15 ONLY. A wider
sweep (seq_wr_batch, 8 gaps x 2 generator counts x 3 watermarks x 4 reps = 192
runs) found intermittent stalls immediately:

    hi=0 (off)   16 points   0 non-clean
    hi=2/lo=1    16 points   1 -- 1+1 gap=4,  2/4 runs, timeouts=2, [360,0,0,359]
    hi=8/lo=4    16 points   1 -- 1+1 gap=11, 1/4 runs, timeouts=1, [0,0,1,0]

**CORRECTION (same day):** that "matching timeout count" was an artifact of my
own instrument, and the conclusion drawn from it was WRONG. The sequence
counted `not r.ok` as a timeout, but pumice_char computes

    ok = wr_ok and rd_ok and mism == 0 and rd_total == expect_rd_txn

so `not r.ok` counts MISMATCHES too, and "fails == timeouts" was tautological
rather than corroborating -- the two were computed from the same condition.

Re-measured with engine completion read from the NOTES instead: `stalled=False`
on every failure, `timeouts=0` everywhere. **Both engines complete. This is
data corruption, not a stall.**

    hi=0 (off)   0/8 failing
    hi=2/lo=1    2/8 failing   mism = 180, 359
    hi=8/lo=4    1/8 failing   mism = 360

Batching-off is clean on the identical workload. The counts are QUANTIZED
around 180 and 360 (and 179/359, one short) out of 16000 beats per run --
roughly 1.1% and 2.2%, with 360 = 2x180. Random DQ collisions would scatter;
a fixed ~180-beat unit means something structural is mis-delivered. Identifying
what has size 180 (region, CAM depth, drain length, burst count) should name
the mechanism.

PUMICE-042's fix cleaned gaps 12/15 but NOT gap 4.

**Both failures are at 1+1 -- which is also the ONLY configuration batching
helps.** +30.6% at 1+1; ~0% at 2+2/3+3/4+4, where the bus plateaus at ~160 MB/s
regardless because multiple generators already keep same-direction work queued
and there is no turnaround left to amortise. So the one regime it benefits is
the one where it breaks.

**Correction:** the two bank_gap_sweep runs that died/stalled in the 2+2 stage
were blamed on the sweep script, on the strength of a measure_concurrent check
at gap 12 ONLY showing no timeouts. Both had batching defaulted on, and
batching demonstrably stalls at other gaps. Same defect -- the tooling was not
at fault.

**PUMICE-043 folds into this** -- its 1-beat-in-1/8 residue at hi=8 is the same
corruption at a different gap, not a separate defect.

### ILA, 2026-09-17 — the DRAM is not driving; pumice returns that faithfully

Capture on a failing run (trigger rd_dbg_mismatch, batching hi=2/lo=1, gap 4,
1+1), reports/ila_pumice039_batching.csv:

    valid beats 940, mismatched 180
    all-ones (undriven DQ)            91/180
    wrdata_en during a read return     0 cycles
    dfi_rddata == rd_dbg_actual        EVERY mismatched beat

Three things follow, and they redirect the search:

1. **NOT PUMICE-042's mechanism.** Zero write-during-read overlap. The DFI-side
   turnaround fix is not implicated.
2. **pumice does NOT mangle the data.** What the PHY delivers is bit-for-bit
   what the reader receives.
3. **The DRAM is not driving DQ.** The captured beats alternate between
   all-ones (undriven) and ONE repeated stale word (2b53168cedf9d1c9) -- the
   a7ddrphy's free-running ISERDES holding its last captured value. The
   capture window is opening over a bus with nothing on it, for ~180 beats.

Ruled out by measurement:
  * read alignment -- batching is WORSE at the old rden=6/delay=7 (4/12 and
    3/12 failing) than at rden=1/delay=2, so PUMICE-040 is not implicated
  * accumulated state -- per-rep soft_reset (every CSR to RTL default, geometry
    restored) does not change the rate
  * over-delivery -- stray=0 on every failure
  * cell damage -- the post-failure read-only audit is always mism=0
  * engine stalls -- stalled=False, timeouts=0

**Leading hypothesis:** the write drain's ACT/PRE activity closes a row that an
already-issued read depends on, so the read finds no open row and the device
drives nothing. That is the same class the arbiter's w_ap_col_guard /
w_pre_col_guard exist for (issue #42: "batch-2 row-1 writes landed on row 0"),
and a long uninterrupted write run is exactly what would defeat a guard sized
for ping-pong traffic. Testable: CLOSE page policy, or writer/reader forced
onto banks that share no rows.

**CLOSE page is clean -- but the test is CONFOUNDED.** baseline (page_policy=2)
runs 0/12 failing at every watermark, where open_page fails 2-4/12. But CLOSE
page also drops the bus from ~435 MB/s to 33 MB/s -- 13x. A clean result at
one-thirteenth the command rate does not separate "row state was the mechanism"
from "the hazard needs a density CLOSE page cannot reach". Suggestive, not
evidence. A better discriminator holds the rate roughly constant while changing
row reuse -- e.g. open_page with writer and reader forced onto banks that share
no rows.

Next: identify the ~180-beat unit (stable at exactly 180 across both read
alignments), and find a row-state test that is not rate-confounded. It is the strongest clue available -- a
fixed quantum of mis-delivered data, not scattered collisions. Candidates:
the concurrent region size (0x20000 per the notes), the read CAM / return-ring
depth, or the number of bursts in one drain.

### Earlier the same day (superseded by the above)

2026-09-16: PUMICE-042 is fixed, and batching is now CLEAN and FAST:
  gap12 hi=2/lo=1  0 mismatched, bus +29.9%
  gap15 hi=2/lo=1  0 mismatched (0/8 reps), bus +25.0%
hi=2/lo=1 is both the cleanest AND the fastest setting -- higher watermarks
give LESS bandwidth and a residual (PUMICE-043), so there is no trade-off to
tune. What remains is deciding whether to make it the BUILD DEFAULT (currently
high_wm=0 = disabled) and validating that with a batching-ON matrix + gate.

PUMICE-037's fix costs **-17.4% of bus bandwidth at gap 15** (writes -17.4%,
reads unaffected): the arbiter pays the full ~18-cycle tRTW on EVERY direction
switch, and at high gap nearly every read is isolated so nearly every one
charges it. Gaps 0-12 cost nothing.

LiteDRAM does not pay per switch. Its multiplexer stays in READ until reads are
exhausted or an anti-starvation timer fires, then pays its turnaround ONCE for
the whole batch (`multiplexer.py`: `if write_available: if (~read_available |
max_time0)` -> the RTW chain). pumice's flat FR-FCFS arbiter interleaves freely.

pumice's own source already anticipates this -- `pumice_cmd_arbiter.sv:80`:
"write drain amortizes the tWTR/tRTW bus turnaround instead of ...".

Realignment cannot substitute: tRTW is alignment-independent (proven on the
board, PUMICE-037). Batching is the only route that recovers this bandwidth.

### 2026-09-17: ROOT CAUSE FOUND ON THE ILA -- a swallowed ACT inside tRFC

`reports/ila_pumice039_batching.csv` (hi=2/lo=1, gap 4, 1+1, a 180-beat
failure). The 180 bad beats are NOT scattered and NOT corrupt data:

    distinct ACTUAL values on 180 bad beats: 2
        0xffffffffffffffff   x91    undriven DQ (bus pulled high)
        0x2b53168cedf9d1c9   x89    one stale word held by the ISERDES

That is an IDLE DQ BUS. a7ddrphy's free-running ISERDES holds its last capture,
so "all-ones alternating with one fixed word" means the DRAM drove NOTHING and
pumice sampled the float. Confirmed on the DFI side independently:
`dfi_rddata_valid` is asserted for **180 consecutive samples (2028..2207)**
while `w_dfi_rddata` carries only those two values -- one unbroken run, exactly
matching the checker's 180 bad beats (they arrive later in 8-beat groups, +4 per
group, which is just AXI burst pacing).

**Why the DRAM was silent.** One tRFC violation in the capture:

    REF @448   -> ACT bank7 @463    gap=15
    REF @1036  -> ACT bank0 @1051   gap=15
    REF @1632  -> ACT bank2 @1635   gap=3     *** VIOLATION ***
                  ACT bank1 @1636   gap=4     *** VIOLATION ***
    REF @2205  -> ACT bank3 @2220   gap=15
    REF @2792/3378/3963 -> gap=15 each

Six of seven refreshes pace the next ACT at 15. The seventh lets two ACTs out
at 3 and 4 cycles. The DRAM is still refreshing, so it DISCARDS them -- bank 1
never opens. Every following read to bank 1 is a column access to a closed
bank, and DDR2 answers by driving nothing. The idle run starts with the first
read return after that swallowed ACT and ends **two cycles after the NEXT
refresh** (REF @2205), which re-synchronises the DRAM with the controller's
bank image; the legal ACT bank1 @2308 (gap 103) then works.

Everything else on the DFI was RULED OUT by the same capture, so do not re-test
these: `wrdata_en` never overlaps a read return (0 cycles); zero column
commands to a closed bank from sample 444 on (3..443 are the ILA window opening
mid-stream); read columns march monotonically +4 with no row wrap; RD->WR
accounting is exact (940 RD, 940 valid samples, balance never negative, the
constant +18 is pipeline depth); and the return stream is NOT slipped -- a lag
scan is flat at 0.11% for every nonzero lag. RD->WR turnaround is 20/27/29,
so PUMICE-042's tRTW fix is working.

**Mechanism: spacing computed in the arbiter is destroyed downstream.** The
arbiter enforces tRFC correctly -- `w_act_gate_live = !w_rfc_busy && ...` gates
every ACT branch, and `r_rfc_cnt` loads on the fired REF. But
`pumice_dfi_cmd_path.sv` gates only COLUMN commands:

    assign w_gate = ((!w_is_col) || w_col_ok) && ...

ACT/REF/PRE pass through ungated. When the column gate stalls the single
command stream, row commands queued behind it in the CDC FIFO lose their
arbiter-enforced idle cycles and drain back-to-back on release. The capture
shows exactly that shape immediately before the bad refresh: ACT@1585,
RD@1589-1591, a **19-cycle dead gap**, WR@1611, another gap, 14 back-to-back
reads @1615-1628, then PRE/PRE/PRE/REF/ACT/ACT @1629-1636 as one solid
unpaced run. The good refresh @2205 shows the correct shape: four PREs, REF,
then a clean 15-cycle gap before ACT.

This is PUMICE-042's mechanism on a different command pair -- and PUMICE-042's
own fix (tRTW 3 -> 20) LENGTHENED the column stalls, which is why the residue
appeared after it. Write batching triggers it because the drain is what creates
the long column stalls in the first place.

**It is not only tRFC.** Full spacing audit of the DFI stream:

    pair                          n     min   median
    REF->ACT  (tRFC)              7       3       15   one gross violation
    ACT->RD   same bank (tRCD)  754       1      368   2 violations, gap=1
    PRE->REF  (tRP)              40       1        6
    ACT->ACT  any bank (tRRD)    24       1      150   tRRD=1, legal

The two tRCD=1 cases (ACT bank2 @2677 -> RD @2678; ACT bank3 @3336 -> RD @3337)
are the reader's bank-handoff ACTs and did not corrupt in this run -- marginal
rather than gross, but the same class and latent.

**Fix direction:** enforce row-command spacing on the DFI side, the way
PUMICE-042 enforced turnaround -- a pacer in `pumice_dfi_cmd_path.sv` loaded on
a fired REF that blocks ACT for `tRFC`, plus a per-bank ACT->column pacer for
tRCD. The CSRs already exist (`TIMINGS_RFC_REFI.tRFC`). The general statement
is that ANY inter-command timing computed upstream of the CDC FIFO is
unenforced on the wire; the column gate is currently the only thing that is not.

**Not yet directly probed:** the FIFO-bunching mechanism is inferred from the
command shape on the wire, not from an occupancy probe. An ILA on the CDC FIFO
level + the arbiter-side command stream would confirm it and is the cheapest
next measurement.

### 2026-09-17: FIX -- the DFI layer no longer holds any timing

Sean: "The dfi layer should be super simple. All delays must come from the
scheduler." That is the correct architecture and it dissolves this bug class
rather than patching one more command pair.

Removed from `pumice_dfi_cmd_path.sv`: the `COL_BURST_CYC` parameter, the
`t_rtw_i`/`t_wtr_i` ports, and the `r_col_pace` / `r_turn_pace` /
`r_last_col_was_rd` / `r_col_seen` pacer. The accept gate is now

    assign w_gate = (!w_is_rd || rd_op_ready_i) && (!w_is_wr || wr_op_ready_i);

-- no timing term, only the two STRUCTURAL holds (aligner slot free, write data
staged), both sized never to fire. `pumice_dfi_layer.sv` and `pumice_core.sv`
drop the duplicate CSR plumbing, so tRTW/tWTR now reach exactly one consumer.

Why it is safe, in order of strength:

 1. MEASURED. This task already records that with `CMD_HISTORY_EN` armed the
    global tRTW check fired ZERO violations while batching was on. The
    scheduler's turnaround enforcement was verified correct under the very
    workload that corrupted -- the arbiter was always right, only the wire was
    wrong. The backstop being removed was never load-bearing.
 2. The tCCD clamp `w_t_ccd_eff = max(t_ccd_i, BURST_WORDS)` has an IDENTICAL
    floor to the deleted column pacer (`BL_WORDS == BURST_WORDS`), so that
    pacer could never fire on a correctly-clamped tCCD. It only ever fired on
    the turnaround -- the 20-cycle stall that compressed everything behind it.
 3. No staleness hole in the arbiter: `trtw_ok_i` is a strict flop of a counter
    that loads a cycle after the RD event, so it is stale for exactly 2 cycles;
    `w_wr_turn_block = r_rdfire0 || r_rdfire1` blocks writes for exactly those
    2 cycles. Continuous coverage, and symmetric for reads.

The path is now constant-latency end to end, which is the property that was
missing: arbiter (all timing) -> CMD_DELAY shift register (fixed N, verified a
token shift reg, not a stall) -> CDC FIFO (cannot accumulate, nothing
downstream stalls) -> DFI cmd path (never inserts a cycle) -> wire. Spacing at
the DRAM pins now equals what the scheduler computed.

Consequence recorded in both files: `w_t_ccd_eff` and the arbiter's forward-tCCD
counter are now LOAD-BEARING -- they are the only things keeping the column
period honest, since nothing downstream will absorb a too-tight tCCD any more.

**Gate:** char-framework `families_x16` PASSES on the final RTL --
sim_time_ns=10,496,600 (10.5 ms simulated, 231.8 s wall), not a vacuous fast
pass. Lint elaborates with no new warnings. Net -64 lines; the DFI command path
loses 98 lines of logic.

**STILL OPEN -- do not close this task.** The sim gate only proves the existing
path is not broken. It does NOT prove TASK-007 is fixed, because the failure
is a silicon-only intermittent. Board validation required:
  - bitstream + `seq_wr_batch` with batching enabled at 1+1 gap 4,
  - REF -> ACT must hold at 15 (it was 3), no 180-beat idle-bus runs,
  - and watch for PUMICE-042's RD->WR collision returning, which is the one
    thing this change could regress.

**Follow-up (highest value):** `pumice_cmd_history_checker` watches the ARBITER
OUTPUT, which is exactly why its tRFC check stayed silent through this entire
failure while the wire was violating tRFC by 12 cycles. Retarget it at the DFI
wire and this class of bug is caught in sim instead of by an ILA capture.

### 2026-09-17 BOARD: the DFI fix WORKED for tRFC and exposed a real arbiter bug

Measured on silicon, ILA-verified, 3 watermarks x 10 reps, gap 4, 1+1.

**Round 1 -- DFI pacer removed (5f043e6f8) alone:**

    hi=0 (off)   0/10 clean       <- control, platform sound
    hi=2/lo=1    10/10 failing    ~150 beats
    hi=8/lo=4    10/10 failing    ~155 beats

WORSE than the 2/8 it replaced. But the ILA showed the fix did exactly what it
was designed to do, and named the reason for the regression:

    (1) REF->ACT   min=15  required>=15  violations=0   <- tRFC FIXED
    (2) rddata_valid on an idle bus: all-ones=0         <- 180-beat runs GONE
    (4) RD->WR     min=1   required>=20                 <- NEW: tRTW violated

So the tRFC diagnosis and remedy were both correct. Removing the wire-level
pacer exposed a PRE-EXISTING arbiter defect the pacer had been masking.

**The arbiter defect.** Not FIFO compression -- the ILA shows a lone write
spliced into a back-to-back read stream, surrounding idle gaps regular:

    @2025 RD b0   @2026 RD b0   @2027 RD b0   @2028 WR b2   @2029 RD b0

The column MASKS apply `trtw_ok_i`/`twtr_ok_i` and the fire-history guards at
CLASSIFY time, ~3 pick-pipeline cycles before the command issues. A write
selected while no read had recently fired issues INTO a read burst that started
meanwhile; `w_wr_turn_block` is only 2 cycles wide and is long spent. Four
violations in one 4096-sample capture, all the same shape.

**Fix:** live turnaround re-validation at the FINAL PICK, exactly mirroring the
`w_act_gate_live` pattern already used for ACT (which exists for the identical
staleness reason -- see PUMICE-018).

    assign w_rd_turn_live = twtr_ok_i && !w_rd_turn_block;   // RD after a WR
    assign w_wr_turn_live = trtw_ok_i && !w_wr_turn_block;   // WR after a RD

applied to both column branches, plus the read-priority override so an ILLEGAL
write can no longer defer a legal read. Coverage is continuous at the issue
cycle: cycles 1-2 by the fire history, 3+ by the loaded tRTW counter.

**Round 2 -- with the arbiter fix:**

    hi=0 (off)   0/10 clean    400.6 MB/s
    hi=2/lo=1    2/10 failing  448.2 MB/s   mism [0,1,0,2,0,0,0,0,0,0]
    hi=8/lo=4    2/10 failing  448.2 MB/s   mism [0,0,0,1,0,0,2,0,0,0]

Bulk corruption GONE: magnitude 150-360 beats -> **1-2 beats**, ~100x. Rate back
to the pre-existing ~2/10. Batching now yields +11.9% bus.

**STILL OPEN.** Three things, none of them the bug above:

 1. **1-2 beat residue at 2/10.** Matches the PUMICE-043 signature already
    recorded here (1 beat in 1/8 at hi=8/lo=4), which PREDATES this work. Not
    yet characterised on the ILA.
 2. **Read eye is NARROW and leveling's final verify FAILS, reproducibly.**
    `chosen bitslip 0, read tap 4 (eye 0..9)` = 10 taps, against the recorded
    bring-up tuple of tap 8 / eye 17 wide, plus
    `WARNING: leveling not clean: ['final verify at centred (bitslip, tap) failed']`
    on every run. A marginal read eye is a CREDIBLE cause of a sporadic 1-2 beat
    miscapture with nothing to do with the scheduler. Do not assume the residue
    is a controller bug until this is explained. See
    [[project_pumice_board_bringup_tuple]].
 3. **Timing margin dropped +294ps -> +25ps.** The live gate sits in the
    final-pick cone, which is the known critical path. It CLOSES (post-phys-opt
    WNS=+0.025, TNS=0, hold met) but there is no headroom. Cheaper formulation
    available: because the DFI path is now constant-latency, the turnaround
    counter could be loaded AND checked at the selection stage, making spacing
    correct by construction and keeping the term out of the final-pick cone.

### 2026-09-17 ROUND 3: 90/90 CLEAN. Batching is correct and ON by merit.

The surviving gap-1 tRTW violation had a precise cause -- a ONE-CYCLE SEAM
between the two halves of the guard:

    r_rdfire0 <= w_fire_out && r_do_rd;   // records a fire the cycle AFTER it

but the pick that selects the next command is evaluated the cycle BEFORE its own
command fires. So a WRITE picked in the very cycle a READ fires out sees
r_rdfire0 still 0, and issues one cycle behind it. Neither half is wrong; they
simply do not overlap. Closed by folding the in-flight fire into the live gate:

    assign w_wr_turn_live = trtw_ok_i && !w_wr_turn_block
                         && !(w_fire_out && r_do_rd);

(w_fire_out is r_pick_valid && cmd_ready_i -- registers and an input, never the
combinational pick, so it cannot form a loop. Verilator confirms: no UNOPTFLAT.)

**Board, 30 reps x 3 watermarks x 4000 txn, gap 4, 1+1 -- 90 runs:**

    hi=0 (off)   0/30 failing   400.3 MB/s   <- control
    hi=2/lo=1    0/30 failing   449.3 MB/s   +12.2%
    hi=8/lo=4    0/30 failing   449.3 MB/s   +12.2%

Zero mismatched beats anywhere. **TASK-007's corruption is FIXED**, and write
batching -- the feature that could never be enabled -- now runs clean and pays
+12.2% bus bandwidth.

**The whole arc, every step measured at the wire, not inferred:**

    stage                  tRFC viol   idle-bus beats   tRTW viol   failures
    original                       1              180           -   2/8, 1/8
    + DFI constant-latency         0                0           4   10/10
    + live turnaround gate         0                0           1   3/30, 5/30
    + in-flight fire in gate       0                0           0   0/30 x3

Three distinct defects, each real, each pre-existing:
 1. tRFC: the DFI layer's own pacer stalled the in-order FIFO, compressing
    REF -> ACT from 15 cycles to 3. The DRAM discarded the ACT, the bank never
    opened, 180 consecutive reads captured an undriven DQ bus.
 2. tRTW classify-time staleness: the column masks gate ~3 pick-pipeline cycles
    before issue, so a write selected while no read had recently fired issues
    INTO a read burst that started meanwhile.
 3. tRTW one-cycle seam: as above.

(2) and (3) were latent for as long as the DFI pacer existed -- it masked them.
Sean's architecture call ("the dfi layer should be super simple, all delays come
from the scheduler") is what made them observable. A masked bug is strictly
worse than an open one: it moves under you the moment anything downstream
changes, which is exactly what PUMICE-042's tRTW=20 did.

**Corrected along the way, for the record:** the residue was NOT the read eye.
The bad beats carry a Hamming distance of 36/64 against expected -- random data
from a DQ collision, not a marginal capture. The eye anomaly below is real but
was never the cause.

### STILL OPEN after the fix

 1. ~~**Timing margin is +16 ps** -- refactor needed~~ **ACCEPTED, NOT A
    BLOCKER.** Sean 2026-09-17: *"this is designed for aggressive timing."*
    pumice is a research MC deliberately pushed hard (see
    [[project_pumice_at_rest]]), and a thin positive margin is the intended
    operating point, not a defect. Post-phys-opt WNS=+0.016, TNS=0, hold met --
    it CLOSES, which is the bar. The selection-stage / output-register refactor
    is recorded below for whoever wants the slack back, but nothing is waiting
    on it and it should not be treated as outstanding work.
 2. **Read eye is 10 taps (0..9, tap 4) against the recorded bring-up tuple of
    tap 8 / eye 17**, with `leveling not clean: final verify at centred failed`
    on every run, reproducibly. Not causing the corruption (see above) but
    unexplained and a real deviation from [[project_pumice_board_bringup_tuple]].
 3. ~~**PUMICE-043** should be re-tested~~ -- DONE 2026-09-17, and it WAS this
    same seam. Retested at its exact point (hi=8/lo=4, gap 15) with 30 reps:
    **0/30 failing** (1.8% chance of a false clean at its 12.5% rate).
    PUMICE-043 CLOSED. Its drain-depth dependence was the number of direction
    crossings, not accumulation over the run.
 4. `pumice_cmd_history_checker` still watches the ARBITER OUTPUT, which is why
    it reported zero tRTW violations throughout while the wire was violating it
    four times per capture. Retarget it at the DFI wire.

### 2026-09-17 BREADTH: 0 failures in 120 runs across the configuration space

The 90/30-clean result above was ONE operating point (gap 4, 1+1). PUMICE-037's
history is exactly a fix that held at the tested points and failed elsewhere, so
the fix was re-measured across 5 gaps x 2 generator counts x 3 watermarks,
4 reps = 120 runs:

    gens  gap |      off     hi=2     hi=8 |   gain2   gain8 | fails
       1    0 |    550.3    550.5    550.7 |   +0.0%   +0.1% | 0/12
       1    4 |    400.6    448.3    448.2 |  +11.9%  +11.9% | 0/12
       1    8 |    300.7    335.1    379.9 |  +11.4%  +26.3% | 0/12
       1   12 |    240.7    314.1    286.8 |  +30.5%  +19.2% | 0/12
       1   15 |    209.3    263.0    258.0 |  +25.7%  +23.3% | 0/12
       2  0-15|    160.7    163.0    163.0 |   +1.4%   +1.4% | 0/12 each

    TOTAL: 0 failing runs out of 120   (210 clean runs counting the 90 above)

Includes gap >= 8, which is PUMICE-037's regime, and 2+2, a different
arbitration pattern (more same-direction work queued, fewer turnaround
crossings).

**The performance characterisation is UNCHANGED from the pre-fix measurements,**
which is the check that matters: the fixes removed corruption without perturbing
the scheduler's throughput behaviour.
  * gap 12, 1+1 = **+30.5%**, against the "+30.6% at 1+1" recorded earlier in
    this task from the original (corrupting) measurements. Same number, no
    corruption.
  * 2+2 flat at ~163 MB/s at EVERY gap, against the recorded "~0% at
    2+2/3+3/4+4, bus plateaus at ~160 MB/s" -- multiple generators already keep
    same-direction work queued, so there is no turnaround left to amortise.
  * gap 0 shows no gain, the expected control: no read gap, nothing to batch.

**TASK-007's data corruption is CLOSED on evidence.** What keeps the task open
is the +16 ps timing margin (item 1 above), not correctness.

**Refactor note (for item 1).** The obvious approach -- mirror `r_tccd_fwd` and
load the turnaround counter at SELECTION -- does not transfer directly: tCCD is
direction-AGNOSTIC and loads the same value whichever column wins, whereas a
turnaround counter must know whether a read or a write was selected, and at that
stage BOTH can be candidates with the winner decided downstream. Loading on a
guess is wrong; loading conservatively (block both directions for max(tRTW,tWTR))
would throttle reads behind tRTW=20 and destroy read bandwidth. Two workable
options: (a) replicate the arbitration tie-break at selection, or (b) hold the
arbiter's OUTPUT REGISTER when the registered command would violate turnaround --
which keeps the term out of the pick cone entirely and is safe here precisely
because the DFI path below is constant-latency and cannot compress what it
receives. (b) is simpler and should be tried first.


## 2026-09-25 — items 2 and 4 CLOSED. Nothing outstanding.

**Item 2 (read eye 10 taps vs the recorded tuple's 17) — NOT A DEVIATION.**
It was a comparison across two different operating points. The bring-up tuple
(bitslip 0, tap 8, eye 0..16) was measured on the **66.67 MHz** profile; this
build is **75 MHz**, where the bit period is shorter and the eye is narrower.
Measured across every 75 MHz run on record: 36 x `eye taps 0..9 (width 10)`,
6 x the same centred at 4, 4 x `0..11 (width 12)` — 10 is simply the 75 MHz
value, reproducibly. Sean, 2026-09-25: *"I thought the eye was always 10 clocks
and you couldn't get it any better."* Correct.

The `leveling not clean: final verify at centred failed` warning recorded here
as reproducible **no longer occurs** — zero occurrences across today's runs on
the current bitstream.

One observation worth keeping, and it is not a defect: **every recorded eye
starts at tap 0** — `0..9` or `0..11`, never `3..12`. IDELAY taps only ADD
delay, so a window pinned at the bottom of the range is the signature of a
LEFT-TRUNCATED eye: if the true optimum sits at or before tap 0 you cannot walk
left to find the other edge, and "centring" at 4 centres the visible fragment
rather than the eye. That would make 10 a measurement floor, not a physical
limit. Testable by advancing the coarse alignment (`rddata_delay` +-1) and
watching whether the window moves off tap 0 and widens. It is margin, not
throughput, and 16 MB memtest is clean — filed as an observation, not work.

**Item 4 (retarget the command-history checker at the DFI wire) — DONE, via
the DFI slave rather than the RTL checker.**

Two corrections to this task's own text, both found by reading the RTL:

1. `pumice_cmd_history_checker` does **not** watch the arbiter output. It is
   bound at `cmd_valid_o && cmd_ready_i` — POST cmd-FIFO and POST the CMD_DELAY
   token release, i.e. the scheduler's output. At the time this task was
   written the DFI layer still had its own pacer BELOW that point, which is
   what compressed the stream; the checker's blind spot was the DFI path, not
   the FIFO.
2. That blind spot is now structural rather than positional: the DFI layer
   holds no timing at all (2026-09-17), so the scheduler output SHOULD equal
   the wire. "Should" is precisely what the ILA had to disprove last time.

So the audit went where the wire is already decoded — `DFISlavePHY` in
CocoTBFramework (RDS-DV `472c663`), which sees every command the DRAM sees.
Optional `jedec_timings=` checks tRCD/tRP/tRAS/tRFC/tWTR/tRTW; tRFC and the
turnarounds are the valuable ones because they are not per-bank, so per-bank
state looks correct while they are violated — exactly where the 180-beat bug
hid. Violations are recorded, and `jedec_checks` counts commands audited so
"clean" is never vacuous.

Wired into `_bring_up` with `AUDIT_T_*` knobs that move the audit ALONE,
leaving the DUT programming untouched — which is what makes it
mutation-provable. `perf_paging_sweep` now asserts zero wire violations AND a
nonzero check count.

    real timings          clean over 4067 audited commands, all 8 paging modes
    AUDIT_T_RCD=40
    AUDIT_T_RFC=400       fires: tRCD=29..471, tRFC=8, each with cycle/gap/required

A clean result now means the spacing the scheduler computed is the spacing that
reached the DRAM — the property this task spent three defects establishing, now
checked every run instead of by ILA capture.

Gate: GATE_RC=0, 0 FAILED, 188 passed at BOTH geometries.

**Nothing is outstanding.** Item 1 is accepted (aggressive timing is the design
point), item 3 closed 2026-09-17, items 2 and 4 above. CLOSING.
