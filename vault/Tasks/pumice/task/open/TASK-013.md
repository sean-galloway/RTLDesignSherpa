# TASK-013: the adapt predictors (modes 4/5) are inert on everything measured — but untested on traffic built for them

**Status:** open 2026-09-26  **Priority:** P3 — research question; nothing
depends on it and the modes cost nothing to leave in

Sean, 2026-09-26: *"Leave adapt in; maybe they need more research."*

Raised when [[TASK-011]] retired RBL (modes 6/7) and the obvious next question
was whether `adapt_time` (mode 4) and `adapt_access` (mode 5) should follow.
They should NOT, yet, and the distinction is the point of this task.

## What is measured

Board, txn_scale=1000, peak 600 MB/s. Compared WITHIN each profile (comparing
a sequential number against a concurrent one is how a phantom 50% loss nearly
got reported here):

| profile | scenario | open_page | adapt_time | adapt_access |
|---|---|---|---|---|
| paging (sequential) | incremental_bl8 | 561.4 | 561.4 | 561.3 |
| paging (sequential) | col_major_bl8 | 195.2 | 195.2 | 195.2 |
| pairs_paging_mix (1w+1r) | incremental_bl8 | 276.1 | 276.2 | 276.0 |
| pairs_paging_mix | row_major_bl8 | 285.6 | 285.6 | 285.6 |
| pairs_paging_mix | col_major_bl8 | 88.2 | 88.2 | 88.2 |
| pairs_paging_mix | col_major_interleaved_bl8 | 110.6 | 110.6 | 110.6 |

**Identical to plain open page on all six, within +-0.2 MB/s** -- four
families, sequential and concurrent, no difference anywhere.

## Why that is NOT the same finding RBL got

RBL was retired on a **demonstrated cost**: mode 6 lost 26% of bandwidth on a
workload built specifically to suit it, and mode 7's hill-climb drove itself to
a no-op. The mechanism was exercised, proven to work (thrash% 100% -> 57.8%),
and still lost.

The adapt modes have only a demonstrated **absence of benefit**, and their
mechanisms may never have been exercised at all:

* `adapt_time` closes a row on an idle TIMEOUT. Every workload measured
  saturates the generators, so a bank may never sit idle long enough for the
  timer to expire. A mode whose trigger never fires cannot show a difference.
* `adapt_access` votes a row closed from 2-bit saturating counters that must
  LEARN. Short windows and one address pattern per run give the counters little
  to converge on.

So "inert on everything measured" is what the data supports. "Inert by nature"
is not, and removing them on this evidence would repeat the error [[TASK-010]]
diagnosed for RBL -- concluding from a workload that could not discriminate.

## What would settle it

The [[TASK-011]] method, applied to these modes:

1. **adapt_time** needs traffic with genuine idle gaps per bank -- bursts
   separated by more than the timeout, so the timer actually fires. The `gap`
   dial on the generators does this; `page_tr_init` sets the timeout.
2. **adapt_access** needs rows with STABLE, DIFFERING reuse -- some touched
   once, some many times, repeatedly, so the counters can converge to different
   verdicts per row. `hotcold_scenarios()` ([[TASK-010]]) already builds
   per-generator locality variation and is the obvious starting point.
3. Read it on **thrash% and ACT/txn**, not bandwidth -- that is what exposed
   RBL's mechanism working while it lost.

If either mode shows a win on traffic built for it, that is a real result. If
neither does, they are retired on the same evidence RBL was, and
`pumice_row_pred_table` goes with them.

**Do not remove them before running that.** They cost area, not correctness,
and the measurement is cheap compared to deleting a mechanism that was never
given its workload.

## 2026-09-26: designing the traffic found four defects first

Sean: *"think deeply about the kind of address patterns that will affect the
adapt predictors and how long the streams must be. lets see if we can
specifically contrive patterns that show improvements."*

Working out what those patterns must be turned up, in order, the reasons the
measurements above could not have shown anything.

### 1. mode 4 has never adapted, on any run, ever

`PAGE_ADAPT_CFG.check_interval` resets to 0 and the RTL wraps the ENTIRE TR
adjustment in `if (check_interval_i != 0)`. `tr_min/tr_max/tr_step` reset to 0
too, and TR is clamped to `[tr_min, tr_max]` on every adjustment, so even with
the interval running TR would be pinned to 0 -- and `tr == 0 disables that
bank's timeout entirely`. On top of that the host driver had **no accessor at
all** for `PAGE_TIMEOUT_CFG`'s three range fields or for `PAGE_ADAPT_CFG`.

The shipping `adapt_time` config sets `page_tr_init=24` and nothing else, so
every "adapt_time is identical to open page" row in the table above was
measuring `fixed_open(24)` wearing mode 4's name. This is the same defect
class as RBL's `reset_interval=0` ([[TASK-011]]): a mode whose adaptation is
switched off by its own reset values, measured as if it were running.

Fixed: `set_page_timeout_cfg()` and `set_page_adapt_cfg()` added to the
driver, `page_tr_{min,max,step}` and `page_adapt` added to `ControllerConfig`,
and a config (`adapt_time_tuned`) that actually turns the mechanism on.

### 2. mode 4 CANNOT express per-bank adaptation -- policy_scope=0 is a fiction

The obvious contrivance for a timeout predictor is heterogeneous traffic
across banks: streaming banks want a long TR, row-walking banks a short one,
and per-bank TR should beat any single fixed value. `policy_scope=0` is
documented as "per-bank TR" and the storage IS per-bank (`r_tr[NUM_BANKS]`).

It cannot work. `r_mc` is **one global signed counter**, and the adjust loop
applies that single decision to every `r_tr[b]`:

```systemverilog
logic signed [4:0] r_mc;                      // ONE counter, not per bank
...
for (int b = 0; b < NUM_BANKS; b++) begin
    if (r_mc > mc_high_thr_i)      tr_n = r_tr[b] + tr_step_i;
    else if (r_mc < mc_low_thr_i)  tr_n = r_tr[b] - tr_step_i;
    r_tr[b] <= tr_n;
end
```

Every `r_tr[b]` starts at `tr_init` and moves on the same global signal, so by
induction all eight hold identical values for all time. No across-banks
stimulus can ever show a difference. **The per-bank contrivance is ruled out
by construction, not by measurement** -- which is worth more than a null
result, because it says not to go looking.

What is left for mode 4 is temporal: converge on the right TR without being
told it. That is measured against a fixed-TR LADDER (`fixed_open_tr{2..64}`),
best-per-workload, not against one fixed point -- profile `adapt_tr`.

### 3. the hot/cold workload's cold generator emitted ONE ADDRESS

The stimulus [[TASK-010]] built for exactly this purpose was broken. Under
`placement="same_bank"` the confinement mask was `bank_stride - 1` = 0x7FF,
and the cold generator is `col_major` with stride `row_stride_same_bank` =
0x4000. The hardware masks the OFFSET before adding base (`dma_address_gen`:
`offset = (i*stride) & wrap_mask`), and `0x4000 & 0x7FF == 0`, so **every
index mapped to the base address**. The "walker" never walked; four rows were
in play instead of eleven.

The mask looked like the obvious way to say "stay in this bank" and cannot be:
on this geometry the bank bits sit BETWEEN the column and row bits
(col `[10:0]`, bank `[13:11]`, row `[14+]`), so "one bank" is not a contiguous
low-order field and no AND-mask expresses it. What an AND-mask CAN express is
a bounded row walk that leaves the bank bits alone --
`rows * row_stride_same_bank - 1`.

Fixed as `confine_mask()`, which picks the mask from the stride's granularity
and is now used by BOTH `same_bank` and `banks` placement. The rule it
encodes: **a wrap mask finer than the stride collapses the walk onto the
base.** All four families now walk; `col_interleave` still crosses banks,
which is that family.

Blast radius: `placement="banks"` has the same collapse and is used by
`bin/bank_gap_sweep.py` for `col_major`. The confinement was introduced
2026-09-22 (`6cac8cb83`, which merged that script's local measurement path
into `measure_concurrent`); PUMICE-036's "col_major flat, DRAM-bound" knees
are dated 2026-09-14 and so PREDATE the bug and stand. **Any re-run of that
sweep since 2026-09-22 is poisoned** and must be repeated.

### 4. mode 5 needed no config fix at all

`ctr_init=0` in the shipping `adapt_access` config does NOT mean strong-open-0:
the RTL reads `ctr_init_i == 0 || > 3` as "use the build default", which is
`2'b01`, weak open. With `ctr_open_max=2` that is already the fastest-
converging setting. Mode 5 was configured correctly the whole time and was
starved of stimulus by defect 3.

## How long the streams must be

| mode | what must converge | cost | verdict at txn_scale=1000 (8000 txn/gen) |
|---|---|---|---|
| 5 adapt_access | one 2-bit counter per distinct row, from `ctr_init=1` | **1 activation per row**: a cold row serves <=1 column op -> `++` -> 2 -> closes; a hot row serves many -> `--` -> 0 -> holds | ~11 activations to train the whole table out of ~1000 per row. Trains in the first 0.1% of the run. Even txn_scale=10 suffices |
| 4 adapt_time | global TR walking `[2,64]` in steps of 4 | 14 steps x `check_interval` = **~14,336 cycles** at interval 1024 | a single stream is ~70,000 cycles, so ~5 traversals -- adequate. **At txn_scale=1 it is ~70 cycles, a factor of ~200 short: the adjust path NEVER FIRES in sim.** A sim pass proves the config programs, not that the mode adapts |

Consequence: mode 4's verdict can only come from the board.
`adapt_time_fast` (check_interval=4) exists so the adjust path can at least be
exercised where a waveform can be read; it is not a configuration to quote
numbers from.

**And a second, independent reason, which applies to BOTH modes.** The sim runs
against a DFI loopback (DFISlavePHY + MemoryModel, no a7ddrphy) that does not
model DDR2 page timing at all, so every family moves identical data in
identical time there. **No paging policy can show a bandwidth difference in
sim, by construction** -- not mode 4, not mode 5, not close_page. So the sim
gate here proves the stimulus is well-formed, the configs program and the
records come back intact; it is not and cannot be the experiment.

What sim CAN check is the COMMAND TELEMETRY. `PAGE_STATS_{HIT,MISS,EMPTY}`,
`SCHED_STATS_ACT` and the PRE count tally commands ISSUED, and the address
pattern changes those whether or not the PHY charges for them. That is the
in-sim evidence that defect 3 is really fixed: the cold generator's ACT and
page-miss counts should jump now that it visits eight rows instead of one.

## The contrived patterns

**Mode 5 -- `adapt_rowmix` / `adapt_rowmix_2x2`.** N generators on ONE bank:
some streaming inside a single row (many column ops per activation -> hold
open), the rest walking disjoint 8-row windows one burst per row (exactly one
column op per activation -> close on sight). open_page gets the hot rows right
and pays a precharge on every cold ACT; close_page gets the cold rows right
and pays an ACT on every hot burst. **Mode 5 is the only policy that can get
both classes right, so the bar is beating BOTH.**

Two ratios, deliberately: 3:1 (`adapt_rowmix`) hands open_page most of the
traffic before a predictor runs, so mode 5 starts behind; 2:2
(`adapt_rowmix_2x2`) should bring open and close page near a tie, which is the
condition under which "beats both" is unambiguous. If mode 5 wins at 2:2 and
not at 3:1, the honest finding is that it needs a cold-heavy mix.

Row budgeting matters and is now enforced: generators get the span they
actually use (1 row for a streamer, `same_bank_rows` for a walker) rather than
a fixed one-row pitch, because two cold engines on overlapping windows give a
shared row TWO column ops per activation -- which the table then classifies
OPEN, the exact opposite of what a cold row is.

Aliasing is bounded: the table XOR-folds the row to 6 bits, which is the
IDENTITY below row 64. At `same_bank_rows=8` the 2:2 mix tops out at row 17,
so every distinct row is a distinct entry. Past ~61 cold rows start folding
onto the hot ones and corrupt exactly the discrimination being measured.

**Prediction (recorded before the run):** `adapt_access` > `open_page` >
`close_page`. A cold access under open page costs PRE + tRP + ACT + tRCD + RD;
under mode 5 the precharge rides the previous burst as an auto-precharge, so
it saves ~tRP per cold access on roughly the cold share of cycles. If
`adapt_access` comes back within +-0.2 MB/s of `open_page` AGAIN, on stimulus
that is now verified to discriminate, that is the retirement evidence.

## 2026-09-26 sim: defect 5, and the first evidence mode 4 works

Sim, txn_scale=1, DFI loopback. Command telemetry only -- the loopback charges
nothing for page management, so MB/s is not a verdict here and is not quoted.

### 5. mode 5 cannot vote close at ANY address pattern -- the BURST is the gate

First run of `adapt_rowmix` came back with `adapt_access` **bit-identical to
open_page** (ACT=32, miss=32, PRE=32) on stimulus whose address walk had just
been verified correct. The counters explain it in one line:

    col_ops=128   ACT=32     -> exactly 4 column ops per activation

The mode-5 table votes a row closed only when an activation served **<= 1
column op**; at >= 2 it decrements toward open. A DRAM column op moves 16 B on
this geometry, so the suite's default AXI `blen=8` (64 B) is FOUR column ops
*inside one row*. Every activation -- hot and cold alike -- served 4, every
counter decremented, and every row voted OPEN.

**No address pattern whatsoever can make mode 5 vote close while the burst is
longer than one column op.** Defect 3 (the collapsed cold walk) was necessary
to fix and not sufficient; the binding parameter is the burst length, not the
stride. This is why every campaign to date found mode 5 inert: the suite has
always run blen>=4.

Fixed as `cold_blen` (default 2 = 16 B = exactly one column op), applied to the
COLD generators only -- hot generators are supposed to serve many column ops
per activation and keep the caller's burst. A short scattered burst is not a
setting chosen to flatter the mode; it IS the access pattern a close-on-sight
predictor exists to catch.

### mode 4 demonstrably adapts -- and lands on the ladder's optimum

`adapt_tr`, col_major_bl8 (the page-hostile family), command counts:

| config | ACT | miss | empty | thrash |
|---|---|---|---|---|
| open_page | 8 | 8 | 0 | 100% |
| fixed_open_tr2 | 8 | 7 | 1 | 87.5% (PRE=15 -- re-precharging) |
| **fixed_open_tr4** | 8 | 0 | 8 | **0%** <- unique fixed optimum |
| fixed_open_tr8 (= adapt's tr_init) | 8 | 7 | 1 | 87.5% |
| fixed_open_tr16 / 32 / 64 | 8 | 7 | 1 | 87.5% |
| **adapt_time_tuned** | 8 | 0 | 8 | **0%** |
| close_page | 32 | 0 | 32 | 0% (at 4x the ACTs) |

**TR provably moved**, without needing a readback register. The ONLY difference
between MODE_FIXED_OPEN and MODE_ADAPT_TIME in `pumice_page_policy.sv` is
`f_tr()` returning `tr_init_i` versus `r_tr[b]`; the mistake counter has no
output effect until an adjustment fires. So if TR had stayed at its tr_init,
`adapt_time_tuned` would be bit-identical to `fixed_open_tr8`. It is not.
Therefore TR moved -- and it moved to the TR=4 behaviour, one `tr_step` down,
the direction MC drives on "held too long".

That is the temporal win the ladder exists to test: one config, not told the
answer, reaching the per-workload optimum that its own starting value misses.

**Caveats, so this is not over-read.** txn_scale=1 is 32 column ops, a tiny
sample. `r_check_cnt` free-runs whenever the mode is on, so the intervals
between adjustments here include host CSR idle time, and the traffic-to-idle
ratio on the board at txn_scale=1000 is nothing like this. The trajectory is
inferred from the endpoint, not observed -- there is no TR readback (worth
adding: a stat register for `r_tr[0]` would make this directly checkable rather
than deduced).

### the stimulus itself is working

Every config shows `ACT = 32` = one activation per transaction, hot generators
included. That is the hot/cold conflict doing its job: four engines
round-robining on one bank evict each other's row before any of them returns.

### 6. one bank measures mode 5 where its mechanism cannot pay

`bank_timer.sv`: *"auto-precharge fires once the read/write recovery (preblk)
AND tRAS elapse"* -- the AP path waits tRAS exactly like an explicit precharge.
So on a single bank the ACT -> PRE -> ACT chain binds at tRAS + tRP either way
and mode 5 can only save the command-bus SLOT -- while a lone active bank is
precisely the case where the command bus is not contended.

Auto-precharge pays when precharges COMPETE for issue slots against other
banks' commands. `bank_spread` replicates the hot/cold group onto N banks: each
still holds one open row with a streamer and a walker fighting over it, and now
the precharges those conflicts generate contend for the bus.
`adapt_rowmix_2bank` is 2 groups x (1 hot + 1 cold), the widest this stimulus
goes -- `char_gen_unit` has NUM_GEN=4.

## RESULT: mode 5 discriminates, on stimulus built for it

Same profile, same scale, after `cold_blen=2`. 2 hot : 2 cold, one bank:

| config | ACT | miss | empty | thrash | PRE |
|---|---|---|---|---|---|
| open_page | 25 | 25 | 0 | 100.0% | 25 |
| **adapt_access** | **25** | 10 | **15** | **40.0%** | **9** |
| close_page | 82 | 2 | 80 | 2.4% | 4 |

And spread over two banks (`adapt_rowmix_2bank`):

| config | ACT | miss | empty | thrash | PRE |
|---|---|---|---|---|---|
| open_page | 28 | 28 | 0 | 100.0% | 28 |
| **adapt_access** | 26 | 12 | **14** | **46.2%** | **11** |
| close_page | 81 | 1 | 80 | 1.2% | 2 |

**This is the best-of-both the mode is designed for, and the first time it has
ever been observed.** adapt_access holds open_page's activation count (25, not
close_page's 82) while converting 15 of those 25 activations from conflict-MISS
to EMPTY: the cold rows are closed on sight, so the next activation finds the
bank closed instead of holding the wrong row. Explicit precharges fall 25 -> 9
because those closes ride the column op as auto-precharge -- 16 command-bus
slots freed.

Every earlier "adapt_access is inert" result stands explained: defect 3 gave it
no row variation to learn from, and defect 5 meant it could not have voted
close even with perfect variation.

**What this is NOT.** It is not a bandwidth result. The loopback charges
nothing for page management, so the saved precharges and avoided conflicts cost
zero here by construction. Whether 100% -> 40% thrash and 16 freed slots turn
into MB/s is a board question, and the prediction on record is
`adapt_access` > `open_page` > `close_page`.

Note the two-bank variant is not clearly ahead of the one-bank variant in
telemetry (46.2% vs 40.0% thrash), and should not be expected to be: its whole
argument is command-bus SLOT CONTENTION, which is a timing effect the loopback
cannot price. Both go to the board; if the two-bank case does not beat the
one-bank case there, the bank_spread rationale (defect 6) is wrong and should
be recorded as such.

## Board plan

| profile | question it answers |
|---|---|
| `adapt_rowmix`, `adapt_rowmix_2x2` | does mode 5's thrash reduction become bandwidth, and does it beat BOTH fixed policies |
| `adapt_rowmix_2bank` | does command-bus slot pressure add to that (tests defect 6's reasoning) |
| `adapt_tr` | does one adapt_time config match the best fixed_open_tr per family, without retuning |

txn_scale=1000. Read thrash%, ACT/txn and PRE/txn beside MB/s -- the mechanism
and the payoff are separate claims and RBL is the example of the first arriving
without the second.

## BOARD RESULT 2026-09-26: the win is real, the predictors are not

Board, txn_scale=1000, 75.00 MHz read off BUILD_CLK_HZ, peak 600 MB/s.
Read bandwidth, all stimuli from the contrived set:

| stimulus | open_page | close_page | adapt_access | adapt_time_tuned |
|---|---|---|---|---|
| 3:1, one bank | 205.9 | 55.4 | 203.9 (-1.0%) | 228.1 (+10.8%) |
| 2:2, one bank | 221.2 | 72.1 | 221.2 (0.0%) | 245.7 (+11.1%) |
| 2:2, two banks | 327.7 | 144.2 | 323.8 (-1.2%) | 436.8 (+33.3%) |

### mode 5 (adapt_access): does not pay, and barely engages

Flat to -1.2% on every stimulus. The telemetry says why: thrash 100.0% ->
97.0%, PRE 32797 -> 32567 -- about 230 converted closes out of ~16,000 cold
activations, roughly 3%, where the same stimulus in sim converted 60%. The
mechanism that sim showed working does not reproduce at scale on hardware, and
the cause is NOT yet known. That gap is the remaining open question here; do
not retire mode 5 on this alone, because the sim/board divergence is itself
unexplained and an unexplained divergence is a bug somewhere, not a verdict.

**Prediction on record, falsified.** This task predicted
`adapt_access > open_page > close_page`. It is not.

### mode 4 (adapt_time): the win is real and the ADAPTATION is not

adapt_time_tuned is genuinely faster -- +10.8% to +33.3% over open page, with
a visible mechanism (2-bank: thrash 100.0% -> 25.8% while issuing MORE
precharges, 40800 vs 32797, i.e. closes moved off the critical path; blocked
cycles 642k -> 526k). That is a real result.

It is not adaptation. Two controls settle it.

**Control 1 -- the fixed-TR ladder on the same stimulus** (`adapt_rowmix_2bank_tr`):

| config | rd MB/s | vs open |
|---|---|---|
| adapt_time_tuned | 436.8 | +33.3% |
| **fixed_open_tr2** | **436.8** | **+33.3%** |
| fixed_open_tr4 | 368.6 | +12.5% |
| fixed_open_tr8 | 338.5 | +3.3% |
| fixed_open_tr16 / 32 / 64 | 327.7 | +0.0% |

adapt lands EXACTLY on fixed_open_tr2 -- and tr_min is 2.

**Control 2 -- move only the floor** (`adapt_floor`). If adapt tracked the
workload, the floor would not matter; if it decays to the floor, it tracks it:

| config | tr_min | rd MB/s | matches |
|---|---|---|---|
| adapt_time_tuned | 2 | 436.8 | fixed_open_tr2 = 436.8 |
| adapt_time_floor8 | 8 | 338.5 | fixed_open_tr8 = 338.5 |
| adapt_time_floor16 | 16 | 327.7 | fixed_open_tr16 = 327.7 |

**adapt_time == fixed_open(tr_min), exactly, in all three.** MC is dominated by
"held too long" (a conflict PRE on a bank whose timer had not expired), so TR
shrinks monotonically to tr_min and stays. The mistake counter, check_interval,
tr_max and tr_step earn NOTHING measurable. Mode 4 is subsumed by mode 3 at
TR=tr_min -- the same verdict class RBL's mode 7 got (bit-identical to open
page), reached the same way: by controlling for the simple mechanism before
crediting the complicated one.

Note this also explains `adapt_tr`'s plain-family result, where
fixed_open_tr2 matched adapt on row_major, col_major AND incremental. One
number, three families, no learning: it was the floor every time.

### THE ACTUAL FINDING, which is worth shipping

**A short fixed page timeout beats open page by +9.1% to +33.3%.**
`fixed_open` at TR=2 is mode 3 -- no predictor table, no mistake counter, no
epoch machinery -- and it equals the best adaptive result on every workload
measured:

| stimulus | open_page | fixed_open_tr2 | gain |
|---|---|---|---|
| col_major (sequential) | 195.2 | 212.9 | +9.1% |
| hotcold 2:2 two banks | 327.7 | 436.8 | +33.3% |
| row_major / incremental | 572.0 / 561.1 | 571.8 / 561.1 | ~0% (nothing to fix) |

It costs nothing on the page-friendly families and wins big on the
page-hostile ones. That is the shippable result of this task.

## Where this leaves modes 4 and 5

| mode | verdict | evidence |
|---|---|---|
| 4 adapt_time | **subsumed by mode 3** at TR=tr_min; adaptation earns nothing | two controls, exact equality at three different floors |
| 5 adapt_access | no bandwidth benefit, and engages 20x less on board than in sim | 3 stimuli; the sim/board divergence is UNEXPLAINED |

Recommend: default the board to `fixed_open` TR=2 rather than open page.
Do NOT retire mode 5 yet -- the unexplained sim/board divergence must be
understood first, because it may be a defect in the predictor's hardware path
rather than a verdict on the idea. Mode 4's retirement is better supported, but
its timeout PATH is exactly what mode 3 provides, so retiring mode 4 costs
nothing functional.

Still missing, and cheap: a stat register exposing `r_tr[0]`. Both controls
above had to infer TR from bandwidth equality. A readback would have shown the
decay directly in one run instead of three.

## Is mode 5's sim/board divergence a REFRESH artefact? No.

Sean asked, 2026-09-26, and it was a good hypothesis: the refresh PRESSURE
differs by 117x between the two environments.

    sim    REF=74   vs ACT=26      -> 2.85 refreshes per activation
    board  REF=810  vs ACT=33427   -> 0.024 refreshes per activation

A refresh drains every bank with PREA. PREA does not teach the counter
(learning is gated on `w_is_pre == OP_PRE`), but it DOES claim the fall
(`w_pre_claims[b] = (w_is_pre && bank==b) || w_is_prea`), suppressing
auto-precharge-close detection, and it leaves every bank closed so the next ACT
reads EMPTY rather than MISS. At 2.85 refreshes per activation that is not a
correction on the measurement, it could BE the measurement.

Tested on the board (`adapt_refresh`), varying ONLY t_refi:

| config | REF | rd MB/s | ACT | PRE | thrash |
|---|---|---|---|---|---|
| open_page | 800 | 327.6 | 32798 | 32799 | 100.0% |
| adapt_access | 809 | 323.8 | 33334 | 32382 | 97.0% |
| open_page_fastref | 1883 | 317.5 | 33882 | 33882 | 100.0% |
| adapt_access_fastref | 1882 | 317.5 | 33882 | 33882 | 100.0% |
| adapt_access_slowref | 13 | 342.6 | 32009 | 32013 | 100.0% |

**The hypothesis predicts the opposite of what happens.** More refreshes should
mean more conversion; instead mode 5 goes to ZERO at high refresh and is also
inert at near-zero refresh. Its only engagement (3%) is at the DEFAULT rate, in
the middle. Non-monotonic, zero at both extremes: not a refresh effect.

Two things the experiment did find:

1. **`adapt_access_fastref` is BIT-IDENTICAL to `open_page_fastref`** -- same
   ACT (33882), same PRE (33882), same thrash, same 317.5 MB/s. That is the
   RBL mode-7 signature: a mode provably contributing nothing.
2. At near-zero refresh, `PRE=32013 ~= ACT=32009` -- every close is an explicit
   precharge, so `close_pred_o` is never asserted at all.

Together these say mode 5's prediction rarely survives to be USED on hardware,
rather than that it learns the wrong verdict. The next probe should be
`close_pred_o` itself (is it ever asserted? for how long?), not the counters --
`close_pred_o[b] <= 1'b0` on EVERY fall, so a prediction cleared on close and
re-established only at the next ACT may simply not be live when the column op
issues. There is no readback for it today, which is the second argument for a
predictor-state stat register.

Incidental: slow_refresh is the fastest config here at 342.6 MB/s, so refresh
costs ~4.4% on this stimulus (327.6 -> 342.6).

## Mode 5 localized: the AP datapath works, close_pred_o does not assert

Two more board experiments, no RTL change needed.

### It is not run length -- matched scale, opposite behaviour

`adapt_rowmix_2bank` swept on the board:

| txn_scale | ACT | PRE | thrash | engaged |
|---|---|---|---|---|
| 1 | 32 | 32 | 100.0% | 0% |
| 10 | 326 | 329 | 100.0% | 0% |
| 100 | 3335 | 3240 | 97.0% | 3% |
| 1000 | 33338 | 32385 | 97.0% | 3% |

Sim at txn_scale=1 on this same stimulus converted 14 of 26 activations (54%).
**The board at txn_scale=1 converts ZERO.** So the earlier "60% in sim vs 3% on
board" was not a learning-window or steady-state effect -- at matched scale the
two environments do the OPPOSITE thing. Board engagement saturates at 3% from
scale 100 and never improves.

### The auto-precharge datapath is PROVEN GOOD on hardware

**CORRECTED 2026-09-26, and the first version of this argument was wrong.**
Sean: *"Isn't there a separate config bit to turn off AP?"* There is, and it is
the bit `close_page` actually uses.

There are TWO independent auto-precharge controls:

| control | written by | effect |
|---|---|---|
| `PAGE_POLICY_CFG.page_policy_or` (legacy open/close) | `set_page_policy()` | CLOSE turns on the legacy `w_ap` path |
| `policy_mode` + `ap_mode_en_o` | `set_page_mode()` | any mode 1..5 sets `ap_mode_en_o=1`, and `ap_close_o` then OVERRIDES the legacy path |

`close_page` is `page_policy=CLOSE` with **`page_mode=None` -> mode 0**. Mode 0
is not in `w_mode_on`, so `ap_mode_en_o=0` and `ap_close_o='0`: **close_page
never exercises `ap_close_o` at all.** Its auto-precharge is entirely the legacy
`w_ap` path. The original claim here -- "close_page is MODE_STATIC_CLOSE, so the
port the predictor drives is proven good" -- was proven about the WRONG PATH.
`ap_close_o` had never been driven on hardware by anything: no config set
policy_mode=2, and mode 5's close_pred_o does not assert.

Tested properly with `static_close_mode2` (`page_policy=OPEN` so the legacy path
is off, `policy_mode=2` so `ap_close_o={all 1}` -- any AP behaviour can only come
from `ap_close_o`):

| config | AP source | rd MB/s | ACT | PRE | thrash | rd_lat |
|---|---|---|---|---|---|---|
| open_page | none | 327.6 | 32800 | 32800 | 100.0% | 100.8 |
| close_page | legacy `w_ap` | 144.1 | 160018 | 36 | 0.0% | 192.1 |
| **static_close_mode2** | **`ap_close_o`** | 144.1 | 160002 | 2 | 0.0% | 192.0 |
| adapt_access | `ap_close_o` via close_pred_o | 323.8 | 33334 | 32382 | 97.0% | 96.8 |

`ap_close_o` driven all-ones is INDISTINGUISHABLE from the legacy path (144.1
MB/s, ~160k ACT, PRE ~0 both). So the port works, the scheduler honours it, and
the DFI path carries it.

Two consequences. The conclusion below (mode 5's fault is `close_pred_o`) SURVIVES
and is now properly evidenced rather than accidentally so. And this is the first
time mode 2 has ever been measured -- `close_page`, the config named for it, is a
different mechanism.

`adapt_access` drives that same proven-good port from `w_acc_close`/`close_pred_o`
and returns `PRE ~= ACT`.

**So the AP mechanism, the scheduler's ap handling and the DFI path are all
fine. `close_pred_o` is simply not asserting.** The fault is inside
`pumice_row_pred_table`, not anywhere downstream of it, and mode 5 should NOT
be retired as a bad idea -- it has never actually run on hardware.

### Where to look, in order

1. `close_pred_o[b] <= 1'b0` on EVERY fall, re-established only at the next ACT.
   Under real tRCD/tRAS the column op may issue in a window where the verdict
   is not yet live, so the bit is correct and simply never sampled.
2. `r_col_cnt` reset discipline. Learning compares `r_col_cnt <= 2'd1` at the
   explicit PRE; if the count does not clear per activation on hardware timing,
   every row looks like a multi-access row and votes OPEN forever -- which is
   exactly the observed `PRE ~= ACT`.
3. The `w_fall` claim window is ONE cycle ("a PRE to the bank at the fall cycle
   or the next one"). That window was tuned against loopback timing; on the
   board the PRE can lag the fall by more, which would misclassify explicit
   closes as auto-precharge closes and suppress learning entirely.

(1) and (3) are both "a timing assumption that holds in the loopback and not on
the board", which is the shape of every sim/board divergence in this controller
so far.

Blocked on observability: there is no readback for `close_pred_o` or
`r_col_cnt`. That is now the THIRD investigation forced to infer predictor state
from bandwidth equality (after mode 4's TR decay and the refresh test). A small
stat block -- `close_pred_o` assert count, AP-close count, `r_tr[0]` -- would
have answered all three directly and is the recommended next change.

## The mechanism, not the predictor: AP costs 4.9x the activations

Sean, 2026-09-26: *"I wouldn't expect auto-precharge to be very performant. Is
this what the adapt* are using?"*

**Only mode 5 uses it, and mode 4 explicitly forces it OFF.**

```systemverilog
assign ap_close_o = (policy_mode_i == MODE_STATIC_CLOSE) ? {NUM_BANKS{1'b1}}
                  : w_acc_on                             ? w_acc_close
                                                         : '0;
```

| mode | close mechanism |
|---|---|
| 2 static_close (close_page) | auto-precharge, unconditional |
| 5 adapt_access | auto-precharge, gated by close_pred_o |
| 3 fixed_open / 4 adapt_time | `ap_close_o='0` -> background explicit PRE (timeout_pre_req_o) |

That maps exactly onto every result in this task: the background-PRE modes win,
the AP mode does nothing, the all-AP mode is catastrophic.

Mechanism isolated on the board (`ap_vs_bgpre`), same stimulus, same
close-on-sight policy, differing only in HOW the row is closed:

| config | mechanism | rd MB/s | ACT | PRE | thrash | rd_lat |
|---|---|---|---|---|---|---|
| open_page | none | 327.7 | 32794 | 32796 | 100.0% | 100.7 |
| close_page | AP, always | 144.1 | **160006** | 8 | 0.0% | 192.0 |
| fixed_open_tr1 | bg PRE, ~always | **436.8** | **32400** | 40400 | 24.7% | 96.0 |
| fixed_open_tr2 | bg PRE, 2-cyc grace | 436.8 | 32600 | 40800 | 25.8% | 96.0 |
| adapt_access | AP, predicted | 323.8 | 33429 | 32570 | 97.0% | 96.7 |

**Auto-precharge costs 4.9x the activations for identical traffic** -- 160,006
vs 32,400, about five activations per transaction -- and latency 192.0 vs 96.0.
Confirmed on BOTH AP paths independently: the legacy `w_ap` route (close_page,
160,018 ACT) and the `ap_close_o` route (static_close_mode2, 160,002 ACT) land
on the same number, so this is a property of auto-precharge itself and not of
one implementation of it.

### Why: AP is UNCANCELLABLE

AP commits to closing at the column op, before it is known whether more requests
to that row are coming. A background PRE fires only once the bank goes IDLE, and
if more same-row requests are pending the bank is not idle, so the row survives
and serves them. **The idle gate is an implicit cancellation, and that is the
entire difference.** On a controller whose value is FR-FCFS reordering to batch
same-row columns ([[TASK-002]]: worth 3.9x on streaming), AP destroys the row
before the batching can happen -- it fights the reordering that justifies the
design.

Corroboration: `fixed_open_tr1` and `fixed_open_tr2` are IDENTICAL (436.8 both),
so the grace period contributes nothing. The idle gate alone does the work.

### Consequence for mode 5 -- bigger than the close_pred_o bug

The previous section localized mode 5's failure to `close_pred_o` never
asserting. That stands, but it is no longer the main point: **even with
close_pred_o fixed, mode 5 would apply a mechanism that costs 4.9x the
activations.** Fixing the bug would make mode 5 apply a bad mechanism more
selectively, which is a smaller win than it sounds -- its ceiling is bounded by
AP, and AP is structurally wrong for a reordering controller.

**Recommendation: re-route mode 5's per-row verdict to the BACKGROUND PRECHARGE
path, not the AP path.** `close_pred_o` should raise `timeout_pre_req_o` for a
predicted-dead row (close it as soon as the bank idles, without waiting out TR)
instead of driving `ap_close_o`. That keeps the idle-gate cancellation that makes
mode 3 fast while adding the per-row selectivity mode 5 was built for. It is the
only version of mode 5 that could beat `fixed_open`.

### Revised standing of the whole page-policy axis

| mode | verdict |
|---|---|
| 3 fixed_open | **THE WIN.** TR=1 or 2, background PRE gated on bank idle. +9.1% to +33.3% |
| 4 adapt_time | same mechanism as 3; adaptation adds nothing (decays to tr_min) |
| 5 adapt_access | right idea, WRONG MECHANISM (AP) plus a bug (close_pred_o). Needs rework, not retirement |
| 2 static_close | the AP mechanism at full strength, and 2.3x slower than open page |

The one-line summary of this task: **closing pages early is worth up to +33%,
and the mechanism that matters is a background precharge gated on bank idle --
not a predictor, and not auto-precharge.**

## fixed_open TR=2 is safe as a DEFAULT: zero regressions on the full grid

The +9.1% to +33.3% result was taken on contrived hot/cold stimulus plus three
plain families. That is not enough to change a shipping default, where the
question is not "does it win" but **"does it ever lose"**. Swept the full family
grid at MEDIUM (three burst lengths, gap and multi-id variants) on the board,
txn_scale=1000, peak 600 MB/s:

| scenario | open_page | tr1 | tr2 | tr4 | tr2 vs open |
|---|---|---|---|---|---|
| incremental_bl4 / bl8 / bl16 | 561.6 | 561.6 | 561.6 | 561.6 | 0.0% |
| row_major_bl4 / bl8 / bl16 | 572.2-572.3 | = | = | = | 0.0% |
| col_major_bl4 | 114.7 | 128.0 | 128.0 | 114.7 | **+11.6%** |
| col_major_bl8 | 195.2 | 213.0 | 213.0 | 195.2 | +9.1% |
| col_major_bl16 | 286.7 | 311.2 | 311.3 | 286.7 | +8.6% |
| col_major_interleaved_bl4 | 249.5 | 352.2 | 352.2 | 353.1 | **+41.2%** |
| col_major_interleaved_bl8 | 262.1 | 354.2 | 354.2 | 354.3 | +35.2% |
| col_major_interleaved_bl16 | 364.5 | 438.2 | 438.2 | 438.2 | +20.2% |
| col_major_bl8_multiid | 195.2 | 213.0 | 213.0 | 195.2 | +9.1% |
| col_major_bl8_gap | 195.2 | 213.0 | 213.0 | 195.2 | +9.1% |

**Worst case -0.0% (rounding). No scenario regresses. Zero integrity failures.**

Three things this adds beyond the contrived result:

1. **col_major_interleaved is the biggest win in the whole campaign, +41.2%**,
   and it was not measured before this sweep. The bank-interleaved walk gains
   most from closing early -- it touches every bank in turn, so a row left open
   is a row that will certainly conflict before it is ever revisited.
2. **TR=2 is a sweet spot, not just a working point.** tr1 is identical to tr2
   everywhere, and tr4 misses the plain col_major wins entirely (114.7 / 195.2
   / 286.7 -- exactly open_page) while still getting the interleaved ones. The
   optimum is 1..2 and the cliff is between 2 and 4.
3. **Page-friendly families are EXACTLY flat**, not merely "close": 561.6 and
   572.2-572.3 to the tenth on every burst length. Closing early costs nothing
   where there is nothing to close, because the idle gate never fires when the
   next request is already queued for the open row.

**Recommendation: change the shipping default from open page to fixed_open
TR=2** (PAGE_POLICY_CFG.policy_mode=3, PAGE_TIMEOUT_CFG.tr_init=2). It is
strictly dominant across every scenario measured, costs no area (mode 3 is the
timeout path that already exists for mode 4), and needs no predictor.

That is an owner's decision, not mine to land: it changes a CSR reset value, so
it wants the RDL change, the regenerate, and the docs sync in one pass
([[feedback_docs_sync_with_config]] -- docs sync with configs, always).

Related: [[TASK-011]] (RBL, the worked example), [[TASK-010]] (the
per-generator scenario machinery), [[TASK-005]] (predictor area),
[[TASK-002]] (FR-FCFS reordering value).
