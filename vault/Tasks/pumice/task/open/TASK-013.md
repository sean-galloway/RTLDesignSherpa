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

Related: [[TASK-011]] (RBL, the worked example), [[TASK-010]] (the
per-generator scenario machinery), [[TASK-005]] (predictor area).
