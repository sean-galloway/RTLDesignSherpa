---
title: A dependent hop classifies against the pick, not against the image
summary: In a pipelined scheduler the candidate for the next command (the column behind an ACT, the ACT behind a PRE) appears only once the bank image has moved, so every dependent hop pays the image lag plus the pipe depth. Classify it against the command being picked this cycle and make the fire stage the only authority (live row check, bounded holds). The FR-FCFS arbiter's 24-cycle row against a 13-cycle floor (pumice TASK-044, 2026-10-23).
---

# A dependent hop classifies against the pick, not against the image

**Rule:** when a scheduler pipelines its decision (classify, select, pick,
fire) and classifies against a registered image of the device (row open,
timers ready), a command that depends on the previous one -- a column on
the row an ACT is opening, an ACT on the bank a PRE is closing -- cannot be
classified from the image: the image moves only after the fire, and the
candidate then still has the whole pipe to walk. Classify the dependent hop
against the command the pipe is **picking this cycle** (and the one in the
output register, and the one fired last cycle, until the image catches up),
and make the fire stage the only JEDEC authority: it re-reads the LIVE
device state (the row must be open and equal to the column's row; the bank
must be closed before an ACT) and HOLDS a command that is waiting on a
timer whose remaining count is bounded, instead of dropping it and paying
the pipe again. A speculation whose premise never fired (the ACT was
rejected) fails the live check and is dropped there, losslessly.

## The failure that taught it

`mc_cmd_arbiter` (the FR-FCFS core) classifies pool entries against
`r_bank_row_active` / `r_bank_open_row`, which are the bank timers' flops
registered once more at the arbiter's input: two cycles behind a fire. The
pick is three registers deep (STAGE-1a mask, pre-pick, output). On
col_major, one generator, every eight-column row cost 24 cycles against a
13 / 15-cycle floor (tRTP or tWR, plus tRP, plus tRCD), traced fire by fire:

| hop | JEDEC | measured | where the cycles went |
|---|---|---|---|
| last column to PRE | tWR 4 | 6 | two cycles of re-issue guard after the column fire |
| PRE to ACT | tRP 2 | 6 | image drops two cycles after the fire, then the three-stage pipe |
| ACT to column | tRCD 2 | 5 | same: image, then pipe |

The per-bank core (`mc_bank_pick`) was built with a lookahead decode and a
next-op hint and sat on the floor; the owner's question was why it kept
winning after the multi-thread bug was fixed.

## What landed (and what each step bought, measured)

1. **Exact close-on-drain.** The arbiter's auto-precharge predicate counted
   only schedulable siblings; a write burst's entries are allocated at AW
   and filled beat by beat, so "youngest schedulable" was true of every
   streaming write that happened to be the last one landed, and the row
   closed under the burst behind it (BUG-027, which turned the feature off).
   Pending entries now count as demand (`wr_sch_pend_i`), the same predicate
   the per-bank records give the other core. Row: 24 to 21 / 19.
2. **Forward paths.** A column is a hit against the ACT in the output
   register or fired last cycle; an ACT is a candidate while its bank's PRE
   is in the output register or fired and the image has not dropped
   (`r_pre_closing`, the twin of the existing `r_ap_closing`); ACT
   candidates are guarded only against ACTs, not against the column or PRE
   they depend on. Fire stage: columns require the live row to match
   (`w_col_row_ok`) and hold for tRCD when the lookahead says it is within
   reach; ACTs hold while the bank is closed inside tRP / tRC. Row: 18 / 16.
3. **Classify against the pick itself.** The pick comb's result this cycle
   (`w_act_pick`, `w_pre_pick`) is the command loading the output register;
   three registers from classify to fire equal a two-cycle timer plus the
   fire cycle, so the hop lands exactly. Row: 15 / 13 -- the floor. One
   trap on the way: the ACT behind an auto-precharge arrived while the live
   row was still open (the device closes it tWR later), was DROPPED as
   "bank open", and re-picked at +8 instead of +6; the hold has to include
   "this bank is draining an AP".

The pick comb reads pre-pick registers and live timer bits, never the
classify outputs, so forwarding it is not a loop; Verilator's UNOPTFLAT and
the formal proof both stay clean.

## The composition that was NOT free

Exact close-on-drain still cannot see a burst whose AW has not arrived. On
the write-ceiling and read-in-flight probes (a just-in-time AXI stream) it
closed a row per burst and six BUG-027 cells failed again, milder. The
close is now armed per bank by the page policy's mistake predictor
(BUG-030): a predicted close (timeout or auto-precharge) followed by a
different row arms it, one reopened by the same row disarms it
(`drain_close_ok_o`). A closing decision belongs to the policy that owns
the evidence, not to the arbiter's view of its window.

## How to check a design against it

1. Trace fires, not bandwidth: a histogram of fire-to-fire gaps per command
   kind and the first few hundred fires in order. Each hop's excess over
   its JEDEC minimum is a named mechanism (image lag, guard, pipe stage) or
   it is not understood.
2. For each dependent hop, ask what the EARLIEST cycle is at which the
   pipeline could know the previous command will fire. If the answer is
   "when the image shows it", the hop pays the image lag.
3. Every speculation needs its fire-stage check and its drop path named;
   every hold needs a bound (which timer, how many cycles).

Related: [[plane-boundary-registered-snapshots]] (why the image is
registered in the first place), [[priority-logic-depth]],
[[block-boundary-dead-cycles]] (the same "account every excess cycle"
discipline for datapaths).
