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

## Bank preparation: the row command rides inside the column's dead time (TASK-045)

Column-first class priority is the textbook FR-FCFS order, and it is free
exactly when the command bus has slack: a burst occupies several command
slots, the next column is eligible only every tCCD, and a ready ACT or PRE
for another bank fits in the slots between. At the board geometry (BL4 on
x16 over DFI 1:2, one command per 75 MHz cycle) one column per cycle fills
the data bus AND the command slot, tCCD is 1, and column-first holds every
row command behind the stream: the next bank's ACT waited for the run to
end and tRCD was paid in the open on every row switch. Measured on the
bank-interleaved family: 12 command slots per 8-column row (ACT, tRCD
bubble, 8 columns, close, tRP bubble) against the 9 a prepared bank needs;
383 vs 455 MB/s one thread, 469 vs 502 eight threads.

The rule that fixes it is the per-bank core's alternation, not row_first:
after a column, a ready row command takes the slot; after a row command,
columns; with one class pending the other falls through. A row command
then follows the column that just fired, inside that column's own tCCD, so
no column ever loses its ELIGIBLE slot -- which is what row_first does
("one slot in five", TASK-002, the ACT lands on the cycle the next column
becomes eligible). At tCCD >= 2 the alternation and column-first measure
the same, because the ACT was already landing in the dead time.

**The trap underneath it.** The close-on-drain candidate was the
age-YOUNGEST same-row column, which is the last one only while the column
pick runs strictly oldest-first. Once a row command can interpose, the
column sitting in the pre-pick register is not consumed; its slot is masked
as in flight at classify, so the STAGE-1b selection is already the next
column, and the reload drops the held one back to classify for a two-cycle
round trip. It re-issues behind its younger sibling: the candidate fires
with a sibling still in the window (correctly demoted) and the true last
column carries no flag. 61 of 128 read rows stayed open and were closed by
a demand PRE two slots later. Holding the pre-pick column did NOT fix it:
the 1b selection it refused was masked all the same, so the hole moved one
stage up (115 rows). What fixed it was letting the fire stage OWN the
close: a column with no same-(bank,row) entry anywhere in the live window,
valid or pending, either direction, on a bank the page policy has armed,
closes -- the same predicate the candidate approximated, evaluated once
where the live data is (`w_ap_last`, promote as well as demote). A proxy
for a live predicate is only as good as the ordering assumption under it.

Checked on the isolated core bench (`test_pumice_core_bankprep.py`, 40 s a
run, cycles per row and explicit PREs per phase, plus a per-cycle arbiter
trace that lists the same-row siblings the fire stage sees), then on the
proxy. The bench, not the proxy, is where the mechanism was found: the
proxy run is seven minutes and sees bandwidth; the bench sees the slot.

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
4. Any "last of" / "youngest" proxy used to make an irreversible decision
   (an auto-precharge, a drain) needs the live predicate at the fire stage
   too, in BOTH directions -- and a bench short enough to run the proxy's
   assumption into the ground (here: a row command interposing between two
   columns of one row).

Related: [[plane-boundary-registered-snapshots]] (why the image is
registered in the first place), [[priority-logic-depth]],
[[block-boundary-dead-cycles]] (the same "account every excess cycle"
discipline for datapaths).
