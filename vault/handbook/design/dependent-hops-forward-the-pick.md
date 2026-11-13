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

## A second issue lane is in flight for every guard (TASK-047, 2026-11-03)

The same arbiter grew a row-only second output lane (`DUAL_ISSUE`: an ACT or
PRE in the same DFI word as a column, on its own phase). Every shadow and
forward term above answers "is a row command on this bank in flight or just
fired?", and a lane that one of them does not see re-opens the hazards they
close: the pre-pick ACT picked twice, a column classified against a row its
ACT has not opened, a refresh drain that misses an open bank. So the lane
register counts as in flight wherever the main output register does
(`w_inflight_preact`, `w_if_preact_out`, `w_act_guard`, the speculative-hit and
early-ACT terms), and its fires feed `r_guard0`, `r_actg0`, `r_actsh_*`,
`r_pre_closing` and `r_preguard0`. The lane loads at the main register's edge,
from the same pre-pick registers, so the pre-pick moves past the command it
took. The lane fires on the live image, never beside a main-lane row command
and never to the main lane's bank. The formal wrapper's `dual` task checks
that contract, and removing any one of its three fire terms fails it.

## The same lane on the per-bank pick core (memory-controllers MC-014, 2026-11-12)

`mc_bank_pick` grew the lane a week later, after the Ramulator comparison and
a slot-occupancy trace had named the single command slot as granite's ceiling
on the bank-parallel miss families (97 percent of MC cycles firing, an ACT
every 9 cycles; [[dram-cycle-model]]). The pick core has no pre-pick
registers or guard shadows to extend; what it has is one registered request
set, one effective-winner register and a stale mask, so the lane is a second
winner register fed from the same request set, and every rule of the
arbiter's lane maps onto those three things:

- *rideable* = a row request whose bank has no column request in the
  stale-masked set and is not the main winner's (the arbiter's `f2_free`),
  ACT before PRE, the age tie-break and the rotor inside the class. The main
  select treats "a row can ride" exactly as "the last fire was a row
  command" -- columns first -- so a rideable row stops costing a column slot,
  and one that cannot ride keeps the slot it had.
- the lane's pair is *stale-masked* for its whole life in the lane plus the
  cycle after its fire, the same two-cycle window a main-lane row command
  gets; without it the main select re-picks the pair whose ACT is firing on
  the lane and drops it at the fire stage, a slot per row.
- it fires beside a main COLUMN only (the arbiter's lane may also fire into an
  idle main slot; this one may not -- see the timing paragraph below), never
  to the main winner's bank, on the live gate (row image, bank readiness,
  tRRD / tFAW), and *holds* while the class applies and the lookahead opens
  within the pipe -- the main winner's own hold rule.
- its fire feeds the one hint register when the main lane raised no hint
  that cycle, and the ACT-fire history the refresh grant reads. One hint
  register was enough: a column fire with auto-precharge (the hybrid policy's
  common case) raises none.

Two things made the lane cheap to trust. The lane-off core is proved
bit-identical to the golden copy by the existing lockstep task, so the
single-issue product is untouched by construction; and a `dual` task proves
the word invariants (one row command per word, beside a column or alone,
another bank, the live gate) on free inputs, so the DFI command path's
contract holds whatever the environment presents. Sim: `col_major_interleaved`
reads 686 -> 773 MB/s, `row_thrash` 687 -> 775, `random` 656 -> 722, within
1 percent of the ideal on the pure families; `col_major` unchanged.

**The lane must not hang off the main pick's tail** (the sys100 build of
2026-11-12, -1.715 ns, 462 failing endpoints on a core that closed at +0.147
without it). Two things the first lane did looked harmless at the RTL and
were each a critical path:

- it excluded the main select's FRESH row pick from its own candidates
  (`w_sel_src` -> `w_oh_row`), so the lane's rotor ran AFTER the main select
  cone: 15-18 levels, 11.8 ns, 68 percent route. The cut: no same-cycle
  exclusion. The two lanes may load one pair; the fire stage's clash term
  (the REGISTERED main winner's bank) blocks the lane for that cycle and it
  re-picks. A fresh main row pick only happens when no column can fire, a
  cycle the lane could not have used anyway -- so the exclusion bought
  nothing the clash term does not, at the price of the whole select cone.
- its fire was ORed into the plane's command valid (the arbiter's lane may
  fire alone, so the plane's push valid is `main || lane`), which put the lane
  gate -- itself a function of the main fire -- on the fire cone into the DFI
  path: -1.49 ns on the formatter's address register. The cut: the pick core's
  lane fires beside a main column only (`w_col_fire_now`), its `a2_*` imply
  the main valid, and the plane keeps them out of the push valid for that
  core. The idle-slot fire was worth nothing measurable (sim 772 vs 773).

Two more builds found two more terms, each a smaller cone, each the same
mistake in a milder form:

- the candidate set excluded the REGISTERED main winner's bank
  (`r_win_pair >> 1 == b`, sixteen compares): -0.549 ns, 26 of 29 failing
  endpoints. Cut: no exclusion at the pick; the fire stage's clash term
  already keeps the lane off that bank for the cycle.
- "a bank is busy" asked the store whether its pending column could issue NOW
  (`wr_commit_ready_now_i`, the drain queue's full flag): -0.105 ns, the last
  5 lane endpoints. Cut: busy = a column request PENDING there, ready or not.
  A bank whose column merely waits for its data is still not one to re-open
  from the lane.

And one cut had a consequence the formal task could not see (it asserts fire
invariants, not liveness): once the lane fired only beside a main column, a
HELD lane pair -- stale-masked from the main select for its whole life in the
lane -- had no way out when no column was available: the main could not take
it, the lane could not fire it, and the row waited for a refresh to shake
things loose. `mixed` in sim fell from 262 / 331 to 16 / 16 MB/s with every
beat correct. The mask rule became: a held pair is masked only while a column
request is pending somewhere (while the main lane has something else to take
and the pair will ride beside it); with nothing pending the main select takes
the held pair as its own row pick and the clash term makes the lane re-pick.
*Every "the lane owns this request" rule needs the matching "and here is how
the main lane gets it back" rule*, and a liveness failure shows up as a
bandwidth number, not a checker -- which is why the lane's sim set carries
`mixed` (two directions, conflicts in every bank) and not only the pure streams.

The fifth build closed at +0.059 ns under the budget with the main pick as
the worst path, and the board gave `col_major_interleaved` reads 688 -> 774,
`row_thrash` 688 -> 774, `random` 661 -> 729, `mixed` 330 -> 649 with the lane
on, every other cell and every lane-off cell unchanged
(`char_results/board_mc014_granite_row_lane_sku100_2026-11-12.md`).

The rule behind all of it: *a second winner is a second pipeline, and it
joins the first only at registers*. Its candidates come from the registered
request set alone (not the registered winner, not the store's readiness),
its exclusions happen at its own fire stage, its fire rides a fire the main
lane already decided. Any term read from the main select's combinational
output, or from a late input the main select also waits on, puts that cone in
series with the lane. The formal `dual` task now asserts the lane fires beside
a column only (`a_beside_col`), which is what lets the plane drop it from the
valid.
