<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->
# jet-prime delta 04: the 2-cycle resident hit (TASK-002)

**Status:** landed 2026-11-19. The fourth place jet-prime's architecture
differs from jet's. jet's books ([HAS](../../../jet-mesi-l1/docs/jet_has/jet_has_index.md),
[MAS](../../../jet-mesi-l1/docs/jet_mas/jet_mas_index.md)) still describe
the cache; [delta 01](01_fill_engine.md) is the fill engine, [delta 02](02_pair_fabric.md)
the pair fabric, [delta 03](03_single_miss_path.md) the single miss. This
chapter is about the resident read hit: where its three cycles went and
how one came back without reopening the 100 MHz closure that put it there.

## Why

With the miss path rebuilt (TASK-001, steps 2-5) jet-prime was under
HPDcache at every depth on both thrash configurations. What stayed over
HPDcache was the resident hit: jet answered a read hit in 3 cycles at the
injector, HPDcache in 2 (1 inside the cache plus its wrapper's reorder
ring). At depths 1 and 2 every resident configuration (`r4k_*`,
`r16k_we64`, `smoke4k_we64`) sat a cycle per transaction over HPDcache,
and on the thrashes half the depth-1 transactions are hits, so the 3.5 %
depth-1 margin on `r64k_we255` (0.48 cycles per transaction) was this
cycle too. From depth 4 the hit rows were 1.00 on both and the gap was
gone. JP2 only asked that the hit not regress; TASK-002 asks for
HPDcache's floor.

## Where the three cycles were

jet TASK-003 (2026-11-10) counted the v3 resident read hit after its two
FIFO bypasses; jet-prime inherited it unchanged:

| cycle | what happens |
|---|---|
| c0 | CPU handshake; the request skid is transparent while empty, so the lookup sees the request this cycle: the tag array (asynchronous read) is read at its set and the words are captured into the classify-stage register with the request |
| c1 | classify on the captured snapshot (hit, way); the data-array read address is presented a stage ahead of the way select (TASK-003 step 1) |
| c2 | the word lands (the data array is a synchronous-read block RAM), the serve fires, the deposit goes to `jet_prime_rsp_seq`, whose head-deposit bypass offers it to the frontend's staging FIFO in the same cycle |
| c3 | `cpu_rsp_rd_valid` (the staging FIFO's read side, a cycle after its write) |

The capture/classify split is the v3 lookup pipeline (jet ISSUE-001,
2026-11-03): in v2 the classify decided acceptance from the skid's
asynchronous read and the 24-level cone through `u_control` and `u_repl`
missed 100 MHz by 1.8 ns. The split is a timing decision, so the cycle had
to come from somewhere other than folding the classify back.

## What changed

**The data array already reads every way.** `l1_data_array` keeps one
block RAM per way and reads all of them at `a_addr` every cycle; `a_way`
selects among the registered outputs on the output side. So the data read
does not need the way -- it needs only the index and the beat, which are
in the request's address at c0. Nothing in common-ip changed.

**The arriving request leads its own data address in the capture cycle.**
Port A's read address now has four owners in priority order: the commit
read cursor, an unfired read serve record, the arriving request's
`{set, beat}` (`w_live_lead`, keyed off `lkup_valid_i` alone, never off the
capture -- whose room term is the classify cone), and the classify-stage
occupant's own address (TASK-003's lead, now the fallback). In c1 every
way's word for the request's set is on the port and the tag compare's
way selects it.

The live lead yields to the occupant whenever the occupant may need its
own lead (`w_occ_need`: its live lead did not land, the array was written
at that edge, a serve record is pending, or the commit deposits this
cycle -- registers and commit state, not the classify). The first cut did
not have this term and the board found it (bin 5a): an occupant that
cannot serve directly must lead in c1 to answer from its record in c2, as
TASK-003 had it; with the next request's live lead taking the port, that
occupant fell to the record's own re-presented address (c3) and the
one-deep record then held the classify, so the mixed read/write resident
rows lost 40 % of their throughput at depth 4 and 16 (`smoke4k_we64`
1.01 -> 1.76 cycles per transaction, `r16k_we64` 1.05 -> 1.78) while the
pure-read row and the hit floor showed the win. After a write the stream
therefore runs the record path at one per cycle (3 cycles) until a bubble
lets a lead land again; a pure read stream serves every hit directly.

**A read hit answers in its classify cycle (`w_direct_fire`).** When the
occupant's own lead landed (`r_pa_live_d1`), nothing wrote the array at
that edge (`r_dwr_d1`: a word read at a write's edge predates the write),
no commit deposit wants the completion port this cycle, the serve record
is not firing and holds no read (a pending write that is not firing
leaves both ports free; a same-line write would have held the request in
the classify), the classify deposits the hit straight from port A with
the occupant's tag: `cpl_valid_o` in c1, the sequencer's bypass puts it in
the staging FIFO in c1, `cpu_rsp_rd_valid` in c2. Otherwise the serve
record loads and fires a cycle later as before. The direct fire never
loads the record, so `sn_safe_o` and the pend-room rule see nothing new.
With the combinational array (`DATA_SYNC_READ=0`, the control unit TB)
the same fire happens off the occupant lead.

**A write hit's response leaves in its classify cycle too (`w_direct_ack`).**
jet echoes the store on a write response, so the response needs no array
word: whenever the completion port is free the classify deposits the
write's own data with the occupant's tag in c1. The record still loads
and does the array write and the E-to-M promotion when the W port and the
tag port are free; `r_srv_dep` marks it as already answered, so its fire
no longer needs the completion port. The window between the ack and the
array write is the one the record always had: a later access to the line
is held in the classify until the record fires (the same-line rule), and
`sn_safe_o` holds snoops while a write record is pending, so no observer
sees the pre-write data after the ack. Bin 6 had the read side only: the
hit floor read 2 and `r4k_we0` matched HPDcache, while `r4k_we255` and
`r16k_we64` at depth 1 stayed a cycle over on their writes.

**What stays off the classify cone.** The way select for the direct word
and the deposit's tag and data muxes are keyed on port ownership and the
record's own fire, not on the classify; only `cpl_valid_o` carries the classify,
as `lkup_hit_o`, the repl taps and the serve-record load already did. The
live lead's address mux is keyed on `lkup_valid_i`, the cursor and the
record, all registers or shallow. Out of context the worst path is the
same one as jetp5 (the fill engine's staging read pointer into the data
BRAM address) at 19 levels: 6,033 LUT / 5,402 FF (jetp5: 6,010 / 5,399), 16 RAMB36, 1,998 LUTRAM, WNS +0.082 ns at 10 ns (jetp5 +0.321; the same worst path -- the fill engine's staging read pointer into the data BRAM address -- so the spread is placement) -- `ref/results/ooc/jetp6`.

**The read-after-write hazard the lead crosses.** The sync read samples at
the c0 edge. A write serve that fired in c0 lands at that same edge, and
the pre-write word is what the read returns; the classify's same-line
rule (a pending write serve on the line holds the next access) does not
see it, because the record cleared at that edge. `r_dwr_d1` declines the
direct fire for any array write in c0 (the control's own or a fill beat
through the core's write mux), and the record path then reads a cycle
later, after the write. A write in c1 can only be a serve-record write
(fill beats and commit merges land in claimed ways, which never hit), and
a pending record already excludes the direct fire.

## What this changes for the checks

- **`jet_prime_control_tb._await_serve`** polled for a hit's deposit from
  the cycle after the accept and scored a write's W-port signals in the
  deposit cycle; the deposit is now in the accept cycle and a write's
  array write is a separate, later event. The watcher's first sample is
  the current cycle (the rule in [[checks-encode-events-not-cycles]], met
  the same way as step 5's commit watcher), the write's array write and
  promotion are awaited on their own, and the write's ack is checked to
  never follow its array write. The report carries `direct_serves` /
  `record_serves` so the fast path is counted, not assumed: the FULL cell reports 107 hits answered in the accept cycle and 2 from the record (the two are hits whose accept cycle had the completion port taken).
- Two sim assertions in the control: at most one depositor per cycle, and
  a direct serve never with the commit's word on port A.

## Verification that carries this step

- Lint clean (control at both `DATA_SYNC_READ` values, both tops). The
  committed RTL differs from the RTL the board and OOC bins were built
  from by a declaration-order code motion only (the two direct-serve
  assigns moved below the accept signals they read, caught by the
  pre-commit hook); the regenerated flats differ in the order of those
  four lines and nothing else, and gate and FULL were rerun on the moved
  RTL.
- jet-prime gate 21/21; FULL 155/155 (0:09:05) from clean; the reference-rig gate
  7/7.
- Pair-rig func cell, cycle-counted from the waveform at the CPU
  boundary (`cpu0` handshake to response handshake, responses in accept
  order): every directly served read hit 2 cycles (3 of 3 in the final
  RTL's cell; the first cut's cell had 6, two of them held behind an
  older response in J4 order), the cell's one write hit acked in its
  accept cycle and answered in 3 (held a cycle behind an older response),
  misses min 20. The board's resident rows are the measurement.
- Control formal on the regenerated flat: covers PASS (23 of 23 and 7 of
  7 reached); the safety prove (BMC depth 64, boolector) on the committed
  flat (645e7cf19e) PASS 2026-11-20 06:22 after 24:46 wall (23:51 solver;
  no trace) -- against 26:52 on the step-5 flat and 11:57 on the step-3
  flat; steps 61-63 took 3:18, 3:30 and 5:19, so the per-step cost of the
  step-5 environment carries over and the hit-path change did not add to
  it. The liveness BMC is as TASK-001 left it: the step-5 run was stopped
  by the owner at step 123 of 192; the tighter environment and the run on
  this flat were TASK-003 (closed 2026-11-20): the two 128 bounds
  derived at 68 and 62 from the environment's constants and asserted at
  80, the liveness BMC at depth 112 PASS in 1:07 on this flat, covers
  7 of 7, both mutants FAIL at the new bounds.

## Board

`ref_jetpp_bringup` bin 7 (REF_CACHE_SEL=3): 18,241 LUT / 11,896 FF, WNS
+0.040 ns at 100 MHz under the 0.2 ns clock-uncertainty budget, the same
worst path as bins 3-4 (the fill engine's staging read pointer into the
data BRAM address; bin 4 was +0.019, bin 6 +0.003 -- placement spread).
Smoke PASS (ci0 CRC 1814064162, bin 4's); both 55-run sweeps err 0
(`perf_sweep_jetpp_bin7_single_20261119T132547Z.json`,
`perf_sweep_jetpp_bin7_dual_20261119T132726Z.json`), all 55 single-core
read CRCs equal to bin 4's. Hit floor (`lat_min`, `r4k_we0` depth 1) 3 ->
2, HPDcache's.

Cycles per transaction, injector 1 idle (s5 -> s6, HPDcache):

| config | depth 1 | depth 2 | depth 4 | depth 16 |
|---|---|---|---|---|
| `r4k_we0` | 4.00 -> 3.00 (3.00) | 2.00 -> 1.50 (1.50) | 1.00 -> 1.00 (1.00) | 1.00 -> 1.00 (1.00) |
| `r4k_we255` | 4.03 -> 3.03 (3.00) | 2.03 -> 1.54 (1.50) | 1.04 -> 1.04 (1.01) | 1.04 -> 1.04 (1.01) |
| `smoke4k_we64` | 4.02 -> 3.02 (3.07) | 2.00 -> 1.58 (1.53) | 1.01 -> 1.01 (1.12) | 1.01 -> 1.01 (1.12) |
| `r16k_we64` | 4.16 -> 3.17 (3.20) | 2.08 -> 1.66 (1.64) | 1.08 -> 1.08 (1.22) | 1.05 -> 1.05 (1.20) |
| `r64k_we64` | 12.76 -> 12.27 (13.73) | 7.91 -> 7.80 (9.79) | 6.10 -> 6.08 (8.22) | 5.29 -> 5.27 (7.64) |
| `r64k_we255` | 13.17 -> 12.68 (13.65) | 9.31 -> 9.19 (11.04) | 8.65 -> 8.65 (10.53) | 8.51 -> 8.51 (10.51) |
| `r128k_we64` | 16.94 -> 16.69 (18.83) | 9.91 -> 9.86 (13.11) | 8.09 -> 8.08 (11.37) | 7.58 -> 7.57 (10.90) |

The resident rows are at HPDcache's numbers at depth 1 and within 0.05
cycles at depth 2 (the residual is a write whose accept cycle finds the
completion port taken and acks from the record); the depth-1 thrash
margins went from 7.1 / 3.5 / 10.0 % to 10.7 / 7.1 / 11.3 %; from depth 4
every row is s5's within 0.02. Dual-active `r64k_we64` depth 1 12.28 /
12.25, depth 16 5.30 / 5.32; `r4k_we0` depth 1 3.02 / 3.00.

The two intermediate bins: bin 5a (the read side with the arriving
request's lead pre-empting an occupant that could not serve directly)
read the floor at 2 and `r4k_we0` at 3.00 while `smoke4k_we64` and
`r16k_we64` at depth 4 and 16 went to 1.76 / 1.81 / 1.78; bin 6 (the
read side with the yield) restored those and left `r4k_we255` at 4.02,
`smoke4k_we64` 3.27 and `r16k_we64` 3.42 at depth 1 -- the write hit.
Both sweeps are kept in `ref/results` (`bin5a_*`, `bin6_*`).
