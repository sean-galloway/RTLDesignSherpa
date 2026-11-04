# TASK-047: dual issue on DFI 1:2 -- a row command beside the column in one DFI word

> Source: owner, 2026-10-23 ("Do 1/2/3"), item 3 of the FR-FCFS parity
> work: after bank preparation (TASK-045) the one remaining structural
> difference between this controller and the textbook FR-FCFS setting is
> that the command slot and the data slot are the same slot. Related:
> TASK-045 (bank preparation, the policy half), the reverted 2026-07
> bank-parallel scheduler (`4eeb37f9`, a different design on the
> pre-recovery FSM scheduler; its board failure was the open-page read
> return path, not dual issue as such), Phase 3 report section 3
> (the arbiter cone is the 75 MHz critical path at +0.001 ns).

**Priority:** P3 (research; bounded gain, real timing risk)
**Status:** OPEN 2026-11-03 (unparked the same day: ISSUE-027 closed and the
50 MHz board build with the lane closes at +0.134 ns, 0 failing). Remaining:
the board run. Was DEFERRED 2026-11-03 after a best-effort pass (owner: "reopen 47
and see if it can happen; give best effort then defer if needed"). Built
behind `DUAL_ISSUE` (default off, cycle-identical to HEAD), verified in sim
and formal: 9 -> 8 slots per bank-walk row, col_ilv +12 / +14 percent at one
thread. Timing moves by under a nanosecond on a cone HEAD already fails;
blocked on ISSUE-027 (HEAD misses its own 50 MHz board clock). Unpark
condition: ISSUE-027 resolved. Results log below.
**Owner:** TBD

## Why

At the board point (BL4 on x16, DFI 1:2, one command per 75 MHz sys clock)
one column command per cycle saturates the data bus, so every ACT and PRE
costs a column slot. TASK-045 made the FR-FCFS core spend those slots at
the right moment (inside the column's dead time, bank prepared before its
columns arrive); it does not make them free. Per 8-column row on a bank
walk that is 1 slot in 9 (11 percent, 533 of 600 MB/s); on a row-hit
stream it is nothing. The textbook controller does not pay it because its
command bus has slack. On DFI 1:2 the PHY accepts a command on EACH of the
two phases of a DFI word, i.e. two commands per sys clock; the controller
uses one (phase 0, the other phase NOP: `mc_xddr2_cmd_formatter` "v1
places the issued command on phase 0"). Putting the row command on the
other phase restores the slack.

## Ceiling (measured inputs)

| shape | slots per row now (TASK-045) | with dual issue | gain |
|---|---|---|---|
| col_interleave, 8 columns per row, AP close | 9 | 8 | 11 percent (up to 600 from ~533) |
| col_interleave with explicit PRE (predictor not armed) | 10 | 8 | 20 percent |
| col_major (same bank) | 13 rd / 15 wr (JEDEC floor) | unchanged | 0 -- the floor is tRP + tRCD, not slots |
| incremental / row_major | ~1.03 (ACT per row of 256+ columns) | ~1.00 | < 3 percent |

So the gain is bounded to the bank-walk families and to what the page
policy leaves as explicit PREs; a mixed workload with many short rows is
the case that benefits.

## Design

1. **Two output lanes in `mc_cmd_arbiter`:** the pick comb already keeps
   the classes in separate pre-pick registers (`*_col_f`, `*_act_f`,
   `*_pre_f`), so a second output register holding a ROW command
   (ACT or PRE) can be filled in the same cycle as the column register
   whenever both classes are ready for different banks. The fire stage
   checks each lane against its own bank's live readiness
   (`w_out_safe` per lane). The two lanes never target the same bank in
   one word.
2. **Command FIFO entry carries two commands** (`mc_common_pkg`'s command
   struct gets a second, optional, row-command half, or the plane pushes a
   2-wide word). `mc_scheduler_plane`'s CMD_DELAY token path is per word,
   unchanged.
3. **Phase placement:** row command on phase 0, column on phase 1 of the
   same word. Then a column that follows an ACT to the SAME bank is never
   in the same word (the bank timers have not counted the ACT yet, so the
   column is not ready), and tRCD/tRP measured in whole sys clocks from the
   word stays conservative by construction. Columns moving to phase 1
   shifts the DFI data phase by one CK: `rd_phase_i` / `wr_phase_i` are
   runtime (the bring-up tuple was taken at phase 0), so the PHY alignment
   has to be re-measured on the board (`t_rddata_en`, `t_phy_wrlat`).
4. **Bank timers take two events per cycle** (`mc_bank_timers` has one
   `evt_*` set; add a second, or OR the two lanes' events into per-bank
   strobes since the lanes are to different banks). `mc_global_timers`:
   tRRD / tFAW count ACTs; two ACTs never share a word (one lane is a
   column), so one ACT per cycle still holds. tCCD is per column; one
   column per word.
5. **Command history checker and the DFI slave model** need to accept two
   commands per DFI word (the checker's "need N cycles" reads whole words;
   a phase-1 column after a phase-0 ACT on another bank is legal).
6. **Formal:** the arbiter proof's single-output invariants become per lane
   plus "lanes are to different banks".

## Risk

- **Timing is the gate.** The FR-FCFS arbiter cone IS the 75 MHz critical
  path (+0.001 ns on the committed text, Phase 3 report 3.2). A second
  pick in the same cycle adds a second pick mux and a second fire check in
  parallel (not in series) -- the row lane's inputs are the existing
  `*_act_f` / `*_pre_f` registers -- but the output-register load logic
  and the FIFO push width grow. Must be built OOC first at the board
  generics (report 5.3 flow) before any board build. The 75 MHz floor is
  not negotiable (owner).
- **Board PHY alignment** with columns on phase 1 (above). A sim-green
  dual issue that misaligns the data phase on silicon would repeat the
  2026-07 story; the ILA-first bring-up applies.
- **BANK_PICK parity:** the per-bank core would need the same second lane
  to keep the two cores comparable; otherwise the product core falls behind
  the research core by the bank-walk gain above.

## Not this task

- A 1:4 DFI (four phases) -- the board is 1:2 at 75 MHz.
- Issuing two COLUMNS per word (BL4 on DFI 1:2 is one column per word by
  data-bus width; `N_SUBCMD` already handles the BL4-at-1:4 case).

## Done when

- OOC at board generics closes 75 MHz with the second lane; the board build
  keeps a positive WNS.
- Bench (`test_pumice_core_bankprep.py`): col_interleave 8 slots per row
  both directions; proxy col_interleave at eight threads within 2 percent
  of the streaming families.
- Both geometries' pumice regression, granite, common-ip, formal, lint; the
  DFI slave model and the history checker updated and their unit tests
  passing; the HAS/MAS DFI chapter updated.

## Results log

### 2026-11-03: built, verified in sim and formal, timing at noise; deferred on ISSUE-027

**What landed (default off, `DUAL_ISSUE = 0` is cycle-identical to HEAD).**
`mc_cmd_arbiter` grows a row-only second output register (`r2_*`), loaded
at the main register's edge from the same pre-pick registers when the class
priority picks a column; it carries a demand ACT, or with none a demand PRE,
to a bank neither column candidate names. It fires on the live bank image,
never beside a main-lane row / refresh / ZQ / maintenance command and never
to the main lane's bank; it holds while its bank is closed or closing (ACT)
or open (PRE) and is dropped otherwise, and it never blocks the main lane.
Every in-flight / fired guard the main lane's ACT and PRE feed, its register
and fires feed too (handbook [[dependent-hops-forward-the-pick]]). Under
the default `access_pref` a row command that can ride the lane no longer
takes the column's slot; one that cannot still does, as bank preparation
places it. `mc_bank_timers` takes a second event set, `mc_global_timers`
the lane's ACT, `mc_page_policy` the lane on `cmd2_*` (idle timers,
predictor, telemetry). `mc_scheduler_plane` widens the command FIFO word;
`mc_dfi_cmd_path` drives the lane with its own formatter on `row_phase_i`,
which the formatter now also uses for every main-lane non-column command
(LPDDR2 masks the lane off). pumice: `DUAL_ISSUE` on `pumice_core` /
`pumice_top` / `pumice_top_geared` / the char harness (`PUMICE_DUAL_ISSUE=1`
build env), `SCHED_POLICY.dual_issue` and `DFI_PHASE.row_phase` CSRs (RDL
regenerated), effective only on DDR2 with `row_phase` off both column
phases and one column command per word. Granite, scoria and andesite tie
the lane off.

The design study's phase plan changed for the better: the COLUMNS stay on
`rd_phase` / `wr_phase` (0 on the board) and every row command moves to
`row_phase` (1). No PHY re-alignment: the data phases do not move. The only
CK-level shift is ACT -> column one CK shorter and column -> PRE one CK
longer, and the host derivation (`pumice_device.py`) already carries a full
phase margin on every ns-derived delay, so tRCD holds; tRTP is computed
phase-exact with the new `row_phase` argument.

**Sim.**

| check | lane off | lane on |
|---|---|---|
| bench, board geometry, 128 bank-interleaved 8-column rows: slots per row wr / rd | 9 / 9 | **8 / 8** |
| bench columns per cycle wr / rd | 0.878 / 0.890 | 0.996 / 1.000 |
| bench single-bank rows (col_major shape) | 16 / 15 cyc per row | identical |
| proxy 1 thread col_ilv MB/s wr / rd | 452.5 / 496.8 | **505.0 / 567.2** |
| proxy 8 threads col_ilv MB/s wr / rd | 523.2 / 541.3 | **536.0 / 562.1** |
| proxy 8 threads col_major MB/s wr / rd | 458.1 / 506.7 | **508.3 / 572.2** |
| proxy 8 threads incremental / row_major rd | 560.9 / 561.3 | 567.5 / 568.5 |

Zero mismatches and zero DRAM-model violations in every run. The lane
built but off is cycle-identical to HEAD on the proxy (all four families).
At one thread incremental / row_major reads read 0.7 / 1.1 percent lower
with the lane on: one extra refresh in the read phase, because the write
phase before it ended at a different cycle (three 25-cycle refresh gaps
against four, every other read back to back; col_major run alone is
cycle-identical) -- handbook [[measure-over-the-window]]. Eight-thread
col_ilv reads are within 1.1 percent of the streams (the 2 percent bar);
writes are 4.5 percent below (5.7 off). The remaining write gap is the
main output register EMPTY (no column ready), not row commands: a fire-stage
probe counted zero rejects and zero lane holds or drops (1 463 lane fires),
so it is column supply at eight writers, outside this task.

**Regression / formal / lint.** pumice 222 / 222 at both geometries, the
16-cell core DFI suite with the lane on in every cell (16 / 16; the lane
fired in the five with concurrent multi-bank traffic, the others issue one
request at a time or stream row hits), granite 27 + 1 xfail, common-ip
47 fub + 36 macro (3 xfail), scoria and andesite failure lists identical to
HEAD (12 / 21, pre-existing). `formal/mc_common/mc_cmd_arbiter` prove and
cover pass, and a new `dual` / `dual_cover` task (tRRD / tFAW over both
lanes, lane one-hot, never beside a main-lane row, never the main lane's
bank) passes at depth 30 with every lane cover reached; removing any one of
the lane's three fire terms fails it (`a_row2_no_row`, `a_row2_bank`,
`a_trrd_spacing`). Verilator lint warning sets identical with the lane on
and off. RDS-DV `DFISlavePHY` decodes every selected phase whenever two or
more carry a command (it read only the first; RDS-DV #99, `1b83ed1`); DV unit (DFI subset, 308 +
2 new) and DFI sim tests pass.

**Timing (Nexys A7, clean Vivado runs of scratch trees, HEAD vs HEAD +
lane):**

| point | HEAD | with the lane | LUT / FF added |
|---|---|---|---|
| 50 MHz, combiner on (the shipping point) | -2.843 ns, 24 failing | -3.689 ns, 40 failing | +537 / +43 |
| 75 MHz, combiner on | -9.794 ns, 4 283 | -9.885 ns, 4 643 | +812 / +88 |
| 75 MHz, combiner off | -9.951 ns, 2 385 | -9.391 ns, 2 070 | +623 / +88 |

Every failing path, with and without the lane, is the arbiter's STAGE-1a
population -> STAGE-1b -> classify cone at 24-27 levels; the lane moves WNS
by under a nanosecond either way, inside place-and-route variance on this
route-bound cone. But HEAD itself no longer closes its own shipping point
(the 2026-10-27 bitstream closed +0.029 ns at 50 MHz) -- filed as
**ISSUE-027**. "The board build keeps a positive WNS" therefore cannot be
met or refuted for the lane until HEAD closes.

**Deferred** (owner's rule: best effort, then defer if needed). Unpark
condition: ISSUE-027 resolved (pumice closes its board clock again); then
build with `PUMICE_DUAL_ISSUE=1`, confirm the WNS delta, and run the board
with `SCHED_POLICY.dual_issue=1`, `DFI_PHASE.row_phase=1`. Not done:
BANK_PICK parity (granite's core has no lane), the scheduler-side and
DFI-wire command-history checkers and the Ocelus accept tap do not see the
lane, and the eight-writer column-supply gap above.

### 2026-11-03: unparked -- ISSUE-027 closed, the lane closes 50 MHz

ISSUE-027's fix (the arbiter's QoS max as a tree) closes the shipping point:
50 MHz, combiner on, HEAD +0.057 ns and **with the lane +0.134 ns**, 0 failing,
hold clean, 45 992 LUT (+744 over the same text without the lane). Next:
`PUMICE_SYS_50=1 PUMICE_DUAL_ISSUE=1 make bitstream`, then the char profiles
on the board with `SCHED_POLICY.dual_issue=1` and `DFI_PHASE.row_phase=1`
against the lane-off bitstream, with zero mismatches as the bar.


### 2026-11-03, board at 50 MHz: the lane closes clean, the lane BUILD with the lane off does not

Two bitstreams from the same text (tree_q50 lane-off, tree_q50d `PUMICE_DUAL_ISSUE=1`),
all eight char profiles, `PUMICE_MC_CLK_HZ=50000000`. Host knob added:
`TEST_DUAL_ISSUE=1` (pumice_char ControllerConfig) sets SCHED_POLICY.dual_issue and
DFI_PHASE.row_phase (`TEST_ROW_PHASE`, default 1); lane off, neither field is
written (only pumice's map has them). Passes: A lane-off build, B lane build lane
off, C lane build lane on.

| profile | rows | mismatched beats A / B / C | wr / rd C vs B (mean) | best row C vs B |
|---|---|---|---|---|
| every | 68 | 0 / 0 / 0 | +7.6 / +7.9 % | +32 % open_page col_major_interleaved_bl4 |
| windows | 9 | 0 / **18,952** / 0 | -3.7 / +1.9 % | +12 % row_thrash_bl8 |
| half_threads | 48 | 0 / 0 / 0 | +1.0 / +0.3 % | +6 % |
| concurrent | 8 | 0 / 0 / 0 | +5.3 / +5.3 % | +33 % col_major_interleaved_bl8 |
| multigen | 8 | 0 / 0 / 0 | +2.5 / +2.5 % | +7 % |
| half_burst / half_burst8 / half_gap | 48 | 0 / 0 / 0 | within 1 % | |

B vs A bandwidth is 1.000 on every profile (the off lane costs nothing), but B lost
data. `windows` repeated (seeds are fixed per scenario, so every run writes the same
data to the same addresses):

| bitstream | lane | windows runs | failed (scenarios, beats) |
|---|---|---|---|
| lane-off build | -- | 4 (one per fresh program + 2 reruns + pass A) | 0 |
| lane build | off | 7 | 3: random_bl8 open/close (~5,960 / ~4,730), mixed_bl8 close (8,258), row_thrash_bl8 close (10,661) once |
| lane build | on | 1 (pass C) | 0 |

Intermittent, not reprogram-linked (a fail followed a pass with no reprogram), and
only the lane build with the lane OFF. Open: reproduce in the char harness sim with
DUAL_ISSUE=1 and dual_issue_en=0 on the windows random/mixed scenarios; the DFI
command path's NOP gate (`!(DUAL_ISSUE && w_op == OP_NOP)`) and the wider command
word are the RTL that differs with the lane off. CSVs/logs:
scratchpad `t047_board/`.

Later the same evening, `windows` only, lane build:

| run set (time) | lane | row_phase | runs | failed |
|---|---|---|---|---|
| alternating, 18:00-18:46 | on | 1 | 4 | 0 |
| alternating, 18:00-18:46 | off | 0 | 4 | 2 (random_bl8 open/close, ~5,950 / ~4,700) |
| split, 19:00-19:44 (after a granite bitstream ran) | off | 1 | 4 | 0 |
| split, 19:00-19:44 | off | 0 | 4 | 0 |

Totals: lane build lane off 5 / 19 failed, lane on 0 / 5, lane-off build 0 / 4.
The split (TEST_ROW_PHASE now writes row_phase with the lane off) did not
discriminate -- nothing failed in it, including the setting that failed before.
The failure is intermittent and time- or state-dependent; the counts no longer
cleanly separate the lane build from the lane-off build. Next: interleaved soak
of both bitstreams (same profile, alternating programs) for real failure rates,
and a char-harness sim of windows random_bl8 with DUAL_ISSUE=1, lane off.
