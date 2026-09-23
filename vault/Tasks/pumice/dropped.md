<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# pumice — Dropped (ended without completing)

---

## PUMICE-033 — one extra AXI ID bit doubles the arbiter's pick cone

**Status:** DROPPED 2026-09-23 — the premise does not arise.

Sean 2026-09-23: "drop; ID's are always 8-bits or less."

The task existed because AXI_ID_WIDTH 8 -> 9 doubled the arbiter's pick cone and
cost 75 MHz closure ([[project_ddr2_char_board_timing_regression]]). If the ID
is 8 bits or fewer by construction, the 9-bit case is not a configuration this
controller has to support, so there is no constraint to characterise and no
cone to shrink. The measured timing finding stays valid history -- it is why the
board build pins 8 -- it just is not open work.

<details><summary>Original entry</summary>

**[archived heading] PUMICE-033 — one extra AXI ID bit doubles the arbiter's pick cone**
**[archived] Status:** open 2026-09-14  **Priority:** P1 — it is a hard constraint on where pumice can be used

**The finding: `AXI_ID_WIDTH` 8 -> 9 takes the arbiter's
`r_rd_pop -> r_wr_col_q` path from 13 logic levels to 26, and 75 MHz from
+1.100 ns to -6.602 ns.** Measured at SYNTHESIS, before placement, so it is the
netlist and not congestion. Same RTL, same constraints, same clocks, same
synth settings; the only difference is the parameter.

| ID width | logic levels | data path delay | post-route slack |
|---|---|---|---|
| 8 | 13 | 11.09 ns | +1.100 |
| 9 | 26 | 20.21 ns | -6.602 |

**Why it matters beyond this board.** BRIDGE-016 made fabric IDs
`{master index, master id}`, so ANY multi-master fabric in this repo hands its
slave more ID bits than a single master drives. pumice cannot currently absorb
that. It is usable behind one master, or behind a fabric that keeps the index
inside the master's own width -- which is what the char harness now does, by
putting the generator index in the top bits of the 8-bit id rather than on top
of it (7baf98780). That works and costs 1 bit of id space per doubling of
masters, but it is a workaround in the CONSUMER, not a fix in pumice.

**Where to look.** `pumice_cmd_arbiter.sv`: the pick is
`NUM_ENTRIES`-wide and ID comparisons are replicated across every entry, so an
extra bit multiplies by the entry count rather than adding to it. `qos_top` at
:818 is the same shape. The fix is presumably to compare a narrowed key, or to
pipeline the pick a stage further, not to widen everything and hope.

**How this was found**, because the route to it was wrong twice and the method
is the reusable part: the regression was first blamed on removing the data
bridges, on the read-return-ring depth, on constraints, on placement directives
and on hierarchy flattening -- each ruled out with its own build. Sean rejected
the bridge explanation on the grounds that generators behind a bridge and
generators without one look identical to pumice, which is correct and is what
forced the measurement that found it. **Logic levels at the synthesis
checkpoint are the discriminator**: if they differ between two builds, the cause
is RTL or parameters and can never be placement.

```
open_checkpoint <run>/synth_1/<top>.dcp
report_timing -to [get_pins -hier -filter {NAME =~ *u_arbiter/r_wr_col_q_reg*/D}] \
              -max_paths 1 -path_type full
```

**Definition of done:** pumice closes 75 MHz with `AXI_ID_WIDTH = 9`, or the
constraint is documented as permanent in the HAS with the id-space workaround
named as the supported pattern.

---


</details>

---

## PUMICE-038 — the reader's ADDR_HASH compare is inert in the char sim build

**Status:** DROPPED 2026-09-23 — nothing left to chase.

Sean 2026-09-23: "038 drop."

Already downgraded P1 -> P2 on 2026-09-20 when the hash compare was proven
both ARMED and DISCRIMINATING at burst_len=8 (mutation fired, control passed).
The original repro almost certainly used an illegal burst_len=4. With the
mechanism proven live, the remaining item was tidiness.

<details><summary>Original entry</summary>

**[archived heading] PUMICE-038 — the reader's ADDR_HASH compare is inert in the char sim build**
**[archived] Status:** open 2026-09-14  **Priority:** P2 — DOWNGRADED 2026-09-20
**The blanket claim below is NOT reproducible at a legal burst length. Read the
2026-09-20 measurement before acting on the "do not use data_mode=1" advice.**

Found while implementing [[PUMICE-037]]'s sim repro. In
`ddr2_char_macro_tb_top`, a read engine programmed with `data_mode=1`
(ADDR_HASH) never reports a mismatch:

| mutation | expected | observed |
|---|---|---|
| reader given a hash seed XORed with 0xFFFFFFFF | every beat mismatches | `beats_mismatched=0`, PASS |
| reader pointed at a page nobody ever wrote | every beat mismatches | `beats_mismatched=0`, PASS |
| same two mutations with `data_mode=0` (LFSR) | fail | **fail**, "reader 0 data error" |

So the compare path itself works; it is the hash mode that is inert here.

**Not a board problem.** The board runs `data_mode=1` and DOES report
mismatches — thousands of them, which is how PUMICE-037 was found — so the
RTL's hash compare works on silicon. Something between the CSR write and the
reader's expected-data mux differs in this sim build. `reader_status` shows
`crc_valid=False` at done, and the RTL sets `o_actual_crc_valid <= !r_data_mode`,
so `data_mode` itself IS reaching the engine. Suspect the HASH_SEED0/1/2 CSR
writes: if they are dropped, both sides fall back to the same constant and a
"wrong" seed changes nothing — though that alone would not explain the
unwritten-page case, so measure before believing it.

**Why P1.** Every sim check written in ADDR_HASH mode is currently
decorative, and nobody would know: it passes. This is the CONV-002 shape
(a test that reports green because nothing reads the verdict) in a different
dress. Until it is fixed, sim data checks must use LFSR mode, which is
mutation-verified to fail.

### 2026-09-20: does NOT reproduce at BURST=8 -- hash mode is armed

Did the "Do:" below. Added `test_ddr2_char_macro_hash_probe` (TEST_TYPE
`hash_probe`), which runs BOTH directions in one sim and ASSERTS each, so it
cannot pass silently:

    wrong seed + unwritten page  -> beats_mismatched != 0   (detects)
    writer's seed + written page -> beats_mismatched == 0   (no false alarm)

Both hold. sim_time_ns=58,060, so not vacuous. **The ADDR_HASH compare is armed
AND discriminating** in this build at burst_len=8.

The second half matters as much as the first: "non-zero on a mutation" alone
would also be produced by an engine that mismatches on EVERYTHING, so a probe
with only the first check proves nothing. Both mutations from the original
report were applied together, since a dropped seed would explain the wrong-seed
case but not the unwritten-page one.

**Most likely explanation for the original observation: burst_len.** The first
attempt at this probe used burst_len=4 and the TB rejected it outright --
"burst_len=4 is ILLEGAL -- generator bursts must be whole multiples of
BURST_LEN_MULTIPLE=8 ... This is an invalid configuration, not a slow one".
If the original repro ran at a sub-multiple burst, it was an invalid shape that
the guard now refuses, and the engine's behaviour there says nothing about
legal use. The original conditions were not recorded precisely enough to
re-test, which is why this stays OPEN rather than closed.

**Act on this:** the standing instruction "until it is fixed, do not write a
sim check in data_mode=1" is NOT supported at legal burst shapes, and it has
been costing coverage on every test written since 2026-09-14 -- including
`test_ddr2_char_macro_concurrent_gap`, which deliberately uses LFSR mode and
says so. Hash mode is the mode the board runs. Treat data_mode=1 as usable at
burst multiples of 8; if anyone reproduces the inert behaviour, record the
EXACT burst_len, geometry and seeds this time.

**Do:** program a reader in data_mode=1, read back AXI_ATTR and HASH_SEED0/1/2
over APB and confirm what actually landed; then trace `w_cp_expected` against
`fub_rdata` on a single beat in waves. Both are cheap.


</details>

---

## PUMICE-044 — read eye is 10 taps: IDELAY is the only read knob

**Status:** DROPPED 2026-09-23 — time already spent is not recoverable by
spending more.

Sean 2026-09-23: "044 drop, unless more time than the huge amount spent already
is needed; if so I need a very good explanation why more time will not be
wasted."

I do not have that explanation, so it drops. What the time bought: the
inter-lane skew theory was REFUTED by measurement (both lanes identical, taps
0..9), and an MMCME2_ADV attempt to gain phase control broke the board --
CLKOUT2_USE_FINE_PS("TRUE") silently drops the static CLKOUT2_PHASE(90.0), so
writes lost DQS centring and no tap passed at any bitslip. Reverted.

What remains is a PHYSICAL limit, not a bug: on 7-series the read path has one
knob (IDELAY), it spans ~75% of a UI, and the eye is 10 taps wide. The board
levels cleanly at bitslip 0 / tap 4 and every board sequence passes on it. More
time would go into working around a part limitation for margin nobody has
shown is needed.

Re-open only with a SYMPTOM -- a leveling failure or a read miscompare traced
to eye width -- not with a theory about margin.

<details><summary>Original entry</summary>

**[archived heading] PUMICE-044 — read eye is 10 taps: IDELAY is the only read knob and it spans 75% of a UI**
**[archived] Status:** open 2026-09-17  **Priority:** P3

Board leveling reports a 10-tap read eye and `leveling not clean: final verify
at centred (bitslip, tap) failed` on every run, against the recorded bring-up
tuple of tap 8 / eye 17 ([[project_pumice_board_bringup_tuple]]). At 300 MT/s
the UI is 3.33 ns, so a ~781 ps eye (10 x 78.125 ps) is ~23% of a bit period --
poor for an interface this slow.

**NOT inter-lane skew.** Ran `host_train_per_lane.py` (bl=4, txn=4) to test the
obvious theory that the joint sweep -- `pumice_master.py` drives
`PHY_DLY_SEL = self.lanes`, x16 => both byte lanes move together -- was
reporting the INTERSECTION of two skewed lanes:

    lane0: eye taps 0..9 (width 10), centred at 4
    lane1: eye taps 0..9 (width 10), centred at 4

Identical. Zero skew, and per-lane training buys nothing on this board. The
joint sweep is not discarding margin. (Passing bitslip pairs: diagonal
[(0,0),(4,4)], per-lane-only [(0,4),(4,0)] -- 0 and 4 alias, so bitslip
contributes nothing either.)

**The real cause: nothing can place the sampling point.**

 1. Capture is FIXED-PHASE, not DQS-strobed. `ddr2_char_top.sv:138`
    `CLKOUT2_PHASE(90.0)` -- DQ is captured by ISERDES on an internally
    generated 150 MHz clock at a hard-coded 90 deg. The DRAM's DQS clocks
    nothing. So the margin is not the UI; it is how well one fixed FPGA edge
    lands inside a window that moves with tDQSCK, tDQSQ, flight time and PVT.
 2. The FINE knob cannot reach half the eye. IDELAYCTRL is pinned at 200 MHz
    (required, see the comment at ddr2_char_top.sv:106-108) => 78.125 ps/tap
    x 32 = **2.5 ns total range, only 75% of one 3.33 ns UI** -- and IDELAY only
    ever ADDS delay.
 3. The measured eye is therefore CLIPPED, not narrow: it starts at **tap 0 on
    both lanes**, so its left edge is at or below the floor. The true eye is
    wider than 10; we cannot see the part that lies at negative delay.
 4. The COARSE knob overshoots. Bitslip steps a full UI (3.33 ns) while the tap
    range is 2.5 ns -- an 0.83 ns gap it cannot bridge. Exactly why bitslips
    1,2,3,5,6,7 fail outright and only 0/4 (aliases) pass. No combination
    centres the window.

**Fix direction:** the MMCM phase is the continuous, full-range knob and it is
frozen at 90 deg. Sweep `CLKOUT2_PHASE` at build time, or better use MMCM
DYNAMIC PHASE SHIFT as a calibration step, to put the sampling edge mid-window;
IDELAY then only trims. This is what MIG and LiteDRAM read calibration do, and
is likely why LiteDRAM is healthy on this same board
([[project_litedram_ref_proves_board]]).

**Put every knob on one axis first.** Let `s = theta - d` be the sampling point
relative to data, in degrees of CLKOUT2 (150 MHz, 6.667 ns period, so
**18.52 ps/deg**):

    quantity                              time        degrees
    one UI (300 MT/s)                     3.333 ns      180
    IDELAY full range (32 x 78.125 ps)    2.500 ns      135
    measured eye (10 taps)                  781 ps       42
    MMCM STATIC phase step (VCO/8)          208 ps    11.25

With theta = 90 fixed and d in [0, 135], only `s in [-45, 90]` is observable at
all. The eye passes for d <= 9 taps (38 deg), i.e. `s in [52, 90]` -- and its
upper edge cannot be seen because **s can never exceed theta**. That is the
clipping, stated exactly, and it says which way to move: IDELAY delays DATA
(equivalent to moving the clock EARLIER), so the unexplored direction is data
earlier = clock LATER = phase ABOVE 90.

**A static sweep, if done, must go UP and land on the grid.** theta = 90 / 180 /
270 covers `s in [-45,90], [45,180], [135,270]` -- contiguous (steps <= the 135
deg each build can scan) and 315 deg total, comfortably bracketing both edges of
a 180 deg UI. Two points (90, 180) technically suffice at 225 deg.

DO NOT sweep 70/90/110 (an earlier suggestion here, withdrawn): 70 explores the
direction IDELAY already covers, so it adds nothing, and NEITHER 70 NOR 110 is a
legal phase -- the static grid is multiples of 11.25 deg (67.5, 78.75, 90,
101.25, 112.5, ...), so Vivado would silently round both and the comparison
would be against points nobody chose.

**WITHDRAWN 2026-09-17 -- the MMCM phase CANNOT fix this. Built it, measured
it, and the premise was wrong.**

`CLKOUT2` (sys2x_dqs) is the WRITE DQS strobe, not the read capture clock.
From the GENERATED netlist (`rtl-vivado/a7ddrphy/a7ddrphy_generated.v`), which
is the authority here:

    16 x ISERDESE2 (read) : .CLK(sys2x_clk)  .CLKB(~sys2x_clk)  .CLKDIV(sys_clk)
     4 x OSERDESE2 (write): .CLK(sys2x_dqs_clk)

`ddr2_char_top.sv:271` already said so ("all 16 read ISERDESE2 are
.DATA_WIDTH(4) on .CLK(sys2x_clk)") and I read past it. The 90 deg on CLKOUT2
is classic WRITE DQS centring -- which is what its name should have told me.

**So there is NO independent read-capture phase in this PHY:**
  * shifting CLKOUT2 moves the write strobe -- no effect on read capture;
  * shifting CLKOUT1 (sys2x) moves CK **and** the capture edge together. The
    DRAM returns data relative to CK, so the relationship is preserved and read
    margin does not change -- while the write DQS relationship breaks, since
    CLKOUT2 stays put;
  * IDELAY on DQ is genuinely the only read knob: one-directional, 2.5 ns span
    = 75% of a UI. **That, not a missing calibration step, is why the eye is
    pinned at taps 0..9.**

**The attempt also broke the board, instructively.** Swapping MMCME2_BASE ->
MMCME2_ADV with `CLKOUT2_USE_FINE_PS("TRUE")` silently DROPPED the static
`CLKOUT2_PHASE(90.0)`: on 7-series an output using fine phase shift is owned by
the dynamic shifter, so the build-time phase no longer applies. Writes lost DQS
centring, leveling could not lay down a pattern, and a freshly programmed board
reported **no passing tap at ANY bitslip**. Timing was fine (WNS +0.113) -- it
built and closed, it just could not write. REVERTED, board rebuilt.

**Real fix, if the eye is ever worth the work:** give the read ISERDES their own
phase-shiftable clock, separate from sys2x/CK -- a new MMCM output plus a change
to `bin/gen_a7ddrphy.py` so the ISERDES `.CLK` uses it. A PHY change, not a
config tweak, and the only route that moves the read sampling point
independently of CK.

**Worth salvaging separately:** the CSR + walk FSM built here is a working
WRITE-DQS phase control, which this design does not otherwise have and which is
a legitimate write-training knob. If revived it must be RENAMED to say so --
leaving it called MMCM_PS implies read-capture control it does not provide --
and the static 90 deg must be re-established, either by pre-walking the shifter
at reset or by keeping a second non-fine-PS output for DQS.

**Priority note:** the 10-tap eye has NOT caused a failure. PUMICE-039's
corruption was DQ collisions (bad beats 36/64 bits wrong = random data); a
marginal eye yields few-bit errors. 039 measured 210 clean runs with this exact
eye. This is margin-hardening, not a defect -- drop to P3.

</details>

---

## PUMICE-008 — Per-beat DFI read deskew
**Status:** dropped 2026-07-21 — superseded; the board fix was PUMICE-005, not this

The theory was that the board read blocker is a HALF-DFI-WORD PHASE SKEW: the
a7ddrphy returns the two 64b beats of a 128b DFI read word at DIFFERENT capture
latencies, so a single whole-word capture takes one beat correct and the other
STALE from the previous read -> exactly 2-of-4 device-words wrong, EVERY read,
INVARIANT to rddata_delay (which shifts both beats together and so can never
fix a skew BETWEEN them). That was offered as the reason leveling found "no
passing tap".

The work was built and it functions — but it was never the board fix. The real
cause was the PUMICE-005 tuple (rddata_delay alignment + honest metrics +
no-rmw writes), and the board reads clean at deskew 0/0.

Recorded so the effort is not mistaken for an accomplishment, and so nobody
re-derives the same theory. What was built, and does work:

- `pumice_dfi_rd_aligner.sv`: per-beat delay lines, runtime max-deskew capture
  so deskew 0/0 is BIT-IDENTICAL, zero added latency. Verified (3 existing
  aligner FUB pass; macro 398 pass — no fallout).
- Red->green FUB: `test_pumice_dfi_rd_aligner_deskew` (deskew_hi=1 realigns a
  modelled skewed stream -> correct) + `_deskew_red` (deskew_hi=0 -> the 2/4
  corruption baseline). No PHY model needed.
- CSR: `PHY_TIMING.deskew_lo[25:24]`/`deskew_hi[27:26]` (regen in lockstep,
  regmap synced). Threaded top->core->dfi_layer->aligner. Top wr_rd_roundtrip
  green (bit-identical at reset default 0/0).
- FAITHFUL model hook: opt-in per-64b-beat skew in DFISlavePHY (RDS-DV,
  `read_hi_skew`/`read_lo_skew`, default 0 = bit-identical; char rate4_x16
  skew-off 3/3 pass). Char env knobs `TEST_READ_HI_SKEW`/`TEST_DESKEW_HI`.
- Host `set_deskew()` (pumice_device -> PHY_TIMING by name) + `train_deskew.py`
  sweep (deskew_lo x deskew_hi, phase-distinct pattern, pick mism==0) +
  `make train-deskew`.
- Integration red->green: refined the model to a per-cycle 1-deep DQ-bus
  pipeline (`_skew_post`, run EVERY dfi cycle incl. idle, via `_skew_cur` set by
  the serve step) so read N's high beat lands on cycle N+1.
  `test_ddr2_char_uart_pagehit_rate4_x16_deskew` (skew=1 + deskew_hi=1) PASSES
  (mism==0); skew=1/deskew=0 fails (the 2/4). Skew-off rate4_x16 stays green.

Removal of the leftover RTL and CSR fields is tracked as PUMICE-007 (issue #39).
