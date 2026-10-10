# ISSUE-013: read eye is 10 taps: IDELAY is the only read knob

> **Migrated from `PUMICE-044`** on 2026-09-27, when this area's flat
> `dropped.md` was split into one file per item to match the rest of the vault.
> The legacy ID is cited throughout the repo -- RTL comments, DV code, handbook
> notes, commit messages and session memory -- so it is NOT rewritten at those
> call sites; `vault/Tasks/MIGRATION_MAP.md` and this line are how an old
> `PUMICE-044` reference resolves. Body below is verbatim from the flat page.
>
> Lane chosen by reading this item's own Status line and opening, not its title:
> a keyword pass over the 35 items misclassified 14 of them.



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

**Priority note:** the 10-tap eye has NOT caused a failure. TASK-007's
corruption was DQ collisions (bad beats 36/64 bits wrong = random data); a
marginal eye yields few-bit errors. 039 measured 210 clean runs with this exact
eye. This is margin-hardening, not a defect -- drop to P3.

</details>

---
