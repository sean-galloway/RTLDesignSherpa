<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# converters — Closed

---

## CONV-006 — upsize paths now support mid-wide-word INCR burst starts
**Status:** closed 2026-08-26 (opened 2026-08-25) — implemented, not just documented
**Priority:** was P2, raised on review: "if a narrow burst starts in the
middle of wide data, BEs must be used with the data being loaded in the
middle" — correct, and now the behavior.

What shipped (RED tests first on both paths):

- `axi_data_upsize` gained `start_lane`: a burst's first narrow beat
  lands at its ADDRESSED lane (data and WSTRB shifted; leading slots
  '0 = byte-disabled, not clobbered); later wide groups start at lane 0.
- `axi4_dwidth_converter_wr` (upsize): AWLEN counts the lane
  (ceil((lane + narrow_beats)/RATIO)), AWADDR passes through unaligned
  (legal AXI — first beat partial in its container), and an AW-lane
  queue feeds the packer. The queue pops on the NARROW side's last
  beat — a wide-side pop raced back-to-back bursts (burst B's first
  narrow beat sampling burst A's stale lane; caught by the bridge
  parallel_storm seed 1787764509, replayed deterministically).
- `axi_data_dnsize` gained `start_lane` (TRACK_BURSTS): the burst's
  first wide word slices from the addressed lane.
- `axi4_dwidth_converter_rd` (upsize): ARLEN counts the lane; issued
  address still aligns down (slave returns whole wide words); the
  burst-length FIFO carries {lane, len}.
- FIXED/WRAP keep the wide-aligned requirement, asserted in sim.

Pinned regressions: `test_unaligned_wide_start` in BOTH dwidth TBs
(lane-correct data + WSTRB + AWLEN/ARLEN; RED against the old RTL on
every upsize config). The DV bridge TB went back to master-width
addressing so unaligned upsize traffic is exercised end-to-end.

Gates: converters run-all-full-parallel 112/112, DV bridge suite 8/8
with storms hammered, RDS bridge suite green.

---

## CONV-007 — axi4_to_axil4_wr: parked burst AW deadlocked a pending single-beat W
**Status:** closed 2026-08-25 — found and fixed same day (RED → GREEN)
**Priority:** was P0 — permanent write-path deadlock under multi-master arbitration

`w_burst_capture = !r_aw_active && s_axi_awvalid && (s_axi_awlen > 0)`
blocked the W path whenever a multi-beat AW was PRESENT, but the block is
only meant for the cycle the burst AW is ACCEPTED. When a single-beat
write was outstanding (its W still crossing the fabric) and a burst AW
arrived and PARKED on the wire — held off by the one-outstanding guard,
awready low — the parked AW blocked the outstanding write's W forever: W
never forwarded → B never generated → outstanding never cleared → the
parked AW never accepted. Fix: add the `s_axi_awready` qualifier.

A lone BFM serializes AW+W and never parks a second AW, so the FUB tests
could not hit the window; the DV bridge parallel_storm's multi-master
arbiter hit it seed-dependently (4 of 6 seeds). Deterministic replay per
(RANDOM_SEED, binary) + a post-mortem signal probe pinned it.

Pinned regression: `test_pending_w_blocked_by_waiting_burst_aw`
(axi4_to_axil4_wr_tb, runs in run_basic for every config) — RED on the
old RTL across all gate configs, GREEN after. The rd shim has no
analogous hazard (its capture is inside the accept branch and there is
no upstream data channel to block).

---

## CONV-003 — dnsize DUAL buffer: dropped beats and misplaced LAST
**Status:** closed OBSOLETE 2026-08-23 — the mode was removed rather than fixed

The defects were real and confined to `DUAL_BUFFER=1`: 36 of 40 beats under
backpressure, and LAST landing early in two other scenarios. Single buffer
was clean throughout.

Nothing instantiated it. Both wrappers hardwired `.DUAL_BUFFER(0)` and a
repo-wide search found no `DUAL_BUFFER(1)` anywhere; the only thing
exercising the path was the test grid, sweeping it out of habit.

It had also stopped earning its place. Dual buffer existed from the initial
commit to cover a real single-buffer throughput gap, and `281de52c`
(2026-05-21) closed that gap by making the single buffer accept its
replacement during the last narrow beat -- the same commit wired both
wrappers to `DUAL_BUFFER(0)`. Measurement confirms there is nothing left to
recover: 0.992 beats/cycle either way.

So the choice was to debug a broken mode nobody used and that measured no
faster, or delete it. Deleted: 186 lines of generate logic, the parameter,
both wrapper pass-throughs, 8 test configurations, a doc chapter and its
diagram.

Both scenarios gated on account of this (`test_burst_tracking`,
`test_backpressure`) are asserted again and green -- DUAL configs were the
only ones failing them.

**If dual buffering is ever wanted again:** it is in git history at
`40e5e116~1`, and it was broken when removed. Reviving it means debugging
it, not restoring it.

---

## CONV-004 — downsize converters truncate AWLEN/ARLEN on long bursts
**Status:** closed FIXED 2026-08-24 — burst splitting on both paths

Both dwidth converters multiplied the slave burst's beat count into the
8-bit length field, wrapping on long bursts: at 2:1 a full 256-beat burst
lost half its data; at 4:1 a 128-beat burst delivered FOUR beats of 512.
Reads timed out short the same way.

Fixed by splitting one slave burst into master bursts of <= 256 beats.
Write path: AW state machine + a split queue (one memory, two read
pointers) feeding per-burst WLAST framing and a worst-case-wins B fold.
Read path: same AR machine plus a one-bit final-flag queue; the only
R-side change is masking m_axi_rlast out of the upsize except on the
final master burst -- safe because 256 narrow beats is a whole number of
wide beats at every ratio.

RED/GREEN on both paths against the committed RTL. The write check
verifies FRAMING (AW lengths, burst legality, WLAST positions), not beat
count -- on the broken RTL all the data still arrived and a count-only
check passed, which is how the unit level stayed blind.

`make run-all-full-parallel`: **112 passed, 0 failed** -- previously
109/3, with the 3 (chain params 6/7/8) never having passed.

The first attempt (2026-08-23, reverted) and what it taught are in the
task history above the work list; the single-counter W framing it tried
is exactly what the split queue replaces.

---

## CONV-005 — dwidth rd RRESP fold used bitwise OR; SLVERR|EXOKAY inflated to DECERR
**Status:** closed FIXED 2026-08-24 — severity-max fold, RED/GREEN

Found by qc round_2, verified against the RTL (ARLOCK passes through, so
EXOKAY is legal traffic), then reproduced: the new
`test_rresp_severity_fold` scenario injects EXOKAY on one narrow
sub-beat and SLVERR on another and asserts the wide RRESP. RED on all 4
downsize configs (DECERR reported), GREEN after changing
`axi_data_upsize`'s SB_OR_MODE fold from bitwise OR to numeric max --
which IS severity order for RRESP. The mode's only instantiation is the
rd converter's RRESP path, and its own comment declared response folding
as its purpose, so the semantics change is a correction, not a break.
The upsize TB's OR-based expectation was updated with the same
rationale. AXI4SlaveRead gained `resp_override` (same convention as the
AXIL4 slaves) to make the injection possible at all.

Width family: 46 passed.

### CONV-009: converters RTL used manual async reset, against the components mandate

**Priority:** P2.
**Status:** FIXED 2026-09-06. All 11 blocks across the four files are on
`ALWAYS_FF_RST`, and the two AXI5-Lite wrappers that had deliberately matched
the old style follow -- so the area is uniform and the mixed-reset
SYNCASYNCNET on the axil4/axil5 chains is gone.

The two `case` arms the macro cannot carry were handled without semantic
change: the read path's folded into its no-op `default`; the write path's
became `default: if (r_wr_state != WR_IDLE)` with its original `default` body
verbatim in the `else`, because that one clears `r_aw_sent` and is not a no-op.

**Verified:** every converter filelist lints clean in BOTH reset builds (the
residual SYNCASYNCNET on the apb chains and UNDRIVEN in axi_data_upsize are
pre-existing and in files this did not touch); converters suite 97 passed,
0 failed.

(The CONV-009 commit message says "149 passed". That was a miscount on my
part -- 149 is the number of cocotb regression lines in the log, not pytest
tests; several test files run more than one cocotb test. The pytest total is
97, and nothing failed either way. Recorded here because the commit message
cannot be corrected.)

That suite was the point. At the time this was written the conversion was
understood to flip 13 flops from asynchronous to SYNCHRONOUS reset in the
default build, matching the rest of the area. **That is no longer what it
does.** On 2026-09-07 `ALWAYS_FF_RST` became unconditionally asynchronous
(`USE_ASYNC_RESET` is now a no-op), so the converted flops kept the
asynchronous assertion the manual blocks always had. The conversion is now a
pure re-spelling here, with no behavioural change at all.

**Raised:** 2026-09-05. Found while adding the AXI5-Lite converters
(`axi4_to_axil5{,_rd,_wr}`): writing the new flops with the mandated macro
made Verilator report `SYNCASYNCNET` on `aresetn`, because the module they
wrap does not use it.

**The rule.** `/GLOBAL_REQUIREMENTS.md` section 1.1 is explicit and marked
MANDATORY - NO EXCEPTIONS: all RTL under `projects/components/` uses
`` `ALWAYS_FF_RST(clk, rst_n, ...) `` with `` `RST_ASSERTED ``, and
`always_ff @(posedge clk or negedge rst_n)` is listed under NOT Allowed.

**What actually violates it** — four files, eleven `always_ff` blocks:

| File | blocks |
|---|---|
| `rtl/axi4_to_axil4_rd.sv` | 4 |
| `rtl/axi4_to_axil4_wr.sv` | 4 |
| `rtl/axi_data_upsize.sv` | 2 (the file already uses the macro elsewhere) |
| `rtl/axi_data_dnsize.sv` | 1 (likewise) |

`bin/update_resets.py` converts all eleven mechanically. That is not the
work; the work is everything the conversion drags with it.

**Why it is not a five-minute change.**

1. ~~**It changes reset behaviour, it does not just re-spell it.**~~
   **No longer true, and the reason is worth keeping.** The concern was that a
   manual `posedge clk or negedge rst_n` block is asynchronous in every build
   while `` `ALWAYS_FF_RST `` was asynchronous only under `USE_ASYNC_RESET`,
   which sim and synth did not set — so the conversion would have flipped
   eleven shipping flops from async to sync. `ALWAYS_FF_RST` is now
   unconditionally asynchronous (see [[build-flows]]), so the two spellings
   are equivalent and the conversion is behaviour-preserving. The suite was
   run behind it regardless, which is why this is recorded as verified rather
   than assumed.

2. **Two `case` arms have to move.** The macro takes the whole body as a
   macro ARGUMENT, so a comma at paren-depth zero inside it splits that
   argument — Verilator says `Define passed too many arguments`. Both
   `axi4_to_axil4_rd.sv` (`RD_BURST, RD_LAST_BEAT:`) and
   `axi4_to_axil4_wr.sv` (`WR_BURST, WR_LAST_BEAT:`) have exactly that. This
   is why no compliant file anywhere in the tree has a multi-label `case` arm
   inside the macro — the macro cannot express one. The read path can fold
   the arm into `default:` (its `default` is an explicit no-op); the write
   path CANNOT, because its `default` does real work (`r_aw_sent <= 1'b0;`),
   so that one needs a genuine restructure and a reviewer.

3. **The MAS quotes this RTL verbatim.** qc round_41 confirmed the quoted
   blocks in `converter_mas` are verbatim-accurate. Changing the reset
   spelling and a `case` arm invalidates those quotes, so the book needs a
   pass in the same change.

**Do it as its own commit, with the converters suite run behind it.** Do not
fold it into a feature change.

**Superseded:** the three AXI5-Lite converters were written in the core's
manual style so a single compiled design would not be half sync-reset and half
async. That hazard no longer exists — every build is async — and those
wrappers are on the macro too.
