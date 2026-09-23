<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# pumice — Closed (done)

## PUMICE-028 — the pumice sim has never run the board's DRAM geometry

**Status:** CLOSED 2026-09-23 — board geometry is in the DEFAULT regression and
passes.

The board is DRAM_BEAT=32 / BL4 / x16, where one DRAM burst is ONE AXI beat.
The suite defaulted to 64 / BL8 / device==beat, where it is four. Every
per-sub-command rate limit is therefore divided by four before a bandwidth
assertion can see it, which is how a 2x read throttle shipped green
([[PUMICE-025]]) and a pinned burst length went unnoticed ([[PUMICE-041]]).

### Closed because the shipping geometry is now GATED, not merely reachable

`run-all-gate`, `run-all-func` and `run-all-full` — the three names
`projects/components/Makefile` invokes — each run the normal pass and then
re-run the `top` area at the board geometry. Verified 2026-09-23:

    OK: run-all-gate passed at BOTH geometries
    board geometry: 188 passed

Top area only: the geometry constants live in `dv/tests/top` and size the
elaborated RTL there; `fub/` and `macro/` do not read them, so a second pass
would rebuild identical designs for no coverage. A second INVOCATION rather
than a parametrization, because the geometry is read at IMPORT time into module
constants — one process holds exactly one geometry. That is the property that
made PUMICE-041 invisible, used deliberately.

### What it took, and what it found

Nine thresholds and one RTL defect, all invisible at the sim geometry:

- `_mkaddr` shifted by a hardcoded 3 while the RTL decodes at device-word
  granularity (`clog2(DRAM_DEVICE_WIDTH/8)` = 1 on the board), so 256 bursts
  meant for 8 banks landed on 2.
- `t_ccd_i` hardcoded 4 ("BL8 at DFI_RATE 2"); a BL4 x16 burst is ONE DFI word.
  Write utilization 27.56% -> 99.22%.
- `DFISlavePHY(beats_per_burst=BL)` is the framework's K=1 override; the board
  needs BL/K with K=2. Every read timed out and the checker blamed refresh.
- R-beat accounting off by a burst, which hid a same-edge coroutine race that
  dropped the last beat at BOTH geometries.
- Five utilization floors tuned at BL_WORDS=4 — command-bus ceiling,
  single-bank, in_order AP/non-AP, W run-length, pref_row_first. Four are
  beats-per-access numbers and scale by BL_WORDS/4; pref_row_first is capped
  near 50% by construction at one column per access.
- And the real one: **write batching starved reads** ([[PUMICE-039]], fixed in
  `fc83c1b3c`). Sixteen `concurrent_rw[bl4x16]` cells failed with one read beat
  never returning. That defect was in SHIPPING DEFAULT configuration
  (`wr_high_wm` resets to 2) and no BL8 test could see it.

That last item is the task's whole justification, delivered: the suite could
not express the shape that ships, so a read-starvation bug lived in the default
configuration undetected.

### Not closed with this

`DFI_DATA_WIDTH` 128 vs 64 and `dfi_cmd_path`'s DFI_RATE=4 were named here and
never investigated. They are small and unattached to anything; re-file if they
ever matter.

---

**[archived heading] PUMICE-028 — the pumice sim has never run the board's DRAM geometry
**[archived] Status:** open 2026-09-10  **Priority:** P1 — this is why a 2x read throttle shipped green

### 2026-09-20: root-caused and substantially answered

This task's title was literally true and the cause is now known: the char
harness built the RTL from a module-level `DRAM_BL` captured at IMPORT while
pushing the per-test value only to the BFM, so a "BL4" cell ran the controller
at BL8. One line in `_run` (see [[PUMICE-041]], closed). With it fixed the char
sim runs the board's exact geometry -- DFI_RATE=2, 32b beat, x16 device, BL4 --
and `concurrent_gap_board` passes clean at gaps 0/8/13/15.

What REMAINS of this task is the question it really poses: which other cells
still do not run board geometry, and is anything else pinned by an import-time
constant the same way? The bug class -- a per-test value that reaches the
testbench but not the elaborated RTL -- is worth sweeping for, not just this
instance. Check it by reading ELABORATED parameter values out of the generated
build (`grep u_ctrl__DOT__<PARAM>` in local_sim_build/*/Vtop*.h), which is how
this one was caught; comparing the test's arguments against its intent would
have missed it, because the arguments were right.

`dv/tests/top/test_pumice_core_dfi.py` ran at DRAM_BEAT=64 / BL8 / device==beat,
so **one DRAM burst is 4 AXI beats**. The board is DRAM_BEAT=32 / BL4 / x16,
where **one DRAM burst is 1 AXI beat**. Any per-sub-command rate limit is
therefore divided by four before a bandwidth assertion can see it: the read
intake's admit gate (PUMICE-025, fixed) supplied 2 beats/cycle at the sim
geometry and looked healthy, while on the board the same gate WAS the
bandwidth. Every read/write ceiling test passed throughout.

The geometry is now env-overridable (`TEST_DRAM_BEAT` / `TEST_DRAM_BL` /
`TEST_DRAM_DEVICE_W`, defaults unchanged) and `pumice_core_tb_top` takes
`DRAM_DEVICE_WIDTH`. **But the board point does not yet run clean**, so it is
not wired into the suite:

- `read_ceiling` at board geometry trips `pumice_dfi_rd_return_checker` --
  "32 reads outstanding for 512 cyc with no return".
- `write_ceiling` at board geometry stalls W for 1409 cycles (max run 19),
  while the real board sustains 95% of peak on writes. So the failure is the
  testbench or its DFI model, not the DUT.

**Do:** make `TEST_DRAM_BEAT=32 TEST_DRAM_BL=4 TEST_DRAM_DEVICE_W=16` a clean,
routinely-run configuration of the core suite (the write ceiling is the
control: it must reproduce the board's ~95%), then add it to the regression so
board geometry is covered by default. Until then `[[project_pumice_char_suite]]`
board numbers are the only place these limits are visible.

**Why it matters:** the handbook rule is already "match the FPGA exactly in
sim"; this is the case that proves the cost of not doing it. A suite that
cannot express the shipping geometry cannot gate it.

### 2026-09-20 (later): the sweep half is DONE -- 041 was the only instance

`bin/check_pinned_rtl_params.py` (new) decides, for every value in a
`parameters=` dict, whether it is reachable from the enclosing function's
arguments or locals. Unreachable means the elaborated RTL cannot vary per test,
which is the PUMICE-041 shape. It carries a `--self-test` that reconstructs
that defect in six lines and requires the checker to fail on it -- run on every
invocation, because a checker that cannot fail reports "0 violations" over a
suite it is not inspecting.

Repo-wide, 582 test files: **2012 RTL parameters examined, 888 pinned, 0 pinned
with a parametrized twin.** Three candidates surfaced before the twin rule was
tightened (`MECID_WIDTH`/`NSAID_WIDTH` vs `id_width`, `APB_DATA_WIDTH` vs
`data_width`) and all three were substring collisions between genuinely
independent quantities; the rule now suppresses a twin that already supplies
some other parameter in the same dict. **PUMICE-041 was the only instance of
the bug class.**

### What the sweep found instead: pinned values that are not the board's

The bug class is closed; the geometry gap is not, and it is wider than this
task recorded. Board truth is `build-perf/rtl/ddr2_char_top.sv` (ROW_WIDTH 13
at line 37, the rest at 216-233):

| parameter | board | what the unit suite elaborates |
|---|---|---|
| ROW_WIDTH | **13** | 14 (every test) |
| DRAM_BEAT_WIDTH | **32** | 64 |
| DRAM_DEVICE_WIDTH | **16** | 64 (defaults to beat width) |
| DRAM_BL | **4** | 8 |
| DFI_DATA_WIDTH | **64** | 128 (`dfi_rd_aligner`, `dfi_wr_serializer`) |
| DFI_RATE | 2 | 2, except `dfi_cmd_path` at 4 |
| COL_WIDTH / NUM_BANKS / NUM_RANKS / AXI_ID_WIDTH / AXI_DATA_WIDTH | 10 / 8 / 1 / 8 / 64 | match |

**ROW_WIDTH=13 is new** -- this task only ever named beat/BL/device width. The
harness overrides it deliberately ("so it never issues an out-of-range row"),
so 13 is the shipping width of the address mapper and no sim has elaborated it.
`test_addr_mapper` now takes `TEST_ROW_WIDTH` (default 14, unchanged) and is
**clean at 13**: 5 passed at each, with the elaborated value confirmed
different out of the build (`ROW_WIDTH = 0x0000000e` vs `0x0000000d`) so the
override is load-bearing rather than a no-op.

### 2026-09-20 (later still): both blockers were TB bugs; board geometry 14/18

The two blocking failures were exactly what this task predicted -- testbench,
not DUT -- and both came from the same root: a value hardcoded for the case
where the DRAM beat equals the device word. Fixed in `115e0d824`:

* `_mkaddr` shifted by a hardcoded 3 while `pumice_core` decodes at device-word
  granularity (`$clog2(DRAM_DEVICE_WIDTH/8)` = 1 on the board). 256 bursts
  meant for 8 banks landed on **2**; the write stream lost the bank
  parallelism it measures and stalled on row conflicts -- that was the 1409
  cycles with 18-19 cycle runs.
* `t_ccd_i` was 4 ("BL8 at DFI_RATE 2"). A BL4 x16 burst is ONE DFI word, so
  every column command sat four cycles apart. Write utilization **27.56% ->
  99.22%**.
* `DFISlavePHY(beats_per_burst=BL)` is the framework's documented K=1
  override; the board needs BL/K with K = beat/device = 2. The model waited
  for phases the DUT never drives, so every read timed out -- that is the
  "32 reads outstanding, no return" the checker blamed on refresh drain.
* R-beat accounting lost a burst to the tracker's deliberate late arming
  (hidden by a `beats - BL_WORDS` tolerance while a burst was 4 beats), and
  fixing it exposed a same-edge race that dropped the last beat at BOTH
  geometries.

Two assertions were mis-normalized rather than wrong: starvation was bounded
as a share of the active window, which grades the geometry (identical driver
reads 2.9% at BL_WORDS=4 and 9.8% at BL_WORDS=1) and loosens as the DUT slows,
since refresh inflates the window; it is per-burst plus per-refresh now,
calibrated at 0.117 cyc/burst and 2.75 cyc/refresh. Write backpressure
required exactly 0, but at BL_WORDS=1 supply and drain are exactly
rate-matched (one AXI beat IS one DRAM burst, tCCD=1), so the opening ACTs
leave the write CAM one entry behind and it resyncs once: 2 cycles at burst
44, the same burst at n=256 and n=1024, with AW held and the DFI write side
ready. Fixed cost, bounded by a constant.

**Default geometry 18/18** (unchanged, and still the only configuration the
suite gates). **Board geometry 14/18**, from "cannot run the ceilings at all".

### 2026-09-20 (final): 16/18 at board geometry; the residue is PUMICE-046

Three of the four below were thresholds and are fixed in `4a729f568`:
`read_inflight`'s floor is derived from Little's law scaled by BL_WORDS (and
from the NOMINAL ring depth, not the built one, so the
`PUMICE_RD_RET_DEPTH=8` mutation still fails at BOTH geometries -- verified);
`refresh_bubbles` attributes on refresh-SIZED runs plus a majority-of-cycles
check instead of raw run count; and both paging tests assert against the
measured command-bus ceiling (`BL_WORDS / cmds_per_access`) where a flat 100%
is unreachable, leaving the default-geometry gate untouched.

The fourth was NOT a threshold. The close-page family reaches only ~63% of its
own command-bus ceiling and that is now **[[PUMICE-046]]**, with the tRRD /
tRCD evidence that rules out DRAM timing. The two paging tests fail at board
geometry reporting it by name -- deliberately, rather than being tuned green.

**Default 18/18. Board 16/18.** Remaining for THIS task: resolve or accept
PUMICE-046, then wire board geometry into the regression. `DFI_DATA_WIDTH` 128
vs 64 and `dfi_cmd_path`'s DFI_RATE=4 are still un-investigated.

### The four that were left (superseded by the entry above)

Same class again -- thresholds that assume the default geometry -- so none is
a DUT defect, but each needs its own measurement rather than a blanket
loosening:

1. `perf_read_inflight`: 0.30 beats/cycle against a **0.85 floor** under
   200-cycle read latency. At BL_WORDS=1 a read burst is ONE beat, so covering
   a 200-cycle round trip needs ~200 beats in flight and the ring holds 32.
   The floor is only reachable when a burst is 4 beats wide; it needs to be
   expressed against `outstanding x BL_WORDS / latency`.
2. `perf_refresh_bubbles`: "41 separate stall runs for only 10 refreshes".
   At tCCD=1 any perturbation opens its own stall run, so run COUNT stops
   tracking refresh count; the attribution test needs to be on stalled cycles
   or on run length, not on how many runs there are.
3. `perf_paging_sweep` and 4. `perf_paging_sched_cross`: both require **100%**
   write utilization. Board geometry tops out at 98.97% for the rate-match
   resync characterized above, so an exact-100% requirement cannot hold there.
   (`static_close` at 30.77% is a separate question and may be real.)

### 2026-09-22: core_dfi is 18/18 at BOTH geometries; the target is wired

`test_pumice_core_dfi.py` passes 18/18 at the default geometry AND at
`TEST_DRAM_BEAT=32 TEST_DRAM_BL=4 TEST_DRAM_DEVICE_W=16`. Board geometry is now
a first-class regression target rather than something a session has to know to
set:

    make run-board-geom        # the top suite at the shipping geometry
    make run-all-func-both     # default AND board, both reported

It has to be a SECOND INVOCATION, not a pytest parametrization: the geometry is
read at import time into module constants that size the elaborated RTL, so one
process holds exactly one geometry. That is the property that made
[[PUMICE-041]] invisible, used deliberately.

Five more thresholds were tuned at BL_WORDS=4 and had to be derived instead.
Four are beats-per-access numbers and scale by `BL_WORDS/4` (`GEOM_UTIL_SCALE`):
the command-bus ceiling, the single-bank floor (0.20), the in_order floors
(0.30/0.75) and the W run-length claim. The fifth, `pref_row_first`, is capped
near 50% by construction at one column per access -- ACT-over-COL wins at most
every other slot -- so it floors at 0.40 rather than 0.75. Default values are
unchanged in every case.

### What is STILL open, and it is this task's original claim

`make run-board-geom` runs the WHOLE top area, and `test_pumice_top.py` fails
**16 `concurrent_rw[bl4x16]` cells** (read latencies 2 and 7, both refresh
settings):

    TimeoutError: engine-style RD R-wait: {12: 1} beats short after 1000000 cycles

One read beat lost under concurrent read+write at the board geometry.
Deterministic -- same beat index, same runtime to the second across runs, so it
is not a flake.

**NOT caused by [[PUMICE-046]]'s arbiter change.** Verified by running the
identical cell in a worktree at `d11a0aee8`, the commit immediately before
`8b06686af`: byte-identical failure, `{12: 1}` and 347s both sides. The
char-framework board gate does not cover these cells, so "gate green" was never
evidence for this path.

This is the same thing [[PUMICE-037]]'s closure recorded on 2026-09-14 -- "the
board point does not yet run clean in sim", written when the suite could only
build DRAM_BL=8. It still holds. The suite can now EXPRESS the geometry, which
is what made the failure visible; it does not yet PASS it.

**Do:** bisect the 16 `concurrent_rw[bl4x16]` cells to a first-bad commit (the
test is deterministic, so bisect is cheap), then fix. `DFI_DATA_WIDTH` 128 vs
64 and `dfi_cmd_path`'s DFI_RATE=4 remain un-investigated.



---


---

## PUMICE-041 — the char sim never BUILT BL4 (title was wrong; one-line harness bug)
**Status:** CLOSED 2026-09-20  **Priority:** was P1

`test_ddr2_char_char_concurrent_gap_board` (BL4, x16, DFI_RATE=2 -- the
geometry silicon ships) stalls: only 8 of 64 reads return (the outstanding
limit), at every gap INCLUDING 0, which the board passes. Reproduces with
`read_en_gated` on or off, so it is not the gating added in 3e179015e.

The board runs BL4 fine, so this is a char-sim model gap. It matters because it
is why BL4 went untested for so long: `DRAM_BL` was a literal 8 under a comment
asserting BL8 was what the board ran, so no test in that suite could reach the
board's geometry, and "the char sim does not reproduce PUMICE-037" was recorded
as a property of the DEFECT when it was a property of the TEST.

Marked xfail(strict) so it converts back to a real test the moment BL4 works.

### 2026-09-18: the RECORDED SYMPTOM IS WRONG -- measured signature below

This task has said since it was filed: "only 8 of 64 reads return (the
outstanding limit, then stall)". That prose was never produced by a run; it is
the xfail reason, and I repeated it several times today as if it were data.
Measured with CONCURRENT_DUMP at gap 0 (BL4, rate 2, beat 4B, dev 2B, txn 64):

    gap=0 ok=False mismatched=61 bytes=4096
    notes=('read engines did not complete',
           '61 beats mismatched',
           '1:1 VIOLATION: hist total 8 != 64',
           'concurrent 1w+1r of 4w+4r built, region 0x1000')

So: **61 of 64 beats are WRONG**, and the 8 is the read-latency HISTOGRAM
total, not reads returned and not the outstanding limit. "8 of 64 reads return
then stall" and "nearly every beat comes back wrong while the histogram only
records 8" are different bugs and point at different code. Chase the measured
one.

### 2026-09-18: read_bl_anchored is NOT the fix (tested)

The BFM's short-burst phase-anchoring model was the leading candidate:
`DFITimingProfile.a7ddrphy_bl4` sets `read_bl_anchored=True` and the char TB
never did (it builds its own `char_gated` profile). Added
`CHAR_READ_BL_ANCHORED` (default 0, nothing moves) and ran BL4 with it on:

    IDENTICAL failure -- still xfail, same signature.

Hypothesis eliminated. It is consistent with the nphases arithmetic: the preset
documents BL4 at nphases=4, but this board is nphases=2, where
words_per_cycle = dfi_rate * words_per_beat = 2*2 = 4 and a BL4 burst is 4
device words = exactly ONE full DFI cycle. Nothing under-fills, so there is
nothing to anchor. Do not re-try this.

### 2026-09-20 RESULT: burst length is the SOLE variable

Ran the controlled comparison. Added `test_ddr2_char_char_concurrent_gap_board_bl8`
-- the failing cell's twin, identical except `dram_bl=8`. Same scenario,
geometry, gaps, txn count, bytes moved; one variable changed:

    BL8:  ok=True   mismatched=0    1 passed
    BL4:  ok=False  mismatched=61   1 xfailed   '1:1 VIOLATION: hist total 8 != 64'

Until now the evidence was concurrent_gap_board (BL4, fails) vs families_x16
(BL8, passes), which differ in BOTH burst length and scenario, so neither could
attribute the failure. **It is BL.**

The BL8 aligner trace is the useful half:

    RD_ALIGNER probe: valids=512 captured=512 blocked_pre=0 blocked_real=0

Every returned beat captured, nothing blocked, under the EXACT concurrent
traffic that breaks BL4. So the read-return path is sound and the divergence is
burst-length-specific -- consistent with the BFM's per-RD column queuing, where
BL8 spans two due_cycles (k//words_per_cycle, k=0..7, words_per_cycle=4) and
BL4 collapses to exactly one.

The twin is deliberately NOT xfail: its verdict is the measurement, and it is
now a permanent control -- if BL8 ever starts failing too, the attribution
above is void and the fault moved to the scenario.

### STILL UNEXPLAINED -- resolve before proposing a fix

The BFM's per-RD column queuing and the aligner's `ceil(BL/DFI_RATE)` enable
window disagree by 2x at BOTH burst lengths (BL8: 2 cycles queued vs a 4-cycle
window; BL4: 1 vs 2). **Yet BL8 passes.** Why the same 2x discrepancy is
harmless at BL8 and fatal at BL4 is the open question. Any BL4 fix proposed
before that is answered is a story fitted to one data point.

### CLOSED 2026-09-20 -- it was never the read path

`_run` pushed the per-test `dram_bl` into extra_env for the cocotb/BFM side but
built the RTL from the MODULE-LEVEL `DRAM_BL`, which is read from the
environment at IMPORT time and is therefore always the default 8:

    line  97:  DRAM_BL = int(os.environ.get("TEST_DRAM_BL", "8"))   # at import
    line 375:  "TEST_DRAM_BL": str(bl)                              # -> BFM, correct
    line 398:  "DRAM_BL": str(DRAM_BL)                              # -> RTL, WRONG

So a "BL4" cell built the CONTROLLER AT BL8 and told the DRAM model BL4. Proven
by the elaborated values, which were byte-identical between the BL4 and BL8
cells before the fix:

    before:  DRAM_BL=8U  BL_WORDS=2U  RD_EN_CYC=2U
    after:   DRAM_BL=4U  BL_WORDS=1U  RD_EN_CYC=1U

The BFM returns one DFI word per BL4 read; the aligner captures BL_WORDS per
read and the BL_WORDS-th retires it, so it waited forever for a second word.
Hence "hist total 8 != 64", 61 of 64 beats bad, at EVERY gap including 0.

**Result with the RTL actually built at BL4** -- all four gaps, the PUMICE-037
regime included:

    gap=0  ok=True mismatched=0      gap=13 ok=True mismatched=0
    gap=8  ok=True mismatched=0      gap=15 ok=True mismatched=0

xfail(strict) removed; the cell is a normal passing test.

**Every oddity the task recorded is explained by this and nothing else:**
  * the board runs BL4 fine -- the board BUILDS the RTL at BL4;
  * the failure was gap-independent -- the geometry was mismatched from cycle
    zero, so traffic never mattered;
  * `BEATS_PER_BURST = DRAM_BL` looked right and BL/K "broke" families_x16 --
    that cell was also silently running RTL at 8;
  * `read_bl_anchored` changed nothing -- it was never the model.

**The title was wrong in the same way the symptom was.** Twice this task
described a measurement nobody had taken: "only 8 of 64 reads return" was xfail
prose (the 8 is a histogram total), and "BL4 read path does not work" was an
inference from a cell that never built BL4. See also [[PUMICE-028]], which says
the same thing from the other direction and is now substantially answered.

## PUMICE-043 — batching residue at the aggressive watermark
**Status:** CLOSED 2026-09-17 (508f98200)  **Priority:** P2

With PUMICE-042 fixed, write batching is clean at hi=2/lo=1 (0 mismatched
across 8 reps at gap 15). At **hi=8/lo=4** one run in eight returns a single
mismatched beat: `[0,0,0,1,0,0,0,0]`.

NOT dismissed as noise. A single beat is exactly what PUMICE-037's residue
looked like before it turned out to be failing 8 of 10 reps, and this repo's
standing rule is that intermittent means a real bug.

Low practical urgency: hi=2/lo=1 is both cleaner AND faster (+29.9% vs +18.4%
at gap 12), so nothing needs the aggressive setting. It matters as evidence
that something still depends on drain depth -- a deeper drain means a longer
uninterrupted write run, so the suspect is whatever accumulates over that run
rather than the turnaround itself, which 042 now covers.

Repeat every point: a single pass cannot distinguish 0% from 12%.

### CLOSED 2026-09-17 -- it was the one-cycle turnaround seam

Retested at the EXACT configuration (hi=8/lo=4, gap 15, 1+1, txn=2000) with 30
reps instead of 8:

    hi=0 (control)   0/30 failing   209.3 MB/s
    hi=2/lo=1        0/30 failing   262.8 MB/s
    hi=8/lo=4        0/30 failing   257.4 MB/s   <- the PUMICE-043 point

At the observed 12.5% rate (1 beat in 1/8) the chance of 30 clean reps by luck
is **1.8%**, so this is evidence rather than a short-run fluke. The task's own
rule -- "repeat every point: a single pass cannot distinguish 0% from 12%" --
cuts both ways, and is why 4 reps (59% chance of a false clean) would not have
settled it.

**Cause: the one-cycle seam in the arbiter's turnaround guard** (PUMICE-039,
fixed 508f98200). `r_rdfire0` records a fire the cycle AFTER it happens while
the pick runs the cycle BEFORE its own fire, so a WRITE picked in the very cycle
a READ fired out issued one cycle behind it -- a gap-1 RD->WR against tRTW=20.

That explains the drain-depth dependence this task recorded as its key clue: a
deeper drain (hi=8) means more write-run boundaries, hence more chances to hit
the seam. It is also why hi=8 was consistently worse than hi=2 -- originally,
and again mid-fix (5/30 vs 3/30 on 2026-09-17). The suspect named here was
"whatever accumulates over that run"; the real answer was the number of
direction crossings, not accumulation.

## PUMICE-040 — read alignment wastes 5 cycles of latency
**Status:** CLOSED 2026-09-16 (6ba9dba62)  **Priority:** P2

A joint (t_rddata_en x rddata_delay) board sweep found EVERY clean pair on the
diagonal `rddata_delay = t_rddata_en + 1` -- the a7ddrphy's data-vs-valid offset
is a fixed 1 cycle, so any t_rddata_en works provided the delay tracks it.

The board runs rden=6/delay=7. rden=1/delay=2 is equally clean and **5 cycles
faster**, putting DFI read latency at ~7-8 -- matching LiteDRAM's
`read_latency = cl_sys_latency + 6 = 8` on the same board.

A single-axis sweep converges on working-but-slow and nothing flags it: the
a7ddrphy's DQ capture free-runs and rddata_en only gates WHEN VALID IS EMITTED,
so a late rddata_en does not corrupt reads, and rddata_delay silently absorbs
the cost. `TEST_T_RDDATA_EN` makes the faster point reachable.

LATENCY ONLY. It does NOT reduce tRTW -- proven on the board: at rden=1/delay=2
with tRTW=8, gaps 13/15 failed exactly as before the fix, while tRTW=18 was
clean at both alignments.

**Moved to this page 2026-09-16.** It was fixed and marked CLOSED in its own
status line, with the commit named, but stayed on the OPEN page -- so every
count and every "what is left" listing carried it as outstanding work.

---

## PUMICE-014 — retire ALL hand-poking of valid/ready interfaces in pumice DV
**Status:** CLOSED 2026-08-29 — COMPLETE. No hand-driven handshake
remains anywhere in pumice DV. The two remaining are deliberate
exclusions with reasons, not leftovers — see below. HARD RULE from Sean:
"None of the environments should EVER hand poke on any standard interface
or valid ready interface", and "If there are bfms you don't need to set any
signals" — the BFM drives the PAYLOAD too, not just the handshake.
See [[feedback-always-use-axi4-bfms]].

**DONE (0 handshake pokes remaining; residual counts are non-handshakes):**
top: `test_pumice_core_dfi` (50→0), `test_pumice_core` (33→0),
`test_pumice_top_csr` (22→0), `test_pumice_top` / `_geared` (2 ea→0).
fub/macro: `pumice_axi4_ifc_tb` (35→0), `pumice_wr_intake_tb` (34→0),
`pumice_rd_intake_tb` (32→0), `pumice_wr_data_cam_tb` (17→6),
`pumice_rd_cmd_cam_tb` (13→3), `pumice_dfi_cdc_tb` (12→0),
`test_pumice_dfi_cmd_path` (8→2), `pumice_cmd_arbiter_tb` (7→0),
`test_pumice_dfi_wr_serializer` (6→0), `pumice_mem_cmd_scheduler_tb` (3→0).

**Collateral to reuse, do not re-roll:**
* `dv/tbclasses/pumice_axi_bfm.py` — `PumiceAxiBfm`, the one place any
  pumice `s_axi_*` is driven. `write=`/`read=` for single-direction ports.
* `dv/tbclasses/pumice_fub_bfm.py` — `fub_consumer()` / `fub_producer()`
  over the GAXI BFMs for fub-internal valid/ready ports, with an explicit
  `signal_map` (pumice's `aw_push_bank_o` style names do not match GAXI
  auto-discovery, and explicit fails loudly on a rename).

**The two deferred files were FINISHED 2026-08-29**, not waived. Both had
the same root problem -- the MEASUREMENT, not the driver -- and the same fix:
rebase onto the OBSERVED handshake cycle instead of a fixed offset from when
the testbench presented. That is BFM-compatible and more honest (it measures
the DUT's latency, not latency-from-the-testbench).
  * `test_pumice_dfi_rd_aligner.py` — `_CycleObs` records op fires and
    rddata_en cycles; t_rddata_en checked as (en - fire), and the tCCD case
    asserts OUTPUT gaps track INPUT gaps rather than hardcoding 2. Pacing
    comes from the `fixed` valid_delay profile.
  * `dfi_cmd_formatter_tb.py` — `_watch_fire` counts accepts; the check
    samples once the accept is observed, with NO extra cycle (the outputs are
    registered from the accepted command, so an extra wait sampled after
    valid dropped -- that was why the first attempt failed).
  Both mutation-checked: firing a read a cycle early (the ILA-confirmed
  silicon bug) fails the aligner tests; corrupting the bank encoding fails
  9 of 10 formatter tests.

**Not handshakes — verified against the RTL port lists, leave hand-driven:**
CREDITS with no matching valid — `rd_op_ready_i` ("rd aligner has a free
slot"), `bank_act_ready_i` / `bank_rdwr_ready_i` / `bank_pre_ready_i`
(per-bank permission vectors). STROBES with no ready — `wr_done_valid_i`,
`dfi_rddata_valid_i` (DFI read data is unconditional per spec),
`init_cmd_valid_i`, `sched_lu_valid_i`, `snarf_probe_valid_i`,
`wr_fire_i`. Read-only MONITORS also stay (`_mon_b`, `_mon_r`): the AXI
master owns bready/rready but the sequence result carries no per-beat
rid/rlast/rresp/bresp. Observing is not poking.

**Two traps that cost real time — read before the next port:**
1. **Queue-and-go vs blocking send.** `send()` blocks until its packet is
   accepted, so awaiting per beat leaves a GAP between beats. A hand-rolled
   "present the head every cycle" source is always-valid; to match it use
   `_driver_send` (queues and returns). The wr-serializer tCCD test
   measures gaps between `wrdata_en` pulses and read 3 where 2 was
   required until this was fixed.
2. **`ready_policy` is not the `backtoback` profile.** GAXISlave's default
   `valid_first` waits for valid on a CLOCKED loop, so ready lands a cycle
   LATE even at ready_delay 0. Use `ready_policy='always'` to model a TB
   that used to tie ready to constant 1, and `'stall'` +
   `set_ready_policy()` for deterministic consumer backpressure.
   (RDS-DV c220c19 / aacb90d / 5fcf039.)

**Whenever GAXI changes, run all of val/amba** (Sean). Baseline for A/B:
739-741 passed / 2-4 failed at `-n 24` with SEED pinned, and the failing
set is NOT stable run to run — see [[AMBA-MONRATE-INTERMITTENT]]. Do not
read a single differing failure as a regression.

**Also outside pumice (same rule, flagged not owned):**
`projects/components/misc/dv/tbclasses/axi4_slave_wr_crc_check_tb.py`.

**Rule going forward:** no NEW test may hand-poke a valid/ready interface.

## PUMICE-015 — greppable structure trackers (CAMs / page policy / refresh / scheduler)
**Status:** DONE 2026-08-27 — the infrastructure already existed
(`dv/tbclasses/trackers/`, predating the request); this closed the gap
between it and the rearchitected RTL, added the missing structures, and
proved it live. Method note: [[structure-trackers]].

**What was wrong** (nothing had run the trackers since the rearchitecture,
so the rot was invisible):
- `page_predictor_tracker` targeted a DELETED fub (retired with
  HAPPY_HYBRID) — removed.
- `xbank_timers` / `rd_cl_aligner` / `wr_beat_sequencer` targeted RENAMED
  fubs (`pumice_bank_timers`, `pumice_dfi_rd_aligner`,
  `pumice_dfi_wr_serializer`) and read signals that no longer exist —
  retargeted (`btmr` short name; emit-stall + wd handshake taps).
- `scheduler_tracker` targeted the pre-rearchitecture FSM scheduler —
  retargeted to `pumice_cmd_arbiter` and given the Axis-1 POLICY view
  (ORDER/PREF/ROWSEL/COLSEL/PRIO/QOS/WRDRAIN emit-on-change), so a pick
  can be explained and not just observed.
- EVERY tracker hard-coded `mc_clk` while the rearchitected fubs use
  `aclk` — the first one to run killed the test with an AttributeError.
  Fixed centrally: `tracker_clock()` resolves by name, and `guard_run()`
  wraps every run() so a signal miss disables THAT tracker instead of
  failing the sim (instrumentation must never turn a green run red).
- `wire_trackers`'s hierarchy map still pointed at pre-rearchitecture
  instance paths — updated to `u_sched.u_arbiter` / `u_ifc.u_rd_cam` / etc.

**What was added:**
- `page_policy_tracker` (`pgpol`) — the Axis-2 decisions: mode changes,
  per-bank ap-mask edges, timeout-PRE requests, page hit/miss/empty, plus
  the rbl (modes 6/7) and row-pred (mode 5) verdicts read through the
  child instances.
- `cam_tracker` (`camrd` / `camwr`) — entry lifecycle
  INSERT/ISSUE|COMMIT/DRAIN|DONE, CAM-full INS_STALL, and OCC_<n>
  occupancy (the population the write watermarks and most/fewest_pending
  selects key off).
- `refresh_tracker` extended for the v3 work: pull-in CREDIT_<n>, burst
  DRAIN_ON/OFF, REFab-vs-REFpb KIND, and `rotor_advances()` — the exact
  check that catches a desynchronized REFpb rotor mirror.

**Usage:** `PUMICE_TRACKERS=1 pytest <test>` wires them in the core TB;
each writes `<sim_build>/<short>.out`. Off by default.

**Proof (clean run of test_pumice_core_rbl):** all ten trackers wrote live
logs; `pgpol` reproduced the test's arms exactly
(MODE_0 -> MODE_6 -> RBL_LOWLOC(b3) -> MODE_7 -> MODE_0), both CAMs
conserved (45 INSERT = 45 ISSUE/COMMIT = 45 retire), and sched EVT_ACT
(59) matched btmr ROW_ACTIVE_SET (59).

**Remaining (optional, not blocking):** no tracker yet for
`pumice_axi_burst_chopper` / `pumice_wr_splitter` (front-end burst
framing) or the DFI CDC; add them if a front-end bug ever needs the same
cross-structure view.

## PUMICE-001 — Runtime-config axes corrupt data (board + sim)
**Status:** closed 2026-08-25 — board re-validated on the fresh bitstream; matrix 65/70 with the 5 residuals split to PUMICE-020 (observability only). Issue #42.

**Fixes landed 2026-07-23 (commit fab57682):**
- `pumice_cmd_arbiter`: auto-precharge column guard. Under CLOSE the xDA
  precharges the bank as part of the access, but the generic guard deliberately
  does not gate columns against columns and `r_bank_row_active` is a cycle
  stale, so the next entry on the same bank+row still saw "row active" and
  issued a second column into a bank already committed to precharge. On the
  DRAM that column has no open row and the access lands wherever the device
  last had one (batch-2 row-1 writes landed on row 0, clobbering batch 1 —
  64 beats / 48 unique). Guards the bank for 2 cycles after a fired AP column,
  exactly as `r_guard0/1` do for ACT/PRE. No-op under OPEN/HYBRID.
- `pumice_top`: `REFRESH_TUNING.page_policy_or` carries the SOFTWARE encoding
  (0=build default, 1=OPEN, 2=CLOSE, 3=HYBRID) while `page_policy_e` is
  OPEN=0/CLOSE=1/HYBRID=2. The raw cast made software-OPEN run CLOSE and
  software-CLOSE run HYBRID — the entire open_page/reorder config-axis
  corruption keyed off this.

Verified: `pumice_cmd_arbiter` FUB passes on a clean build; macro+top 54 passed
(the 1 failure is PUMICE-002, pre-existing).

**Still open:** board re-run of the config-axis families on a rebuilt bitstream.

**Board baseline (2026-07-22, first rearch config-axis run):** baseline/inorder
9/14 (col_major fails only at scale 1000); bank_interleave / open_page /
reorder 0/14. multiid showed 7 EXTRA read returns (hist 64007 != 64000) —
suspect rd-CAM duplicate issue under reorder. Correctness at the baseline
config is SOLID (soak gate green); these are the runtime
page-policy/scheme/reorder paths.

Full map + signatures:
`projects/fpga-systems/NexysA7/pumice/ddr2-characterization/char_results/FINDINGS_pumice_board_2026-07-22.md`
(+ `char_2026-07-22_wrapup.csv`). Tools: CMD_HISTORY_EN checker,
dfi_rd_return_checker, ILA flow.

**Sim repro available:** `test_ddr2_char_char_families` fails the
bank_interleave family over the DFI loopback — the config-axis defect is
digital and wave-debuggable in sim; start there, no board required.
See PUMICE-003, same class.

**Board re-validation (2026-08-25, bitstream 3159cd6b, unit 210292BFA3EE,
releveled bitslip0/tap7/eye0..14):**
- init + write_read integrity clean; smoke@1000 initially 4/6 — bank_interleave
  32000/32000 beats mismatched, which root-caused to the HOST, not RTL: the
  burst_cols formula counted pumice-beat units where ADDR_MAP.bank_lsb is
  DEVICE-WORD granular, so x16 got bank_lsb=1 (needs 2) and every burst striped
  across banks. Invisible at device==beat, which is why the sim families test
  passed — new `test_ddr2_char_char_families_x16` reproduces it (RED 60 beats)
  and pins the class; one-line fix (BOARD_BURST_COLS = BL) → sim GREEN, board
  smoke 6/6, bank_interleave BW 33→65 MB/s (7.5–7.8x baseline).
- matrix@1000 then 45/70: every col_major-family point failing on ALL configs —
  proven a CHECKER ARTIFACT by exact arithmetic: the 64000-txn x 16 KiB walk is
  1 GiB over a 128 MiB device; mismatched beats = 55808*BL mod 2^16 =
  26624/53248/40960 at bl4/8/16, matching observation exactly. (This was also
  July's "col_major fails only at scale 1000".) Fix: wrap the GENERATED address
  at the device boundary (Geometry.device_bytes; wrap_mask for
  col_major/col_interleave) so the address-hash stays cell-consistent —
  DRAM-visible behaviour unchanged. Sim regression both families tests green.
- matrix@1000 re-run: **65/70 — every family x config DATA-CLEAN.** The 5 flags
  are the multiid 1:1 hist anomaly only (data clean) → split to PUMICE-020.
- tREFI soak gate: **0/15 dirty** (default / tiny 0x40 / huge 0xFFFF) — the
  PUMICE-004 refresh fix re-validated on the current bitstream.
- Config-axis perf, all as designed: open_page/reorder 13–13.8x baseline on
  inc/row_major; bank_interleave 7.8x on col_major; bank-recovery visible on
  col_major_interleaved. July's 0/14 axes are fully recovered.

Final accounting for issue #42 + the July cluster: every failure across
PUMICE-001/002/003/004/007 was verification- or host-side. Zero RTL defects.
CSVs: build-perf/results/char_2026-08-25_{smoke,matrix}_s1000*.csv.


## PUMICE-007 — Retire the deskew RTL + PHY_TIMING.deskew_lo/hi CSR
**Status:** closed 2026-08-24 — already done by 38c8ae63 (Jul 22), the day before this page was stamped open

The deskew path was superseded (see PUMICE-008 in `dropped.md`): the board read
fix was the PUMICE-005 bring-up tuple at deskew 0/0. The RTL and its CSR fields
remain and cost area/timing. Delete rather than train — but only after the
board is re-validated on a rebuilt bitstream so the removal is not entangled
with an active bring-up.

**Resolution (2026-08-24):** the fourth stale entry from the Jul 23 vault
migration (with 002/003/004). `38c8ae63` had already retired the whole
experiment — aligner delay-lines, DESKEW_W threading, PHY_TIMING.deskew_lo/hi
(RDL regenerated), train_deskew/validate_reads, Makefile/ILA hooks — and the
same commit closed board bring-up with reads working on the rebuilt bitstream,
which was this task's stated precondition. Verified against the tree: zero
deskew references in rtl/, the regmap, or the board area; the only survivor is
the historical removal note in pumice_csr.rdl.


## PUMICE-004 — Refresh collides with an open row (arbiter registered-feedback hazard)
**Status:** closed 2026-08-24 — fix landed 38c8ae63 (Jul 22, silicon-soaked); detector armed + mutation-proven

**Bug (#2, command-sequencing).** The arbiter (`pumice_cmd_arbiter`) can grant a
`REFab` immediately after an `ACT` to the same bank WITHOUT a `PRE` in between —
refreshing a row that is still open — and the following `RD` then returns
garbage (zero) for that one read.

Root: the per-bank "safe signals" (`pumice_bank_timers` readiness) are COARSE
and REGISTERED (2-cycle event->ready latency, see the `r_guard` note in the
arbiter), so the combinational picker issues the `ACT`, and the refresh path's
precharge-before-REF check does not yet see the just-opened row -> REF fires
with the row open.

**Reproduced pre-silicon** in `engine_mirror[64]` (`test_pumice_top`),
gear-2/BL8, sustained b2b: burst 25 shows `ACT@31920000 -> REF@31940000 (no PRE)
-> RD@31980000` -> read returns `0x0` (golden `0x190000`); refresh cadence
~10.25 us lands on one read. On the BOARD (gear-4, ILA
`reports/ila_refresh_collide.csv`) the refresh is correctly sequenced
(`RD->PRE->REF->ACT->RD`) — so this is not the board blocker, but it IS a real
arbiter defect. Confirmed on silicon as the residual row-sized corruption in
PUMICE-005.

**Instrument (already wired):** `rtl/fub/pumice_cmd_history_checker.sv`
(generate-gated by `CMD_HISTORY_EN` inside `rtl/macro/pumice_mem_cmd_scheduler.sv`)
— a per-(rank,bank) command-history shift register (slot = cycles-since-issue)
that binds to the arbiter's `cmd_valid/op/rank/bank` and audits JEDEC same-bank
sequencing the coarse gate misses. Ships the refresh-collision assertion (no
`REFab` with any bank row open) plus optional tRCD/tRP/tRAS positional checks.
Coarse = *permission to issue* (forward, lossy); fine = *record of what issued*
(backward, exact) — you need the fine one to audit the coarse one.

**Plan:**
1. `bind` the checker in the arbiter FUB (`test_pumice_cmd_arbiter`) and/or the
   scheduler MACRO (`test_pumice_core_macro`) TBs; add `--assert` to the
   verilator compile args.
2. Reproduce as a directed pre-silicon test — small `tREFI` + sustained
   same-bank reads -> the checker fires RED. **The test MUST also do DATA
   checking** (golden read compare), not just the sequencing assertion.
3. Fix the arbiter refresh sequencing: the precharge-before-REF logic must
   account for a just-issued `ACT` (don't grant `REF`/`REFab` while any bank's
   most-recent row-affecting op is an `ACT`), or block the `ACT` when a refresh
   is being sequenced. Mirror the fix in `refresh_ctrl`/`pumice_cmd_arbiter`.
4. Re-verify: checker GREEN, `engine_mirror[64]` burst-25 read == golden, macro
   109 + gear2 + FUB stay green.
5. Rebuild the bitstream (also picks up the APB CDC fix) and re-soak at tiny
   tREFI as the regression gate.

Scope note: this checker catches command-SEQUENCING bugs only.

**Resolution (2026-08-24):** the same staleness as PUMICE-003 — the fix landed
the day BEFORE this page was stamped open during the vault migration.
`38c8ae63` (2026-07-22) added exactly what the plan's step 3 asks for:
`w_ref_safe` (REF only with all rows closed in the registered view AND nothing
row-affecting in flight or inside the 2-cycle guard AND tRFC met) plus a
mission-mode tRFC down-counter with `t_rfc` threaded top→core→scheduler→
arbiter. Silicon-validated then by the tiny-tREFI A/B soak: 4/4 dirty before,
0-dirty after, on the rebuilt bitstream.

**What was still missing — the plan's steps 1-2 — landed today:**
- `CMD_HISTORY_EN` plumbed through `pumice_core` / `pumice_top` / both tb tops
  (it stopped at the scheduler, so no top-level test could arm the checker).
- `test_pumice_core_refresh_collide` now compiles with `-GCMD_HISTORY_EN=1`.
  Before, its "expected RED" docstring was DOUBLY vacuous: the checker generate
  was off, and the loopback DFI slave serves golden data regardless, so the
  data compare could never see a collision either.
- Anti-vacuity teeth: the test asserts the DFI slave decoded >0 REF commands
  (72 in the directed run) — a scenario that never refreshes can't go green.
- Mutation-checked per the formal discipline: gutting `w_ref_safe` to 1'b1
  fires the checker with the exact bug signature ("REFab issued with rank0
  bank3 ROW OPEN (ACT 2 cyc ago, no PRE)"); restoring it audits 72 REFabs
  clean and the full core_dfi file passes 5/5.

Diagnosis footnote: "zero DBG lines" from the checker was a pytest artifact —
cocotb sim output rides Python logging, shown only on failure unless
`--log-cli-level=INFO` is passed. The checker had been watching all along.

**Residual (rides PUMICE-001's board trip):** re-soak tiny-tREFI on the
2026-08-16 bitstream as the standing regression gate — the July soak was on the
July rebuild. This is confirmation, not an open defect.


## PUMICE-003 — test_ddr2_char_char_families integrity fail (bank_interleave/incremental_bl8)
**Status:** closed 2026-08-24 — already fixed by fcafc435; the re-check just never ran

`bank_interleave/incremental_bl8` fails integrity in the char-families sim
("read engine did not complete", 42 beats mismatched).

**Bisected 2026-07-22:** fails identically at HEAD (95c9490a) — predates the
deskew removal, the refresh/tRFC arbiter change, and the no-rmw shadow writes.
Same masked-regression window as PUMICE-002 (the top/char sims were
compile-broken by the dv/tb filelist drift for a period).

Suspect the config-switch path (ADDR_MAP `bank_lsb=0` preset) interacting with
the read engine. Re-check whether the PUMICE-001 fixes move this before
debugging further.

**Resolution (2026-08-24):** the task's own advice ("re-check whether the
PUMICE-001 fixes move this before debugging further") was correct. The July
bisection pinned the failure at HEAD `95c9490a` (Jul 21) — one day BEFORE
`fcafc435` (Jul 22) fixed exactly this: the bank_interleave preset programmed
`bank_lsb=0`, striping one DRAM burst across banks (writes stripe, the read
command fetches one bank's columns → the deterministic 42-beat corruption).
The re-check never happened because the DV framework then broke (RDS-DV
#69/#70) and the char sims were red for unrelated reasons until 0.6.5.

Verified on cocotb-framework 0.6.5, clean build: the exact repro
(`test_ddr2_char_char_families`, smoke profile = baseline/bank_interleave/
reorder × incremental/col_major) passes in 504s. `set_addr_map_scheme` now
derives the legal boundary `bank_lsb = log2(burst_cols)` with `burst_cols`
computed from the TEST_DRAM_* geometry env the sim wrapper exports (sim
64b-device: burst_cols=4 → lsb=2; board x16: burst_cols=2 → lsb=1).

Same #42 family as PUMICE-001's board findings — this was the sim face of the
scheme-axis corruption. The board re-run of the config-axis families
(PUMICE-001) remains the silicon-side confirmation.


## PUMICE-002 — test_pumice_top_csr wr_rd roundtrip returns zero read beats
**Status:** closed 2026-08-24 — TEST defect, not RTL: stale hand-packed DFI_PHASE

`cocotb_test_pumice_top_csr` fails its AXI write-then-read phase: read 0 gets
ZERO R beats in 800 cycles (`got=[]`), i.e. the read path never returns — while
`test_pumice_top` (45 read-heavy tests), core, core_dfi, geared and the whole
fub/macro suite pass.

**Bisected 2026-07-21:** fails identically at HEAD (95c9490a) with only the
filelist fix applied — predates the deskew removal and the refresh/tRFC arbiter
change.

**Re-confirmed 2026-07-23:** fails identically with `pumice_top.sv` reverted to
HEAD and a clean rebuild, so it is not caused by the PUMICE-001 page_policy fix
either. Note the rebuild mattered — the first run reused a stale `sim_build`
and completed in 0.41 s, which would have made a reverted-RTL run meaningless.

Suspect the CSR-programmed config path (hwif-driven init) diverging from the
TB-driven config the other tops use. The top tests were compile-broken (missing
`gaxi_fifo_async` deps in the dv/tb filelists) for some window, so the
regression that introduced this was masked.

**Root cause (2026-08-24):** the test programs CSRs by HARDCODED offset +
hand-packed bit positions (predates [[registers-by-name]]). `DFI_PHASE` grew
`gear_ratio[8:7]` and `bl[12:9]` when gear/BL became runtime CSRs — during the
exact filelist-drift window this test could not compile — and the test's
`pk((0,0),(0,4))` kept writing the whole register as 0. gear=0/bl=0 programs a
zero-beat burst: init completes, AXI writes still get B responses, but the read
path has nothing to return → rvalid never fires → `got=[]`. Every register
OFFSET still matched the current regmap; only the field packing had rotted.

**Fix:** write `gear_ratio=log2(DFI_RATE)`, `bl=BL` in the DFI_PHASE pack
(one line). Red→green flip confirmed on clean builds. The suspicion in the
original filing ("CSR-programmed config path diverging from TB-driven") was
half right — the divergence was in the TEST's packing, not the RTL's hwif.
Textbook case for [[registers-by-name]]: the by-name TB absorbed the RDL
change, the hardcoded one silently rotted. Follow-up candidate: migrate this
test's CSR writes to the generated regmap so it cannot rot again (its distinct
value — raw-cpuif programming + hand-rolled AXI as a BFM-independent second
opinion — is worth keeping).


## PUMICE-005 — Board reads WORK: validated tuple + honest measurement
**Status:** closed 2026-07-21 — reads clean on silicon; residual corruption split out to PUMICE-004

The rate-2/BL4 board (BUILD_ID 0x44445232) reads CLEAN. The blocker was never
the analog read path; it was three stacked measurement/config defects:

1. **Sweep axis.** s7ddrphy asserts `rddata_valid` a FIXED `read_latency`
   (= cl_sys+6 = 8) sys cycles after `rddata_en` (pure delay line; ISERDES
   capture is continuous), so for reads `t_rddata_en` only places valid. The
   DATA arrives at its own physical latency — `DFI_TUNING.rddata_delay` slides
   the data onto the valid window. Every failed sweep held rddata_delay=0 where
   alignment is unreachable. **Validated tuple: t_phy_wrlat=1, t_rddata_en=6,
   rddata_delay=7, bitslip=0, IDELAY tap 8 (eye taps 0..16, width 17).** Baked
   into the A7Leveling ctor defaults.
2. **False-pass metric.** `wait_engine` default bails when rd_error latches (a
   mismatch latches it) -> `beats_mismatched` read EARLY; and a HUNG read counts
   nothing -> reads back 0 = fake clean. Fixed in bringup_joint_probe /
   `A7Leveling._test` / train_per_lane (ignore_error=True + require done; hang
   reported distinctly).
3. **RMW poison.** On pre-CDC-fix bitstreams the pumice APB window returns a
   PRIOR transaction's data, so every `rmw=True` write spliced stale garbage
   into preserved fields (set_deskew after set_controller_cfg silently reverted
   wrlat/rden -> leveling swept at reset timing). pumice_device now NEVER rmws:
   shadowed full-word writes seeded from RDL resets, `invalidate_shadow()` on
   soft_reset. (RTL CDC fix already landed in `apb4_slave_cdc`; bitstreams in
   `bitstream/` predate it — rebuild to retire the hazard on-silicon.)

Residual intermittent row-sized (256-beat/2KB) read corruption, strongly
refresh-correlated (soak A/B: tREFI default 0/8 dirty, tREFI=0x40 4/4 dirty at
~32-44/1024 beats, tREFI=0xFFFF 0/8) is a separate defect — split out to
PUMICE-004, now confirmed on silicon.

## PUMICE-009 — Generic AXI data-width gearing
**Status:** closed — resolved via external converter

Make host `AXI_DATA_WIDTH` a free parameter (32/64/128/256/512) decoupled from
the core width `DW = DRAM_BEAT_WIDTH x DFI_RATE`. Family-wide
(DDR2/3/4/LPDDR2), for future DDR* IP where each device/PHY pins its own
(beat, rate) but the host SoC wants a fixed convenient AXI width.

Implemented via the EXTERNAL formally-verified `axi4_dwidth_converter_wr/_rd`
in a wrapper `rtl/top/pumice_top_geared.sv` (host width <-> DW; GEAR-1 =
generate bypass, bit-identical). Core datapath untouched. Verified end-to-end
(`test_pumice_top_geared.py`): write bursts at host in {64, 128, 256}
round-trip back through host-width reads (down-gear / bypass / up-gear).

Chose external over the internal gearbox because the datapath was freshly
stabilized and the converters are already formal; also the rearchitecture
already solved the original a7ddrphy forcing function (AXI = beat x rate = 128,
a fine width — no gearing needed for the board).

Design + rationale + deferred internal-gearbox option:
`docs/AXI_DRAM_GEARING_SCOPE.md`

## PUMICE-010 — Single-register AXI-address -> {bank,row,col} mapping
**Status:** closed — resolved

`addr_mapper.sv` is now driven by ONE knob — `ADDR_MAP.bank_lsb` (the CSR
register that replaced the old scheme selector) — plus an optional bank
XOR-hash (`ADDR_MAP.hash_en`/`hash_seed`). The mapping is derived by stacking
fields around the bank position: `col_lo(bank_lsb) | bank | col_hi | row | rank`,
row LSB invariant at `CW+BW`. The classic schemes are just settings, no scheme
mux: `bank_lsb == COL_WIDTH` = ROW_MAJOR; `bank_lsb == log2(cols/burst)` = max
BANK_INTERLEAVE (burst locality preserved by col_lo); `hash_en` = XOR_HASH on
top.

Landed: RDL ADDR_MAP register (regenerated CSR + regmap via
`bin/peakrdl_generate.py`); addr_mapper rewritten (single stacked extraction +
hash, 3 generate blocks + mux gone); bank_lsb/hash_en/hash_seed threaded through
pumice_axi4_ifc / wr+rd intakes / pumice_core / pumice_top (driven from
`hwif_out.ADDR_MAP`); program_defaults + test_pumice_top_csr + core tests
updated. FUB conformance (`test_addr_mapper`) rewritten to sweep bank_lsb across
[0, COL_WIDTH] + hash on/off vs a Python reference — 5/5. Full suite: 407 pass,
0 fail (macro 141 + fub/top 266).

`addr_map_scheme_e` retained only for the retired OLD macro sentinels
(pumice_core_macro / axi_frontend_macro / pumice_config_block), which were
carried to the new intake interface — candidates for future retirement.

## PUMICE-011 — Full LPDDR2 mode-register init
**Status:** closed — resolved

Implemented the JEDEC JESD209-2F LPDDR2 init sequence in `init_sequencer.sv`
(memtype-gated): MRW Reset(MR63) -> ZQ Init(MR10=0xFF) -> MR1(BL8/nWR3=0x23) ->
MR2(RL3/WL1=0x01) -> MR3(DS 40ohm=0x02). The wide MR index (MA up to MR63)
reaches the CA formatter via the ROW request field packed as {MA[5:0], OP[7:0]}
(`dfi_cmd_formatter` unpacks row[13:8]=MA, row[7:0]=OP) — no 3-bit bank-port
limit. Only MR1/2/3 update the CL/CWL/BL shadow; MR63/MR10 are issued but not
shadowed. `mode_register.sv` LPDDR2 CL/CWL decode made JEDEC-faithful (MR2[3:0]
RL&WL enum).

Verified: DFISlavePHY now records decoded MRW ({index:data}); `smoke_lpddr2`
asserts init programmed {63:0x00, 10:0xFF, 1:0x23, 2:0x01, 3:0x02}. Formatter
conformance + init_sequencer FUB updated.

**NOTE (silicon):** the sim gates PHY-init-complete on config-ready (TB) so the
sequencer latches the correct memtype ("config before init"). Real LPDDR2
silicon needs memtype stable before init — a strap, or gating the sequencer's
start on `CTRL.init_start`. DDR2 (the board target) is unaffected: its reset
default IS DDR2.

## PUMICE-012 — LPDDR2 write-auto-precharge dropped writes
**Status:** closed — resolved (RDS-DV DFISlavePHY fix)

`workload_mix_lpddr2` had dropped writes under LPDDR2's HAPPY_HYBRID row-miss
policy, which issues WRA (write-auto-precharge). Root cause was NOT the CA
encoding or write cadence: the DFI slave `_handle_command` had branches for
WR/RD but none for WRA/RDA. DDR2's decoder never returns WRA/RDA (it returns
WR/RD and carries auto-precharge in addr bit 10), but the bit-exact LPDDR2 CA
decoder folds AP into the opcode -> returns WRA/RDA -> fell through -> no
pending write -> `wrdata_en` became "stray data beats" and the write was
silently dropped.

Fix: fold WRA->WR and RDA->RD in `_handle_command` (auto-precharge already
carried in addr bit 10 for both paths). All LPDDR2 traffic tests now pass;
xfail removed.

## PUMICE-019 — top-tier shared sim_build races under clean parallel runs
**Status:** closed 2026-08-26 — fixed via per-worker build dirs (was: open 2026-08-23, mechanism confirmed twice, serial run the workaround)

`dv/tests/top/test_pumice_top.py::_run` shares one compiled sim per parameter
set (`local_sim_build/shared_nr1` / `shared_nr2`) so the suite compiles ~twice
instead of once per test — but there is NO LOCK around the compile. After
`make clean-all`, `run-gate-parallel` (-n 48) sends dozens of concurrent
Verilator/ccache compiles into the same directory and they destroy each
other's artifacts (`Vtop__pch.h.fast: No such file`, invalid-PCH, missing .o).
Measured 2026-08-23: two consecutive clean parallel runs reported 48 and 31
spurious FAILs (126-144 reruns) on a suite that passes 53/55 serially — the
reruns converge only once one compile survives, so the tally is garbage and
the flake burns ~5 min anyway.

`smoke`/warm-tree parallel runs are fine (nothing to compile). fub/macro use
per-test build dirs and don't race.

**Fix options:** a file lock around the cocotb_test `run()` compile (fcntl on
`<sim_build>/.compile_lock`), or a cheap pre-compile step in the Makefile's
parallel targets (run one test per shared build serially first, then fan out).
Whichever lands, the parallel targets must give an honest tally after
`clean-all` — that is the canonical regression recipe.

Found while validating the RDS-DV#69 fix; the 2 real reds behind the noise are
PUMICE-002 and the LPDDR2 decode regression RDS-DV#70.

**Second finding (2026-08-24): failing seeds are unrecoverable.** One serial
clean tier run showed geared[64/128/256] failing together; the per-test SEED is
`random.randint(0,100000)` at wrapper level, printed nowhere in the summary, and
the logs/ + results xml were wiped by the next `make clean-all` — so the repro
was lost. File-scope reruns and a 10-seed `PUMICE_SEED` sweep (30 runs) all
pass. Whatever fix lands for the lock should ALSO make the wrapper echo each
test's SEED into the pytest summary line (or persist logs/ across clean-all
until explicitly cleared) so a one-off failure is reproducible after the fact.

**CLOSED 2026-08-26.** Root cause: cocotb_test's Verilator path re-runs
`verilator -cc` + make UNCONDITIONALLY on every run() (no staleness check),
so ANY cross-process sharing of a sim_build is unsafe — a compile-only
flock cannot help because the unlocked sim-run pass regenerates the tree
too. Fix: per-XDIST-WORKER build dirs (`shared_nrN_gwK`) — workers run
their tests sequentially, so the compile-sharing win survives inside a
worker with zero cross-process sharing; ccache absorbs duplicate C++.
Validated: clean `run-gate-parallel` = 61/61 passed in 88s (was 42
spurious FAILs / 126 reruns). Seed echo also landed: every wrapper prints
`[seed] <tag> ...SEED=<n>` so pytest surfaces it for failing tests and a
one-off red is reproducible after logs are cleaned.

## PUMICE-024 — ORDER_MODE overlays miss 75 MHz: CLOSED by shortening the pre-pick stage
**Status:** closed 2026-09-09 — the ENHANCED tier now closes post-route

The overlays missed 75 MHz by 21-53 ps depending on the placer. Root cause was
not the overlays themselves but where the arbiter did its slot-to-data muxing:
the output stage indexed the CAMs' flat {bank,row,col} vectors with the
REGISTERED pre-pick slot, so six NUM_ENTRIES:1 muxes sat AFTER the pre-pick
flop and fed r_bank/r_row/r_col. That was the reported critical path in every
build (`r_*_pop -> ... -> r_bank`).

Fix: mux at the pre-pick flop instead, registering the already-narrow
{bank,row,col} per class. The wide muxes move into the STAGE-1b cycle where
arg_sel has already resolved and there is slack, and the output stage keeps
only the small class-priority mux. `rd_col_ap` already used exactly this
pattern, so it is the established idiom rather than a new one. Sampling one
cycle earlier is also more coherent: a CAM entry's key is fixed at insert and
the forward guards prevent re-selecting a just-selected slot, so the operands
now come from the same epoch as the decision.

Post-route at 75 MHz, same flow, before -> after:

| Build | Before | After |
|---|---|---|
| base | +0.010 ns, 0 failing | +0.009 ns, 0 failing |
| ENHANCED | -0.021 ns, 4 failing | **+0.005 ns, 0 failing of 72896** |

The base tier was already closing so it does not move (both figures are inside
the placement band); the enhanced tier closes for the first time. Cost is about
144 flops and 0.19% LUT. The same change also shortens the prepick-guard cone,
which feeds the mask build.

Validation: pumice fub 96 / macro 3 / top 119, zero failures; char sim 31
passed + 2 xfailed, zero unexpected.

## PUMICE-017 — CAM->arbiter pick cone does not close timing: CLOSED (stale)
**Status:** closed 2026-09-09 — the measured condition no longer exists

Filed 2026-08-31 against a post-route WNS of **-48.861 ns** with 8939 failing
endpoints, on the grounds that logic delay alone (17.825 ns) exceeded the 15 ns
period so no placement effort could recover it: "it is depth, and it needs
registers."

It got them. The three-stage pick split (STAGE-1a snapshot -> STAGE-1b arg_sel
-> pre-pick -> output), the CAM per-entry vector refactor, and finally the
pre-pick operand muxing of PUMICE-024 did exactly what the task asked for. The
current measurement on the same board and harness, at the HIGHER 75 MHz
target:

    WNS                 +0.009 ns   against 13.333 ns (75 MHz)
    Failing endpoints      0 / 72896
    ENHANCED tier       +0.005 ns, 0 failing

The task's secondary claim -- "PUMICE-006 was never synthesized" -- is also
stale: all three mode axes are in the board build, and the paging predictors
were restored to it on 2026-09-09.

Closed against evidence rather than assumption; the remaining pick-cone work
is performance (the auto-precharge head advance under strict ordering), not
closure, and it is recorded on PUMICE-021 in this file.

## PUMICE-022 — board validation: WRITE TARGET MET (570 MB/s), READ CEILING FOUND
**Status:** closed 2026-09-10 — measured on silicon; read shortfall re-filed as PUMICE-025

Nexys A7 (210292BFA3EE), 75 MHz / DDR2-300, base-tier bitstream at
3c66f442d. Peak is 600 MB/s (75 MHz x 8 B).

**Integrity first:** a7 read leveling found a clean eye (bitslip 0, tap 4,
width 10); 32 MB memtest 8/8 chunks clean, 0 dirty; every characterization
point passed its integrity check (12/12, then 13/13, then 32/32). So the
whole 2026-09-08/09 body of work -- read return ring, write-lead block, JEDEC
timings, restored paging modes, base-build order modes, pre-pick muxing --
is data-clean on hardware.

**Bandwidth, best config (`open_page` and equivalents, row_major BL8):**

| Direction | Measured | Target | Peak | Result |
|---|---|---|---|---|
| Write | **570.0 MB/s** | 510 | 600 | **MET** (95.0% of peak) |
| Read | **291.7 MB/s** | 450 | 600 | missed (48.6% of peak) |

> **CORRECTED 2026-09-10.** The first pass reported `refresh_credit` at
> 574.0/292.2 as the best config. That was an ARTIFACT of run order, not a
> result. `pumice_char.ControllerConfig.apply()` only programmed a mode axis
> when the preset set it, so a preset that left `page_mode` unset inherited
> the previous config's. `refresh_credit` is a CLOSE-page preset and ran
> straight after `rbl_dyn`, inheriting `page_mode=7`, whose predictor kept the
> page open. Standalone it measures 33.8/35.8, which is the correct
> close-page number. apply() now programs every axis on every config
> (0 = build default) so nothing is inherited; the re-run is 36/36
> integrity-clean and order-independent.

For scale: this path measured 12.7 MB/s flat on 2026-07-08 and ~2% of peak.
Writes are now essentially at the data-path limit.

**The read ceiling is structural, not a tuning problem.** Read bandwidth is
291.7-292.2 MB/s and read latency 49.2 cycles in EVERY configuration that
streams at all, and it does not move with:
- burst length -- bl4 290.8, bl8 291.7, bl16 291.7 (identical). This rules out
  an outstanding-transaction or Little's-law limit: more bytes per transaction
  would raise it.
- access pattern -- incremental, row_major identical.
- paging mode -- open_page, adapt_time, adapt_access, rbl_dyn all 291.7.
- scheduling -- age_threshold identical to FR-FCFS.

48.7% of peak, invariant to everything above the return path, is the signature
of a return path that moves one AXI beat every other cycle while the write path
moves one per cycle. Re-filed as PUMICE-025 with this evidence.

**Mode characterization (row_major BL8, MB/s write/read):**

Re-measured order-independently, 36/36 integrity:

| Config | Write | Read | Note |
|---|---|---|---|
| `open_page` | 570.0 | 291.7 | the ceiling; four configs tie here |
| `age_thr` | 570.0 | 291.7 | starvation bound is FREE |
| `adapt_time` | 570.0 | 291.7 | |
| `adapt_access` | 570.0 | 291.7 | predictor holds the page open |
| `rbl_dyn` | 570.0 | 291.7 | **hill-climb works on silicon** |
| `rbl_static` | 33.8 | 36.9 | miss_thresh=2 too aggressive for streaming |
| `inorder` | 33.8 | 35.8 | 16x cost, as sim predicted |
| `refresh_credit` | 33.8 | 35.8 | CLOSE-page; credits do not rescue close-page |
| `baseline` | 33.8 | 35.8 | CLOSE-page reference |

The split is binary: anything that keeps the page open reaches 570/291.7,
anything that closes per access sits at ~34/36. Nothing lands in between,
which is what a command-bus-bound design looks like -- see the BL4 note in
PUMICE-025.

Two results worth keeping:
- **rbl_dyn vindicates the dynamic threshold.** `rbl_static` at the same base
  miss threshold collapses to 33.8 MB/s because it closes pages on a streaming
  pattern; `rbl_dyn`'s per-epoch hill-climb backs the threshold off and
  recovers full bandwidth. That is precisely the "lesser-known alternative
  that wins in a specific situation" the mode work exists to demonstrate, and
  it only shows on real traffic.
- **age_threshold is free.** Same bandwidth as plain FR-FCFS, so the
  starvation bound costs nothing until it engages. It is the mode to reach for
  when in_order is being considered for latency reasons -- in_order costs 17x
  on this pattern.

## PUMICE-021 — paging_sched_cross in_order floor: MISCALIBRATED FLOOR, not an RTL stall
**Status:** closed 2026-09-09 — diagnosed by measurement, floor re-cut by mechanism

The floor failure (`static_close x order_in_order` 37.87%, later joined by
`rbl_static` 37.87% and `rbl_dyn` 44.14%, against IN_ORDER_FLOOR=0.45 whose
comment expected ~56.3%) is the honest cost of the mode. It is NOT a stall
defect and there is nothing to fix in the RTL.

**Discriminator.** Across the eight paging modes under in_order, the split is
exact: every mode that actually drives AUTO-PRECHARGE sits at 37.87-44.14%
(static_close, rbl_static, rbl_dyn) and every mode that does not sits at
exactly 80.33% with stall=94 (build_default, static_open, fixed_open,
adapt_time, and adapt_access -- the last is AP-capable but never closes at the
default counter shape this sweep programs).

**Mechanism, measured** with a command-cadence probe on this exact window
(2026-09-09):

    static_open  x in_order  util 89.51%  ops {ACT:8, WR:64}   gaps 4x63, 8x8
    static_close x in_order  util 36.89%  ops {ACT:26, WRA:26} gaps 4x25, 8x34

Non-AP paging activates a row once and then streams columns at tCCD: ONE
command per access, every gap 4 cycles. AP paging makes every access a pair of
DEPENDENT commands, ACT then column-with-auto-precharge: ACT->col is tRCD
(gap 4) and col->next ACT is the head advancing through the arbiter's 3-stage
pick pipeline (gap 8). A 12-cycle period instead of 4, so about a third of the
utilization. Under FR-FCFS other banks' entries fill those gaps, which is why
the same windows read 100% there; strict ordering cannot fill them by
definition. The 0.45 floor and its 56.3% note predate the pipelined arbiter,
which is why every AP mode landed just under it.

**Resolution.** The test now carries floors split by mechanism -- 0.75 for the
non-AP paging modes, 0.30 for the AP ones -- with the probe numbers recorded
in the comment, plus an assertion that the AP modes are actually present so
the split cannot silently cover nothing. A regression in either class still
fails. Shortening the col->ACT head advance would lift the AP numbers and is
tracked as a performance item under PUMICE-024, not a correctness one.

## PUMICE-020 — multiid read-return accounting: hist total != txn_count (data clean)
**Status:** closed 2026-08-26 — root cause found (AMBA-HISTCH1); 1:1 check moves to the observer path (PUMICE-016) (was: open 2026-08-25, deterministic, observability-only)

`col_major_bl8_multiid` (id_mode=LFSR) at medium@1000 reports a 1:1 violation:
latency-hist total 168409 vs txn_count 64000 (EXTRA returns) — while the DATA
integrity is clean (0 beats mismatched after the device-wrap fix). The value is
byte-identical across all five controller configs, so it is deterministic and
config-independent → an accounting behaviour of the LFSR-ID x chopped-burst
path, not nondeterministic duplication. Sequencing in `measure()` is clean
(clear_stats after programming, freeze before readback), so it is not
cross-scenario accumulation.

First suspect: `axi_perf_latency_hist` transaction-boundary tracking under
many concurrent IDs — one AXI bl8 burst is 8 chopped BL4 DRAM commands, and
per-ID RLAST collapse may be miscounted when IDs interleave. July's basic-scale
run showed the small-N version (64007 vs 64000). Severity: harness
observability only — the 1:1 check is doing its job of flagging it; data-path
1:1 is separately proven by the CRC/mismatch counters.

Repro: `pumice_master.py --char --char-configs baseline --char-level medium
--char-scale 1000` and watch col_major_bl8_multiid; or in sim,
TEST_CHAR_PROFILE with a multiid scenario over the loopback.

**CLOSED 2026-08-26 (direction change).** Root cause FOUND, two layers,
both in the bespoke harness perf path (see AMBA-HISTCH1 in the amba
ledger): (1) hist timestamp FIFO at MAX_OUTSTANDING=8 vs a ~10+ deep
engine admission domain silently dropped samples (sim: up to 6/64 missing
even single-id; fixed by 32 in ddr2_char_macro, after which bl4/8/16/gap
are EXACT 64/64); (2) axi_perf_latency_hist at NUM_CHANNELS=1 decodes ID
BIT 0 as a channel index into a one-entry array — Verilator drops the
odd-id accesses (sim: deterministic 33/64 = the even-id subset), synthesis
aliases them (the board's EXTRA side, 168409 vs 64000). Sean's direction
(2026-08-26): do NOT keep monitor/perf logic inside pumice — the external
observer block (axi4_intf_master_observer) does this job; the shared-
primitive fix is recorded as AMBA-HISTCH1 for when that module is next
touched. PUMICE-016 (adopt the observer) is the vehicle; the 1:1 check
moves there. The cheap "interesting" counters STAY in pumice per the same
direction: PAGE/SCHED/REF *_STATS, OBS_ROW_HIT, refresh-defer histograms.
The sim repro profile (`multiid_min`) stays in pumice_char.py; its multiid
arm remains red until the observer adoption replaces the bespoke hist.

---

## PUMICE-KMAP — real K-maps for the scheduler, CAMs and DFI layer
**Status:** CLOSED 2026-09-10  **Was blocked on:** [[TOOLING-KMAP]] items 1-4

All six criteria of [[signal-contracts-and-kmaps]] are discharged across the 17
computed maps, the artifacts are consolidated, and both halves are gated so they
cannot silently rot again.

**One workbook, one generator.** Four workbooks from three generators across two
directories became `docs/pumice_signal_contracts.xlsx` from
`docs/gen_pumice_signal_contracts.py`, verified to reproduce all 18 original
sheets cell-for-cell. The old flow LOADED the workbook and appended rows, so
re-running duplicated them (the committed Scheduler sheet had 8 such rows); the
new one builds from scratch and is idempotent. An INDEX sheet separates SPEC
tables from COMPUTED grids and opens with the measured RTL status, so the book
cannot be read as a bug list for a controller that meets its targets.

**Criterion 1 (computed, not drawn) was FALSE for four maps**, now gated.
`rd_col_m`/`wr_col_m` modelled 7 terms against 13; `w_ref_safe`, `w_guarded`,
`w_drain_active` each dropped one. `docs/check_kmap_rtl_sync.py` requires every
RTL identifier on a signal's RHS to be NAMED in the documented expression (folds
stay legal, the fold equation is in [brackets]). **16 of 17 machine-checked, 0
drifted**; the generator REFUSES to write on drift.

**Criteria 3/4/5/6.** Axis-term tables with file:line on the four maps whose axes
are folds; relations on all 17 (constraint or explicit independence note); 38
don't-care cells from cited invariants; Quine-McCluskey implicants printed beside
the documented equation on every map.

**Waves: audited, corrected, extended, RENDERED, in the MAS.** The set was drawn
at tCCD=2 with streams captioned "~100% util" -- impossible, and the RTL settles
it (BURST_WORDS=1, so a column every cycle, which is the measured 571.3 MB/s).
Added seven performance diagrams: 13-17 bad-but-correct (admit gate, ring bound,
page thrash, turnaround thrash, refresh storm) and 18-19 pathological, each
captioned with the board number it produced. `design/check_waves.py` found **11
real defects** in the pre-existing diagrams, five of them labels attached to a
logic level instead of a bus slot (WaveDrom silently shifts every label in the
row onto the wrong segment). `design/render_waves.py` produces SVG+PNG for all
19 and **MAS Chapter 7** embeds every one. Rendering itself exposed that every
caption (101-431 chars) overflowed the image and 23 group labels overlapped --
neither visible in the JSON, neither ever seen because nothing had been rendered.

**The lesson.** A spec written during a debugging campaign dates instantly and
silently: these artifacts asserted a 15%-of-peak controller and five live
defects while the board ran at 95% in both directions. Mechanical checks, not
review, are what keep hand-built collateral honest -- every check added here
failed on its first run.

---

## PUMICE-026 — finish the LiteDRAM same-harness A/B (it is already ~80% built)
**Status:** CLOSED 2026-09-10  **Priority:** was P2
**Intent (Sean):** "drop liteddr into the pumice harness so testing is the same."

**START HERE, DO NOT REBUILD:**
`projects/fpga-systems/NexysA7/pumice/ddr2-characterization/flows-litedram-uart/`

That flow already exists and is documented as **WIRED** in its `HARNESS_PLAN.md`:

- `rtl/char_engine_harness.sv` — DUT-agnostic harness (engines + perf meters +
  bandwidth timer + harness_csr + UART bridge) exposing an AXI4 master.
  Verilator-lint-clean standalone.
- `rtl/litedram_char_top.sv` — board top: `litedram_core` + the harness on
  `user_clk`, `init_done`-gated, AXI user port wired.
- `rtl/filelists/litedram_char_harness.f`, `constraints/litedram_char.xdc`,
  `tcl/build_all.tcl`, `tcl/program_fpga.tcl`, `Makefile`, `regen.sh`,
  `litedram_hp.yml`, and a generated `build_board/gateware/litedram_core.v`.
- A `litedram_hp.yml` deliberately mapped onto a high-perf pumice preset, with
  the mapping table written out in its README.

**Progress 2026-09-10 (commit fdaa7db37):**
- ~~regen with BIOS~~ **DONE.** Core regenerated with a functional BIOS (63 KB
  ROM) and `litedram_hp.yml` moved to **75 MHz / 1:2 / 300 MT/s**, matching the
  point pumice is measured at. The stock 100 MHz / 1:4 would have voided the
  comparison.
- ~~XDC reconcile~~ **NOT NEEDED.** The regenerated core xdc has no ddram pins;
  the harness keeps its pin map.
- Five flow bugs fixed to get synthesis running: `REPO_ROOT` two levels short
  (the `../` count was correct at the pre-move path), `CONVERTERS_ROOT` not
  exported, the tcl filelist reader expanding only `$REPO_ROOT`, `.vlt` lint
  waivers handed to Vivado, and `VexRiscv.v` pinned to a path inside the LiteX
  venv. `regen.sh` no longer hardcodes a `/tmp` venv either.

**DONE 2026-09-10 — measured.** Timing-clean LiteDRAM bitstream (WNS +0.195, after
adding the core's CRG reset-strobe false path), `--char-profile matrix --char-scale 1000`,
14/14 integrity, saved as `docs/char_results/litedram_2026-09-10_matrix.csv` with the
write-up `FINDINGS_litedram_ab_2026-09-10.md`. Headline: LiteDRAM reads 564-579 MB/s
(94-97% of peak) through the identical harness where pumice reads 291.7; writes equal
(~554-569 vs 551-570). The read ceiling is pumice's, not the operating point's -- see
PUMICE-025. Ready to close (move the block to closed.md).

**Progress 2026-09-10 (later) — item 0 DONE, harness matches build-perf:**
Sean asked for the LiteDRAM harness to match the current one; the chosen
route was to extract a shared engine block. `char_engine_block.sv` (chargen
regs + generator array + crossbars + perf, one AXI4 master) is pulled out of
`ddr2_char_macro.sv`, which now wraps pumice around it; `char_engine_harness.sv`
is build-perf's `ddr2_char_harness` minus the controller (same UART bridge,
same `bridge_ddr2_char_axil` address map with `ddr2_apb` terminated, same
`harness_csr` with BUILD_ID "LDR2", same timer/LEDs). `make lint` clean;
Makefile on `make/fpga_flow.mk`; `host/host_litedram_char.py` is the pumice
host with the pumice-CSR surface as no-ops. `FPGA_CLK_HZ` in the top was still
100 MHz after the 75 MHz regen (UART divisor wrong) -- fixed. Bitstream build
in flight; then program, `--char-profile matrix --char-scale 1000`, save CSV.

**Was BLOCKING (now resolved as above).** Synthesis reached the harness and
stopped on **41 port mismatches**: `char_engine_harness.sv` is wired
to a `harness_csr` that no longer exists. The whole per-generator config
surface (`o_cfg_wr_*`, `o_cfg_rd_*`, the start pulses, the CRC readback) moved
out of `harness_csr` into `chargen_regs` when the char framework went to a
16-generator array; `harness_csr` is now 75 ports of global/PHY config only.

Rewire `char_engine_harness.sv` against the current framework — `harness_csr`
for the global surface, `chargen_regs` (`chargen_regs.rdl`) for per-generator
config, and the generator array instead of one wr + one rd engine. The pumice
flow's `ddr2_char_macro.sv` is the reference for how the array is driven today.

Then: host variant (copy `ddr2_char.py` + `pumice_master.py`, drop the
pumice-CSR `set_controller_cfg` writes since LiteDRAM self-configures, keep
engine cfg + perf/timer readout; `harness_csr` is at base 0 here), then
`make bitstream && make program && make characterize`.

**RESOLVED 2026-09-10:** `build-litedram/` was an empty duplicate scaffold
(the never-executed destination of a NEXYS-003 move). It cost this session a
rebuild-from-scratch of the LiteX tooling before the real flow surfaced. It is
now DELETED and every reference points at `flows-litedram-uart/`.

**Tooling notes that ARE new and worth keeping** are in
`flows-litedram-uart/2026-09-10_tooling_notes.md`, with two working scripts
beside it (`bin_nexys_bist_soc.py`, `bin_litedram_bist_run.py`): install LiteX
from git not PyPI (PyPI +
Python 3.12 breaks every target on a migen bytecode-inference bug); the RISC-V
toolchain is already at
`/tools/Xilinx/2025.1/gnu/riscv/lin/riscv64-unknown-elf/bin`; PyPI
`pythondata-software-picolibc` ships incomplete sources so the BIOS build
fails; and `--cpu-type=None` yields a clean timing-met bitstream whose BIST
returns garbage because LiteDRAM's DDR2 init and levelling live in the BIOS.
That last point is why item 1 above says `--bios`.

**Why it matters:** LiteDRAM's read is also ~47% of the raw ceiling while its
write reaches 88%; pumice is at 48.6% / 95.0%. Two independent controllers at
the same read fraction on the same board is the strongest evidence that the
read ceiling is a property of this operating point rather than a pumice defect
(PUMICE-025). Same-harness confirmation would redirect or justify that work.

---

## PUMICE-025 — read bandwidth was pinned at 48.7% of peak (FIXED: now 95%, write parity)
**Status:** CLOSED 2026-09-10  **Priority:** was P1. Target was 450 MB/s read; delivered 571.3.
Residual latency work carried forward as [[PUMICE-030]].
**Found by:** PUMICE-022 board characterization (see closed.md for the full table)

Read bandwidth on silicon is **291.7-292.2 MB/s against a 600 MB/s peak** and
does not move with burst length, access pattern, paging mode or scheduling
mode. Write on the same runs reaches 574.0 MB/s (95.7% of peak).

**What the invariance rules out.** bl4 / bl8 / bl16 measure 290.8 / 291.7 /
291.7 -- identical. If the limit were the number of transactions in flight
(generator `GEN_MAX_OUTSTANDING`, ring `RD_RET_DEPTH`, or a Little's-law
round-trip bound) then doubling the bytes per transaction would raise
bandwidth. It does not, so the limit is a per-cycle rate below the transaction
layer, not a concurrency limit. Read latency is a flat 49.2 cycles throughout.

**2026-09-10 ROOT-CAUSED AND LARGELY FIXED: the read intake admitted one
sub-command every TWO cycles.** `pumice_rd_intake` held a single `r_armed` bit
on the AR skid head to mark "the registered snarf probe belongs to this AR".
The bit was cleared by its own admit and could only be re-set the cycle after,
so admits were capped at 0.5/cycle. One admitted sub-command is exactly one
DRAM burst, and on this board (BL4 on x16, 32-bit beat) one burst is ONE AXI
beat -- so the gate was the bandwidth: 0.5 x 8 B x 75 MHz = 300 MB/s, against
291.7 measured (97% of it). Writes have no such stage (`pumice_wr_intake`
runs AW straight from the meta-FIFO head) which is the entire read/write
asymmetry.

Fixed by staging the AR: the skid head is the AR being probed, a new stage
holds the AR being admitted, and the two advance together (1 admit/cycle).
While the stage is held the probe re-points at the stage, so the hit driving
an admit is never more than one cycle old -- the same RAW-forwarding exposure
the arm bit had, rather than a latched hit that would go stale.

Board result (`board_2026-09-10_read_intake_fix.csv`, 14/14 integrity):

| scenario | read before | read after |
|---|---|---|
| row_major_bl8 | 291.8 | **470.9** |
| row_major_bl16 | 291.8 | **471.0** |
| incremental_bl8 | 291.7 | **463.7** |
| row_major_bl4 | 290.8 | **360.4** |

48.6% of peak -> 78.5%. Writes unchanged (551/570). Timing IMPROVED: WNS
+0.285 ns vs +0.039 before, 0 failing of 94060; area +102 LUT / +35 FF.

**SECOND LIMIT, ALSO FIXED: the read return ring was 32 tickets and the board
build never even set it.** `ddr2_char_macro` did not pass `RD_RET_DEPTH`, so
every board bitstream ran the controller default of 32 regardless. Sustained
read rate is bounded by depth / (ticket alloc -> R drain), and this board's PHY
read latency is ~49 MC cycles, so 32 tickets cap reads near 0.78 of the DRAM
rate -- exactly the 78.5% left after the intake fix. Threaded the parameter
from `ddr2_char_top` through the harness and macro, exposed
`PUMICE_RD_RET_DEPTH` as a build define, and set the board default to **64**.

Board sweep (`board_2026-09-10_read_fixed_ring64.csv`, 14/14 integrity):

| scenario | read @ ring 32 | read @ ring 64 | write |
|---|---|---|---|
| row_major_bl8 | 470.9 | **571.3** | 570.2 |
| row_major_bl16 | 471.0 | **571.3** | 570.3 |
| incremental_bl8 | 463.7 | **556.9** | 551.3 |
| row_major_bl4 | 360.4 | 360.4 | 570.3 |

**Reads now match writes** (571.3 vs 570.2, both ~95% of the 600 MB/s peak) and
are within 1.4% of LiteDRAM's 579.5 through the same harness. Timing +0.283 ns,
0 failing of 94415; ring 64 costs ~158 LUT over ring 32.

**2026-09-10 CONCURRENT LOAD -- the workload where pumice's area pays off.**
Every measurement before this ran a write phase then a read phase, so
read/write turnaround was never paid. Running both directions in one window
(new `concurrent` / `multigen` profiles, disjoint regions, both controllers
through the identical harness):

| scenario | pumice total | LiteDRAM total | ratio |
|---|---|---|---|
| row_major bl8, 1w+1r | **570.1** | 285.6 | **2.00x** |
| incremental bl8, 1w+1r | **552.6** | 247.5 | **2.23x** |
| row_major bl8, 1w+2r | **570.2** | 316.4 | **1.80x** |

pumice holds 95% of peak with one, two and three concurrent generators;
LiteDRAM sits near half peak and its read latency rises from 24.7 to 94.5
cycles on incremental. The global FR-FCFS window batches same-direction
columns and amortises tWTR/tRTW; per-bank round-robin pays it per switch.
Files: `board_2026-09-10_{pumice,lite}_{concurrent,multigen}.csv`.

Not measurable this way: `col_major` / `col_major_interleaved` span the whole
device so generators cannot be placed adjacently, and those rows fail
integrity on BOTH controllers (the wrapped-walk hash artifact `strides_for`
documents). `incremental` under multigen likewise falls back to a far-apart
split that measures page thrash. Only bounded-wrap families place adjacently,
so row_major is the trustworthy multi-generator row.

**What is left.** AxLEN=4 still reads 360.4 while writing 570.3, and it did not
move with ring depth, so it is a third and separate mechanism (per-AR overhead
rather than per-column). Read latency is also still ~49 cycles against
LiteDRAM's 24.7 -- bandwidth is fixed, latency is not. Neither blocks the
bandwidth target; track them here rather than reopening the ceiling story.

**(Earlier) SAME-HARNESS A/B DISPROVED THE OPERATING-POINT THEORY BELOW.** LiteDRAM
behind the identical `char_engine_block` / bridge / host, at the identical 75 MHz / 1:2 /
MR0=0x0432 (BL4, CL3) point, reads 564.1 (incremental) / 579.5 (row_major) MB/s and
writes 554/569 -- `docs/char_results/litedram_2026-09-10_matrix.csv`,
`FINDINGS_litedram_ab_2026-09-10.md`. So a column every MC cycle IS sustainable on
this bus for reads: the 48.6% ceiling is pumice's read command path, not BL4. Writes
already match LiteDRAM, which localises it to AR-accept -> column-issue -> R-return
(return ring / rd CAM / AR-order commit). LiteDRAM's read latency is 24.7 cycles vs
pumice's 49.2: ~25 cycles of extra pipeline per access is the other half of the same
story. The analysis below stands as the description of the write path; its
conclusion about reads does not.

**(Superseded framing) Burst length is the fundamental constraint, and it is NOT read-specific.**
The board runs BL4 (host forces `MR0=0x0432` and `bl=4`; the RDL default is
BL8/0x0433). On a x16 device BL4 is 4 transfers = 8 bytes, and 4 transfers at
300 MT/s is 2 CK = exactly ONE MC cycle at 75 MHz. So sustaining 600 MB/s
demands a column command EVERY MC cycle, on a single-issue command bus: 100%
of command slots must be columns, leaving ZERO for ACT, PRE or REF. Every
activate or precharge costs a full column slot -- 8 bytes -- one for one. That
is why the measured split is binary (570 page-open vs 34 page-closed) with
nothing in between, and it caps how much any scheduler can ever recover.

BL8 would halve the command pressure: 16 bytes per column, each burst
occupying 2 MC cycles, so a column every OTHER cycle saturates and the other
half is free for ACT/PRE/REF. That is the single biggest architectural lever
available and it is worth a build.

**Runtime BL8 does NOT work and needs a rebuild.** Tried 2026-09-10 with
`TEST_MR0=0x0433 TEST_DRAM_BL=8` on the BL4 bitstream: a 16 MB memtest passed
4/4 clean, but the characterization workload was **0/8 integrity** and
bandwidth did not move. The simple memtest is not a sufficient check for this
change. `DRAM_BL` is a compile-time parameter in `ddr2_char_top.sv`
(BURST_LEN_MULTIPLE, harness sizing, column stride) as well as a runtime CSR,
so BL8 requires rebuilding the bitstream with `DRAM_BL = 8`, not just an MR
write. Board was restored to BL4 and re-verified clean afterwards.

But note that BL4 does NOT explain the read/write asymmetry: both directions
need the same one-column-per-cycle rate, and writes achieve 95% of it while
reads achieve 49%. The asymmetry below is still an implementation property.

**Hypothesis:** the read return path delivers one AXI beat every other cycle
where the write path delivers one per cycle. 292/600 = 48.7% is close enough to
exactly half to be worth confirming. With the generator ruled out (below), the
limit is inside the controller's return path. Candidates:
1. ~~The char harness's read CRC-check engine consuming R at half rate.~~
   **RULED OUT 2026-09-10 by measurement.** `axi4_master_rd_crc_check` at fub
   level, across all seven slave timing profiles, holds `rready` asserted on
   **100% of run cycles** (140/140, 269/269, 388/388, 325/325, 201/201,
   1925/1925 ...) with a back-pressure count of **exactly zero** in every
   profile, and transfers 128/128 beats each time. With a backtoback slave
   every beat-to-beat gap is 1 cycle. The generator never throttles R, so the
   ceiling is NOT in the harness. Guarded permanently by the
   `rready_never_throttles` scenario in
   `val/amba/test_axi4_master_rd_crc_check.py`.
2. `pumice_rd_return_ring` drain -- one beat per cycle through the BRAM skid
   vs. the write path's rate.
3. `pumice_dfi_rd_aligner` / `pumice_dfi_cdc` read FIFO width or pop rate.
4. `pumice_rd_intake` R-channel assembly.

The latency view (`rtl/schematics/gen_latency.py`) prints per-path flop counts
and names the combinational feedthroughs for each of these blocks, which is the
fastest way to compare the read and write drain structures side by side.

Do NOT start by tuning the scheduler: every scheduling and paging mode gives
the identical 291.7, so the scheduler is not the constraint.

---

## PUMICE-027 — write responses leave pumice out of AW order; the char write bridge routes B by position
**Status:** CLOSED 2026-09-11  **Priority:** was P2
**Found by:** `test_ddr2_char_macro[bank_parallel]` (the only multi-writer scenario), once the
**RESOLVED 2026-09-11 by the bridge generator, not by pumice.** BRIDGE-016 made
fabric IDs master-unique -- each master-side adapter now emits
`{BRIDGE_ID, id}`, so gen0 issues `0_xxxxxxxx` and gen1 `1_xxxxxxxx` and no two
masters can have the same ID in flight. On the strength of that the slave-side
adapter was regenerated to allocate into a `bridge_cam` keyed by AWID and
**deallocate on the returning BID** (`ALLOW_DUPLICATES=1`, "Mode 2: OOO
support") instead of reading an AW-order FIFO head. Owner lookup is now
unambiguous whatever order pumice returns responses in, and the BRIDGE-010
position-order assertion is gone with the mechanism it guarded.

Landed in the pumice tree via `a1e53e5fd` (which regenerated these bridges to
widen the slave IDs). Verified 2026-09-11: `test_ddr2_char_macro[bank_parallel]`
-- the two-writer test that was the standing failure -- PASSES; the full char
framework is 203 passed / 2 xfailed; the pumice component regression is 219/219;
verilator is clean on both board harnesses. Re-running `regen_bridges.sh`
reproduces the committed RTL byte-identically, so the tree is current with the
generator.

Nothing was needed from pumice. Its write responses still leave in FR-FCFS
order rather than AW order, which remains a legitimate AXI4 behaviour; what
changed is that the fabric no longer assumes otherwise.


macro suite could compile again (the `-Wno-PINMISSING` waiver for the bridge regen's
`unmapped_*` ports). Fails identically on HEAD's inline macro and on the extracted
`char_engine_block`, so it predates the refactor.

**Symptom:** `pumice_wr_adapter.sv:168` BRIDGE-010 `$error` at ~31 us: "slave returned B out of
AW order".

**Be precise about where the gap is — the per-generator B handling IS built and
is correct.** `bridge_ddr2_char_wr_xbar.sv:222-224,413-415` steers B to the
owning master by `bid_bridge_id` and gates each master's `bready` so only the
owner's ready reaches the slave; the master-side adapters pass their own B
through. That is exactly the queued-B, per-generator-ready design, and none of
it is the problem.

The problem is the **KEY the ownership lookup indexes on**. `pumice_wr_adapter.sv:99-129`
pushes the issuing master's `bridge_id` into `wr_fifo` at AW accept and reads it
at the HEAD: `bid_bridge_id = wr_fifo[rd_ptr]`. So "who owns this B" resolves to
"whoever issued the OLDEST outstanding AW", not "whoever issued the AW whose ID
this B carries". When pumice returns B out of AW order the head names the wrong
generator, and then the otherwise-correct per-master handshake completes cleanly
against it. The steering works; it is aimed by position.

Worth noting for the fix: the adapter ALREADY records the AWID per slot
(`wr_id_fifo`, :156) — but only inside `ifndef SYNTHESIS`, purely to drive this
assertion. The information needed to route by ID is being captured in
simulation and thrown away in synthesis. Routing by ID means searching the FIFO
for the matching entry instead of taking the head, i.e. a small CAM over
`WR_FIFO_DEPTH`. pumice's write CAM commits in FR-FCFS order (oldest schedulable per row, not
global AW order), so with two writers interleaving, a younger writer's B can come back before an
older one's. The check is sim-only (`translate_off`); on the board the B would silently reach the
WRONG generator (its bresp/count is credited to the other gen). AXI4 permits the slave's
reordering between IDs, so this is a system contract gap, not a protocol violation.

**Not affecting the numbers taken so far:** every board characterization run drives generator 0
alone (one writer, one reader), where position routing cannot misroute. Only bank_parallel /
multi-generator runs are exposed.

**Fix options (decide, do not patch blind):**
1. pumice: return B in AW order -- the write-side twin of `pumice_rd_return_ring` (the read
   path already holds R returns to AR order). Costs a small ticket ring; keeps the bridge
   position-routed as generated.
2. bridge: regenerate `bridge_ddr2_char_wr` with ID-based B routing (each generator already
   owns a distinct AWID space in bank_parallel). The converters/bridge family is in-order by
   design, so this is a generator feature.
3. Test-only: run bank_parallel with `SCHED_POLICY.order_mode=1` (in_order) -- confirms the
   mechanism, does not fix the board exposure.

Of the three, (2) is the smallest change and matches what the crossbar already
wants to do: the per-master steering and ready gating stay exactly as they are,
only the lookup changes from "head of the FIFO" to "the entry whose AWID equals
this BID". Option (1) is the bigger statement -- it would make pumice's write
responses AW-ordered like its reads, which is a controller guarantee rather
than a harness fix and would suit any position-routed interconnect downstream.

Also note the BRIDGE-010 message prints the ID strings garbled (`%0h` applied to the message
continuation) -- cosmetic, in the generated adapter template.

---

---

## PUMICE-031 — REG_LEVEL never reached pumice's TBs; the medium tier had never run
**Status:** CLOSED 2026-09-11  **Priority:** was P2
**Found by:** the TEST_LEVEL conftest-stamp survey (TOOL-016).

The fub, macro and top conftests each stamped `os.environ['TEST_LEVEL'] =
REG_LEVEL`, and cocotb_test copies os.environ over every per-cell export, so
the grid expanded while every cell ran at the stamped depth. In pumice that hid
a second defect. The Group C TBs (rd/wr intake, core_dfi, top_csr, top) grade
on `basic`/`medium`/`full`, but the stamp fed `gate`/`func`/`full`. Gate and
func both fell through to the `basic` default, and **the `medium` tier had
never run in any regression.**

Fix: each wrapper maps the level once at module scope, exports it per cell,
and its depth tables carry gate/func keys beside basic/medium. The stamps are
gone from all three areas. Commits: `33ed558e5` (fub), `b58366f0b` (top +
macro).

Proof: rd_intake read 6 / 24 / 64 bursts at gate / func / full (func had been
6). `test_pumice_top[wr_rd_b2b_multi]` simulated 10.8 / 23.3 / 42.0 us, its
8 / 24 / 48-burst table. fub FULL 96/96; macro + top FULL 123/123; top FUNC
120/120 (the first medium run); no reruns; FULL node sets unchanged.

Left alone: the 17 directed Group B tests. Their loop counts are protocol
structure, not depth, and they never read the level.

---

## PUMICE-032 — three coverage gaps behind green runs
**Status:** CLOSED 2026-09-11  **Priority:** was P2
**Found by:** the PUMICE-031 sweep.

1. **Silicon-bug guards in no regression.** `test_a7ddrphy_bl4_anchored`,
   `_gear_mismatch`, `_read_window` and `test_axi_rd_device_word_check` sat at
   the dv/tests root, which no area collects. They are now the `phy/` area, in
   the dispatcher's AREAS: 16 pass, 2 skip. The skips are gear_mismatch's own,
   disproven on silicon, and it keeps its reason. `4f7dda96b`.
2. **The macro DFI-layer test ran at gear 0.** It never drove `gear_i`,
   `n_subcmd_i` or the strides, which read 0 under Verilator, so a
   DFI_RATE=2 build ran with phase 1's enables masked. A model that only asked
   whether an enable was non-zero passed anyway. It now drives the board
   default and rejects any partial enable; a gear-0 mutant goes red.
   `b53e2b822`.
3. **A requirement cited a skipped test.** design-requirements.md's
   "gear=MAX bit-identical" row cited "macro regression (109)" (3 tests now)
   and the skipped `test_a7ddrphy_gear_mismatch`. It now names the real
   enforcement: the mask is all-ones by construction, every core/top TB runs
   at gear = MAX, and the item-2 check catches a masked phase. `b53e2b822`.

Side effect: the pre-commit filelist check crashed on a tracked `.sby` that
another session's in-flight rename had deleted, blocking every commit in the
repo. Fixed in `36a971588`.

Not done: `dfi_init_complete_i` is still undriven in the DFI-layer test, which
does not exercise init. No test runs gear < MAX, and the requirement does not
ask for one.

## PUMICE-036 — every published board number predates the 2026-09-13/14 harness rewrite
**Status:** CLOSED 2026-09-14  **Priority:** was P1

The read/write figures quoted everywhere in this area -- **571.3 MB/s read,
570.2 write, 95% of a 600 MB/s peak** -- were measured before a run of changes
that all touch the measured path:

- the data bridges were removed and the generators now drive `s_axi` through a
  direct N:1 merge plus one skid layer (8f75add68, d54103176);
- the pattern generators' data function changed from a two-multiply hash to four
  rotate-XOR rounds, deleting a 4-stage pipeline, a 16-deep staging FIFO and 48
  DSPs (475b9a53b);
- the generator array went from 2+2 to 4+4 (a78007109);
- the AXI id scheme changed so the generator index rides inside 8 bits
  (7baf98780).

None of that is expected to cost bandwidth -- the skid is full-rate, the hash is
combinational and stallable, and the W address is consumed only on a burst's
last beat so beats still issue one per cycle. **Expected is not measured.** The
simulation asserts only that bandwidth is positive, so nothing in the gate would
catch a regression here.

**Do, in order:**
1. `PUMICE_SYS_75=1 make bitstream && make program` (the 4+4 bitstream is built
   and closes at +0.016 ns).
2. `python3 bin/axlen_sweep.py` -- confirm the read/write figures and the
   Little's-law fit still hold at the new harness.
3. `python3 bin/outstanding_sweep.py` -- never run on hardware. The outstanding
   dial and the 32-deep ceiling exist precisely so this curve can be taken, and
   it is the direct evidence for [[PUMICE-030]]'s latency argument.
4. `python3 bin/bank_gap_sweep.py` then `python3 bin/plot_bank_gap.py
   reports/bank_gap_sweep.json` -- also never run on hardware. Four generators
   on four banks, concurrent read+write, gap 0..15 across three address orders.
5. Check the knees ORDER as §8 of the methodology doc predicts: rising from
   cacheline to row-major to col-major, and falling as generators are added. If
   they do not, either the sweep or the controller is not doing what it claims.

**Update when done:** AT-A-GLANCE, the char guide, and [[PUMICE-030]]'s table.

---

---

## Result — no regression, and the knees order correctly

All five steps run on the Nexys A7 (ttyUSB5, 4+4 bitstream, 75 MHz, BL4, x16,
`open_page`). `axlen_sweep.py` needed a one-line fix first: a missing
`import sys` that had been there since its original commit f02a4b569, so the
script had never once been runnable.

**Step 2 — axlen_sweep. No regression from the rewrite.**

| AxLEN | rd MB/s | % peak | latency | Little's-law prediction |
|---|---|---|---|---|
| 1 | 98.3 | 16.4% | 51.9 | 90.7 |
| 2 | 196.3 | 32.7% | 48.0 | 192.0 |
| 4 | 368.2 | 61.4% | 50.6 | 351.8 |
| 8 | 570.5 | 95.1% | 50.2 | 570.0 |
| 16 | 570.8 | 95.1% | 96.0 | 570.0 |

**Step 3 — outstanding_sweep, first hardware run.** Knees scale as 1/AxLEN,
errors 0-6.5%: AxLEN 1 no knee inside 32 (389.5 MB/s, still climbing), AxLEN 2
knee ~32 (model 25), AxLEN 4 ~24 (model 12), AxLEN 8 ~12 (model 6).

**Steps 4 and 5 — bank_gap_sweep, 192 points, knees order as predicted.**
Largest gap still within 3% of the gap-0 read bandwidth:

| order | 4+4 | 3+3 | 2+2 | 1+1 |
|---|---|---|---|---|
| cacheline | 15 | 15 | 9 | 0 |
| row_major | 15 | 15 | 9 | 0 |
| col_major | 15 | 15 | 15 | 15 |

Read MB/s gap 0 -> 15: 1+1 row_major 574 -> 206 (36% retained), 2+2 575 -> 417
(73%), 3+3 565 -> 565, 4+4 559 -> 559.

The knee rises with generator count because a gap only bends the curve once
aggregate demand drops BELOW the controller's ceiling; at 4+4 even gap 15
leaves each generator at a ~52% duty cycle across four engines, so demand still
exceeds the ceiling. The 4-bit gap field cannot inject enough idle to starve
four generators — at high counts the lever is the outstanding dial, not the gap.
col_major is flat at every count because it is page-miss bound at ~150 MB/s
(25% of peak): the DRAM is the limit, so pacing never binds. A flat col_major
curve is the expected result, not a missing measurement.

**What the run cost, and what it found.** Three defects in the instrument —
`beats_mismatched()` reading only reader 0 (three of four readers unverified at
4+4), points not independent because damage leaked forward, and a docstring
claiming bank disjointness that only holds for col_major — plus one real
correctness defect in the design, filed as **PUMICE-037 (P0)**. 22 of the 192
points carry mismatches and must not be quoted as clean operating points; the
plotter now rings them. The bandwidth numbers themselves stand.

**Still to do (carried, not blocking):** update AT-A-GLANCE, the char guide and
[[PUMICE-030]]'s table with the figures above.

---

## PUMICE-037 — concurrent read+write with reader gap >= 8 returns bad data AND corrupts cells
**Status:** CLOSED 2026-09-15  **Priority:** P0  **Fixed:** 237d82292

### ROOT CAUSE (ILA, 2026-09-15): write data driven into a read return

`dfi_wrdata_en` asserts while read data is still returning. One capture
(trigger = `rd_dbg_mismatch`, 4096 samples, gap 13/15, tRTW already 8):

* 49 cycles with `wrdata_en` asserted while `rddata_valid`/`rddata_en` active
* 89 corrupted beats; **80% within 12 cycles of such an overlap** (median 7,
  min 6)
* **51% of corrupted beats read back `ffffffffffffffff`** — all ones, the
  signature of an UNDRIVEN DQ bus (matches the 59% all-ones in the earlier
  capture). 0% all-zeros.

Sample 2042 has `wrdata_en=3` while `rddata_valid=3`; the first mismatch lands
at 2048 with `actual=ffffffffffffffff` against `expected=fe1daf8638b768c3`.
The write driver turning on collapses the read data on the shared DQ pins and
the controller returns the floating bus as valid read data -- correct framing,
`stray=0`, exact beat count, wrong payload, which is the whole board signature.

**It is deterministic, not a race.** Overlap spacing is 42 cycles, 44 of 49
occurrences (rest 84 = 2x42). The char generators are fixed-function machines,
so a fixed period hits the same boundary every time -- which is why counts
repeat to ~2% and why tRTW oscillates rather than improving monotonically.

### Why tRTW cannot fix it

tRTW constrains RD **command** -> WR **command**. The collision is between DATA
phases, which sit at different offsets from their commands: read data returns
`t_rddata_en`+ (6..8) cycles after the RD, write data goes out ~WL (1) cycle
after the WR. An 8-cycle command spacing still lets a write's data land inside
a read's return. Measured: tRTW=8 clears gaps 0-12, tRTW=16 still leaves
[2,4,0] at gap 15, and the required value appears to "scale with gap" because
each value shifts one fixed period against the other.

The correct constraint is expressible from the aligner, whose window is
stateless (`pumice_dfi_rd_aligner.sv`: a read admitted at A occupies DQ over
`[A + t_rddata_en, A + t_rddata_en + EN_CYC - 1]`). A write issued at T drives
DQ from `T + wrlat`, so no-collision requires

    T > A + t_rddata_en + EN_CYC - 1 - wrlat

Board: 6 + 2 - 1 - 1 = 6, +1 for the registered ok = **8** -- exactly the tRTW
the board wanted, confirming the arithmetic from two directions. The fix is to
gate write-column issue on the read-return window being clear (tracked per
in-flight read), not on a static command-distance counter.

### Why every simulation missed it

DFI carries `wrdata` and `rddata` on SEPARATE buses, so this overlap is legal
at the DFI boundary and only destructive on the PHY's shared DQ pins. Clean at
`pumice_top` with the hardware generators replicated exactly (including the
S_GAP RREADY backpressure), board geometry, board burst shape, 64 KB / 32
pages, under both the idealised and a7ddrphy read models. LiteDRAM is clean at
every gap on the identical harness and ties its RD->WR edge to
`phy.read_latency`, not to any JEDEC number.

### Fixed so far

`65968b9b4` corrected three timing-derivation defects (tWR anchor, tRTW read-
window floor, phase margin), all confirmed against LiteDRAM on the same part
and clock. Board: gaps 0,2,4,6,8,10,12 now **0/3 failing** (8 and 12 were 3/3).
Residual gap >= 13 remains -- 13:1547, 14:1436, 15:709 -- and is the overlap
above. Note an earlier report of "only gap 15 fails" was a sampling artifact
(the sweep stepped 0,2,..,12,15); 13 and 14 fail too.

Not throughput-related: pumice still corrupts at 64 MB/s with one burst in
flight, less than HALF LiteDRAM's 142.9 MB/s.

Found while running PUMICE-036 on the board (4+4 bitstream, 75 MHz, BL4, x16,
`open_page`). It is a correctness defect, not a performance one, and it is the
reason the first `bank_gap_sweep` run looked incoherent.

**The trigger, narrowed by elimination on hardware:**

| configuration | result |
|---|---|
| prefill 128 MiB, then read every bank read-only, all 3 families | CLEAN |
| reader ALONE, gap 0..15 | CLEAN at every gap |
| writer ALONE, gap 0..15 (incremental, marches all banks) | cells CLEAN |
| writer gap 0..15, **reader gap 0** | CLEAN at every writer gap |
| **reader gap 0..7** + concurrent writer | CLEAN |
| **reader gap >= 8** + concurrent writer | 1.5k-7k of 32000 beats mismatched |
| 4+4 concurrent, gap 0 (and gap 4), incremental | CLEAN, cells CLEAN |

So it needs BOTH a concurrent writer AND the reader's gap field at 8 or above.
Neither engine alone does it at any gap, and the writer's own gap never does it.

**Two distinct symptoms, and the second is the serious one:**
1. *Transient* — with writer and reader on disjoint banks (row_major, writer
   confined to bank 0, reader to bank 4) the reader reports thousands of
   mismatched beats, but a read-only audit of all eight banks afterwards is
   CLEAN. The cells were always right; the returned data was not.
2. *Persistent* — with writer and reader ranges OVERLAPPING (incremental) the
   audit afterwards shows real DAMAGE: banks 3/4/6/7 dirty, 248..4636
   mismatched beats each, reproducible on re-read. Cells genuinely hold wrong
   data. **The write engine alone never does this** (verified above), and a
   read engine cannot write, so something in the concurrent path is either
   writing the wrong data or writing it to the wrong address.

**Why the first sweep run was unreadable.** Damage from one point is inherited
by every later point. `row_major g1` reported an identical 3694 mismatched
beats at eight consecutive gaps; that constant is the *previous* family's
damage being re-read, not a property of those points. Confirmed directly: a
later row_major point reported exactly 5025, which was precisely the audited
mismatch count of bank 4 going in. `bin/bank_gap_sweep.py` now re-fills the
device before every point (`PREFILL=point`, the default) so points are
independent.

**Not yet determined: whether this is pumice or the harness.** Both are live:
- *Harness read engine* — in `axi4_master_rd_crc_check.sv` the R-beat
  bookkeeping (`if (w_r_beat)`, ~line 707) sits inside the `S_RUN` arm, while
  the mismatch compare at the bottom of the same block runs unconditionally.
  A beat that lands while the FSM is in `S_GAP` is compared but not counted.
  **Measured and largely RULED OUT.** That path can only fire through the
  stray-beat drain (`fub_rready = w_r_consuming || w_stray_beat`), and the
  sweep now records `o_stray_beats` per reader: **every one of the 22 failing
  points reports stray = 0**, across 192 points. No beat was drained without an
  owner, so the mismatching beats were legitimately outstanding and came back
  with the wrong DATA. That is a controller-side answer, not a bookkeeping
  artifact — and it is consistent with symptom 2, which the read engine could
  never have produced anyway.
- *pumice* — symptom 2 points at the controller under mixed R/W. Note the
  known refresh-collision suspicion in [[project_pumice_board_bringup_tuple]].

The sharp edge at exactly 8 (bit 3 of the 4-bit gap field) is unexplained; the
gap logic in both engines is a plain 4-bit countdown with nothing special at 8,
and the register layout has gap[27:24] with nothing adjacent.

**Sim repro IMPLEMENTED 2026-09-14 — and it does NOT reproduce.**

`test_ddr2_char_macro.py::test_ddr2_char_macro_concurrent_gap`, ten points:
rd_gap 0/4/7 (control, below the board's edge), 8/12/15 (at and above it),
wr_gap 8/15 at rd_gap 0 (the writer-only isolation the board measured clean),
and 8/8, 15/15 (the sweep's own failing shape). Writer on bank 0, reader on
bank 4, wrapped in one page each, ONE `go(wr_mask, rd_mask)` for both — the
board's `start_both`. **All ten pass.**

The test is armed, not decorative: giving the reader a wrong LFSR seed fails
all ten with "reader 0 data error", and restoring passes all ten. That
mutation was run at the shipped configuration, not a convenient one.

So the sim does not see it **at this geometry**, which is the substance of
[[PUMICE-028]]: this build is `DRAM_BL=8` where the board is BL4, so one DRAM
burst is 2 AXI beats here against 1 on silicon. The next step is no longer
"write the test" — it is running this test at the board's geometry, and
PUMICE-028 records that the board point does not yet run clean in sim.

**Driven at pumice_top too 2026-09-14 — also does NOT reproduce.**
`test_pumice_top_concurrent_rw`, 32 points, all clean. Writer and reader in
flight together on disjoint banks, reader pacing itself between bursts, with
the golden MemoryModel checking BOTH symptoms separately (read beats vs golden
= "bad data"; written cells vs what was written = "corruption"):

| axis | values swept | result |
|---|---|---|
| reader gap | 0, 4, **8**, **15** | clean |
| geometry | bl8 sim point, **bl4x16 board** | clean |
| DFI read latency | 2, **7** (board tuple rden 6 / rddata_delay 7) | clean |
| refresh | default, tight (forces refresh INTO the traffic) | clean |
| reads in flight | 1, **32** (board depth, engine-style B2B ARs) | clean |

Armed, verified twice: corrupting the expected value fails and names the
address, and a permanent count guard asserts the reader compared
`n x BL_WORDS` beats — a concurrent test that returns zero beats would
otherwise pass vacuously.

**Read concurrency was the leading hypothesis and it is now TESTED AND DEAD.**
The first cut of this test used the default sequence runner, which serialises
each burst against its own response and caps outstanding at ONE -- so the gap
always landed on an empty pipe and nothing could ever be in flight across it,
which is precisely the state an `S_GAP`-class hazard needs. Sean: "the bfms
fully support b2b cycles". Re-driven through `run_axi4_sequence_engine`, which
queues ARs back-to-back with no per-burst response wait, at the board's depth
of 32. Still clean.

The depth axis is real, not decorative -- measured, not assumed: depth 1 gives
64 groups and 40990 ns of sim, depth 32 gives 2 groups and 30000 ns, both
comparing the same 64 beats.

**So it is not the controller, across every board-faithful axis inside it:**
geometry, read latency, refresh, and read concurrency. Four rounds of "add an
axis, still clean" says the search space is wrong, not under-sampled.

**Everything still untested is OUTSIDE pumice_top** -- `char_gen_unit`'s N:1
merge and boundary skids, the geared wrapper's dwidth converters, and the real
a7ddrphy against a real device. The board traverses all three; none of these
sims do.

---

### CAUGHT ON THE BOARD WITH AN ILA, 2026-09-14 — it is PHY-side, not the AXI return path

Sim could not reproduce it, so the defect was captured where it lives.
`reports/ila_mism.csv` (4097 samples, 394 mismatching beats in one window).

**How.** `char_engine_block` already exposed a per-beat debug stream --
`rd_dbg_valid / actual / expected / mismatch` -- that was never wired to the
top and whose FIFO defaulted to depth 0, so nothing had ever used it.
Threaded `RD_DBG_FIFO_DEPTH` through the harness and top (default 0, so the
production bitstream is unchanged), `mark_debug`ged the stream, and added a
`mism` trigger mode to `capture_ila.tcl`. **Triggering on the corruption
itself** is the whole point: every other trigger fires on normal traffic, and
at this error rate a free-running capture is a lottery that would not say
which beat lost. ILA build closes at **WNS +0.010 ns, 0 failing endpoints**,
so the capture is trustworthy.

**What the failing beats look like:**

| | |
|---|---|
| mismatching beats captured | 394 |
| `actual` == `ffffffffffffffff` (all-ones) | 233 (59%) |
| `actual` == all-zeros | 0 |
| other (genuinely different data) | 161 (41%) |

All-ones with zero all-zeros is the signature of an **undriven DQ bus** -- a
read whose capture window missed -- not of a mangled datapath.

**The corruption is already present at the DFI boundary.** Baseline all-ones on
`w_dfi_rddata` is 1.6% of samples, and with GOOD beats in the same capture as
the control:

| | within 11 cycles of an all-ones on the DFI bus |
|---|---|
| FAILING beats | **82%** |
| GOOD beats | **30%** |

So pumice's return path is faithfully delivering what the PHY handed it. That
moves the defect from the controller's AXI/return logic to the PHY read
capture, and is consistent with 32 clean points at `pumice_top` -- the sim's
DFI slave BFM always returns correct data, so no controller-level test could
ever have seen this.

**Write-to-read turnaround is RULED OUT as the mechanism.** It was the obvious
hypothesis from the waveform (writes sit a few cycles before the failing
reads), and the control kills it: within 4 cycles of a `dfi_wrdata_en`,
FAILING 59% vs GOOD 59% -- no discrimination at all. At 7 cycles it is 81% vs
67%, which is weak and not worth building on. Do not re-open tWTR/tRTW on this
evidence.

**Read-eye narrowing under write load is RULED OUT (2026-09-15).** It was the
natural follow-up to the all-ones signature and it is wrong. Tap sweep at the
operating bitslip, quiet vs with three background writers hammering other
banks, load VERIFIED in flight on every row (`gen_done` checked after each
read, printed per row):

| tap | quiet | loaded |
|---|---|---|
| 0-9 | clean | clean |
| 10 | 3055 mismatched | 3034 mismatched |
| 11-13 | 4096 mismatched | 4096 mismatched |

Same eye edge, same counts. Write traffic does not move the read eye, so the
corruption is not read-capture margin against bus loading.

**Three earlier attempts at this measurement were WRONG and are recorded so
nobody repeats them.** The first reported "no passing tap when loaded" -- an
eye collapse -- and it was an artifact: it armed the load and then called
`_test()`, which begins with `_reinit()` (a soft reset) and stops it. The
second had the same ordering bug. The third died on a bad API call. Worse,
each left `TXN_MAX` writers running, and **a runaway generator survives
`soft_reset`** ([[feedback_runaway_generators_survive_soft_reset]]): the next
run's leveling reported "no passing tap at ANY bitslip -- analog read path not
recoverable, check sys4x_dqs / IO / pins", which reads as dead silicon. The
board was fine; a reprogram plus re-level gave `verify OK` immediately. Only
reprogramming clears a runaway.

### NOT all board tests fail -- 11%, and the failing ones share three traits

Sean asked the right question: do ALL board tests fail? They do not. Of the
192-point sweep, **22 points (11%) mismatch**; `axlen_sweep` and
`outstanding_sweep` are entirely clean. The failures are sharply structured:

| trait | failing points |
|---|---|
| generator count | n_gen **1 (19) and 2 (3)** -- never 3 or 4 |
| address order | incremental (14), row_major (8) -- **col_major NEVER** |
| gap | mismatches rise MONOTONICALLY: 80 / 122 / 435 at gaps 1/3/6, then ~5000 from gap 8 |

col_major is the page-MISS family: every burst activates a different row, so it
can never hold a stale belief about an open one. The two families that DO fail
are page-HIT streams, where a gap leaves a row **open and idle** between bursts.

### RETRACTED: it IS a refresh collision (Sean was right, 2026-09-15)

The section below concluded "not refresh" from an invalid experiment, and the
ILA trace refutes it. **Both of my arguments were wrong:**

1. *"Rare refresh is no better, so refresh does not drive it."* tREFI 32767 MC
   cycles at 75 MHz is **437 us** between refreshes against a JEDEC tREFI of
   7.8 us. That run was not testing a refresh collision, it was violating DRAM
   RETENTION -- those 62439 mismatched beats are decayed cells, a different
   failure wearing the same symptom. The experiment could not have answered the
   question it was asked.
2. *"Close page fixes it, so it is the open page."* Backwards. Close page
   removes the open-row state that a refresh would invalidate, so close page
   fixing it is evidence **FOR** a refresh collision, not against it.

**The trace, from the capture already committed** (`reports/ila_mism.csv`,
window around the refresh at sample 2551):

```
 2538  RD  bank4          reads issued to bank 4
 2539  RD  bank4
 2540  RD  bank4
 2546  PRE bank0
 2547  PRE bank4      <-- bank 4 precharged 7 cycles after its reads
 2551  REF            <-- refresh
 2568  ACT bank4      <-- row re-activated 17 cycles later
 2575  RD  bank4          reads resume
```

`rd_dbg_mismatch` is asserted CONTINUOUSLY from 2530 to 2579 -- the entire
window from the reads, through the precharge and refresh, until well after the
re-ACT. The refresh's precharge lands on a bank with reads still in flight
through the PHY, and everything in that window comes back wrong. All-ones is
what an undriven DQ bus reads as, which is the 59% signature.

Three of the five refreshes in the capture show the clean pattern
(REF -> ACT bank4 +17 -> ACT bank0 +23 -> RDs +24); the mismatch clusters are
the ones where reads were already outstanding when the refresh arrived.

**This also explains every trait of the failure distribution** without needing
the open-page argument to be about page policy per se: col_major never fails
because it precharges per access and has no in-flight window for a refresh to
collide with; the gap dependence is monotonic because more idle means more
chance a refresh lands mid-flight; low generator counts fail because the read
pipeline is sparser.

### Correct refresh programming does NOT fix it (2026-09-15)

Two separate refresh problems, and only one of them is PUMICE-037.

**Problem 1, real and now fixed: the host had the clock wrong.**
`pumice_char.Config.mc_clk_hz` defaulted to 100 MHz; the board measures
**72 MHz** (bus meter: 233,964,081 cycles in 3.248 s). Every JEDEC timing was
converted into cycles for the wrong clock. Most land conservative at a slower
clock -- a cycle count for a faster clock buys MORE real time -- but tREFI
inverts: 780 cycles is 7.8 us at 100 MHz and **10.8 us at 72 MHz**, against a
JEDEC MAXIMUM of 7.8. The part was under-refreshed ~38% for this entire
investigation. Fixed in `bfcff909d`, with `measure_mc_clk_hz()` /
`check_mc_clk_hz()` so a host can ask the board instead of being told.

**Problem 2, still open: that was not the cause.** Same workload, open page,
`incremental`, 3 repeats, beats mismatched PER RUN:

| refresh programmed for | gap 8 | gap 12 |
|---|---|---|
| 100 MHz (wrong, tREFI 10.8 us) | 5727 | 1959 |
| 75 MHz (correct, tREFI 7.8 us) | 5158 | 2790 |

3/3 runs fail either way and the rates are the same to within run-to-run
scatter. **Correcting the refresh interval does not suppress the corruption**,
so the under-refresh was a genuine misprogramming sitting on top of the defect,
not the defect. (row_major was still running when the window closed; incremental
alone settles the question.)

That leaves the collision itself as the defect: pumice issues precharge + REF
while reads are in flight, and tREFI only sets how OFTEN that window comes
round, not whether it corrupts when it does.

### The aligner DOES capture the PHY preamble -- but fixing it is not viable, and it is not the board defect

Sean: "We had rd alignment there before but an earlier Claude removed it." The
history is exactly that. Three fixes landed and were reverted within an HOUR on
2026-07-14 (2f08eb23e/f0354c137, dcaedce4b/39827800a, 144b3860f/19d483880), and
79a848b69 replaced them with the multi-outstanding redesign, which gates
capture on `r_outstanding != 0` -- its own comment calls that "a WIDE
admit->return gate".

**The defect is real and now has a test.** `cocotb_test_rd_aligner_phy_preamble`
injects what the 2026-07-14 ILA saw: a `dfi_rddata_valid` one cycle BEFORE the
enable window with the device not driving DQ. The aligner captures it, because
the read IS outstanding at that moment and a wide gate cannot exclude it.
`rd_last` then fires a word early and the whole read stream shifts. Nothing in
the suite had ever injected a preamble, so this had never been tested either
way.

**But the fix is not viable, and this is why it keeps being reverted.**
Restoring 2f08eb23e's enable-window credit (+1 per enable cycle, -1 per
captured word):

| check | result |
|---|---|
| rd_aligner unit suite | 4/4 pass |
| full pumice fub+macro+top | 274 pass / 0 fail |
| board bitstream at 75 MHz | builds, **WNS +0.055 ns** (better than the +0.016 without it) |
| `test_ddr2_char_uart` a7gated cases | **2 passed WITHOUT the fix, 2 FAILED WITH it** (direct A/B, clean build each way) |
| board corruption, gap 8 | 5158 -> 4795 beats/run -- **inside run-to-run scatter** |
| board corruption, gap 12 | 2790 -> 2020 beats/run -- same |

So it breaks a previously-passing path AND does not reduce the corruption. The
July reverts were almost certainly this same wall, hit three times in an hour.

RTL reverted. The test stays as `xfail(strict=True)` so the preamble capture is
documented, reproducible and impossible to lose again -- and flips to XPASS the
moment a viable fix lands.

**What this leaves.** The preamble capture is a genuine bug that needs a fix
compatible with the a7gated path -- look at what those two tests model before
attempting another credit scheme. And PUMICE-037 itself is still open: the
aligner preamble is NOT its cause.

### RETRACTED: the scheduler-layer "reproduction" was a FALSE POSITIVE

The section below claimed `PRE(bank 4) issued 1 cycles after RD, tRTP=2` and
named a stale-registered-readiness hole in `w_rfsh_pre_found`. **All of it was
wrong.** The scheduler TB did not stamp cycles on captured commands and the
helper fell back to the LIST INDEX, so "1 cycle after RD" actually meant "PRE
was the next COMMAND in the stream" -- a statement about ordering, not timing.
It nearly drove an RTL change to code that was already correct: `r_guard0` IS
set on a fired column (`pumice_cmd_arbiter.sv:1282` includes `r_do_rd`) and
`w_rfsh_pre_found` DOES gate on `!w_guarded[j]`.

`_cmd_sink` now stamps the issue cycle, and the helper asserts rather than
falling back to an index.

### The scheduler layer does NOT reproduce it -- two tests, both passing

| test | what it checks | result |
|---|---|---|
| `..._refresh_inflight_read` | tRTP from the last same-bank column, tRP into the REF | **spacing respects tRTP=2 tRP=3** |
| `..._refresh_read_stream` | every column lands on a bank with an OPEN ROW, across a sustained stream | **408 columns, 2 REF, all on an open row** |

The second is the one that matters: the first attempt had ONE read outstanding,
which is not the board's state. This streams reads continuously by re-arming the
mock CAM as each issues, so a refresh has to cut into a live queue -- 408
columns across 2 refreshes -- and models row state from the command stream
itself (ACT opens, PRE closes that bank, REF closes all, AP closes on the
column). Not one column is issued to a bank with no open row.

**So the command stream pumice generates is correct**, in both respects that
could produce the board's all-ones: spacing, and never reading a closed row.
That eliminates the scheduler and pushes the defect BELOW it -- the DFI layer's
phase packing and read-return alignment, or the PHY capture. Note the prior
VCD work already pointing there: commit 79fb58a66, "mask-removal corruption is
DFI read-return alignment".

(One more modelling trap recorded: a DDR2 column command carries the COLUMN, so
`cmd_row_o` reads 0 on RD/WR. Comparing it against the open row flags every
column -- 408 of 408 on the first run. Only the "is a row open" half is
checkable from the command stream.)

### Superseded: "REPRODUCED IN SIM at the scheduler layer"

`test_pumice_mem_cmd_scheduler_refresh_inflight_read` — no board, no PHY, no
data path:

```
PUMICE-037: PRE(bank 4) issued 1 cycles after RD to the same bank, tRTP=2.
The DRAM is precharged while its read burst is still being driven out.
```

The refresh path precharges a bank **one cycle** after issuing a READ to it,
against a programmed tRTP of 2. That is the collision, at the layer that
decides command spacing. It is kept as `xfail(strict=True)` so the suite stays
green and the test flips to XPASS the moment the RTL is fixed.

Why no earlier sim saw it: the char macro and `pumice_top` both hand the
controller a DFI slave that always returns correct data, so a truncated read
burst still reads back clean. Only a check on COMMAND SPACING can see it, and
that is what this layer owns.

**Candidate location, from the RTL's own reasoning.** The refresh-drain PRE
picks a bank via `w_rfsh_pre_found`, which gates on `r_bank_pre_ready` — a
REGISTERED copy of the bank-timer readiness (`pumice_cmd_arbiter.sv:533`). The
comment at :304 states the hazard exactly:

> "a column fired <2 cycles ago has not yet dropped this bank's registered
> pre_ready (tRTP/tWR load), so an unguarded PRE pick — normal or
> refresh-drain — could precharge on stale readiness."

`w_guarded` is the intended protection and covers columns in the PICK PIPELINE
(selection / pre-pick, plus the output stage via `w_inflight_col`). The failing
case is a column that has already ISSUED, where the only remaining protection
is that stale registered readiness. This is the same stale-registered-bank-image
family as [[project_pumice_scheduler_ceiling_rootcause]] and
[[project_pumice_mask_ap_hazard_and_tccd_csr]].

Note the REFpb (LPDDR2 per-bank) arm gates on
`r_bank_pre_ready[RK0][refresh_bank_i] && !w_guarded[...]` explicitly, while the
REFab arm relies on `w_rfsh_pre_found`. Whether that asymmetry matters is worth
checking, but it is NOT yet established — do not treat it as the diagnosis.

**What to look at:** whether the refresh scheduler drains (or blocks on)
outstanding reads before issuing precharge-all + REF. The standing suspicion in
[[project_pumice_board_bringup_tuple]] -- "residual corruption is a
refresh-collision bug" -- was right all along.

Close page remains a usable WORKAROUND (33725 beats -> 6), but it is a
workaround, not a diagnosis.

### Superseded: "it is the OPEN PAGE, and it is NOT refresh"

The obvious hypothesis was a refresh landing in that idle window, precharging
the bank while the tracker still believes the row is open -- which would
explain the all-ones. **Tested and REFUTED.** Six repeats per cell, because the
failure is intermittent (gap 12 and 15 failed in the sweep and came back clean
on a re-run, so single points prove nothing):

| config | gap 8 | gap 12 |
|---|---|---|
| open + refresh normal (tREFI 780) | 6/6 runs, 33725 beats | 0/6 |
| open + refresh RARE (tREFI 32767) | 6/6 runs, **62439 beats** | 0/6 |
| open + refresh FAST (tREFI 256) | 6/6 runs, 16529 beats | 6/6, 2759 |
| **close page**, refresh normal | 6/6 runs, **6 beats** | 6/6, **6 beats** |

Making refresh RARE does not help -- it is slightly WORSE -- so refresh rate
does not drive this. Page policy does: **close page cuts the corruption from
33725 beats to 6**, a ~5600x reduction on the identical workload. (Not zero:
about one beat per run survives, which is its own small question.)

So the trigger is an OPEN ROW left IDLE across the reader's gap, and the next
access to it returning undriven data. Refresh is ruled out as the mechanism;
what the controller does with a page it is holding open across an idle window
is not.

**Close page is a usable workaround** for anyone blocked by this, at the cost
of the open-page bandwidth.

**Next:** ILA again, but trigger on the mismatch with the DFI COMMAND bus in
the capture (ras/cas/we/bank/address are already marked) and read back the
command sequence before the failing beat: was an ACT actually issued for that
row, or did the read go out against a row the DRAM had already closed?

**Open and worth a look: the operating tap may be marginal.** `level_cache.json`
records the bring-up eye as `[0, 16]`, width 17, tap 8 centred. Today's scan
gives **0..9, width 10, with tap 8 ONE tap from the upper edge**. That is
either drift since bring-up or an artifact of test depth (more beats per tap =
more chances for a marginal tap to fail = a narrower measured eye). The
depth sweep meant to settle it was the run that hit the runaway, so it is
UNMEASURED. Re-run `txn` 16/64/256/1024 from a freshly programmed board.

**Next:** this is still a PHY read-capture question, so it belongs with the
leveling tuple ([[project_pumice_board_bringup_tuple]]: wrlat 1, rden 6,
rddata_delay 7, bitslip 0 / tap 8, eye 17 wide). Re-run the read-eye scan
WHILE a concurrent write stream is running -- the eye was characterised on a
quiet bus, and if it narrows under write activity that is the whole story.
`bin/` already has the leveling and eye tooling.

**Still recommended as the cheap partition:** run the failing
configuration with LiteDRAM swapped in for pumice. Both sit behind the
identical `char_engine_block`, and that A/B already localized the read ceiling
once ([[project_litedram_same_harness_ab]]). If LiteDRAM corrupts too, the
harness owns it and pumice is exonerated; if it does not, the defect is
pumice's and lives in something only the real PHY exposes. That is one board
run and it partitions the remaining space in half.

**Three pre-existing defects found while getting there** (all in
`dv/tests/top/test_pumice_top.py`, all fixed):
- The module read `BL` from env `"BL"`, a name nothing sets, while the runner
  exports `"DRAM_BL"` — so the Python side believed BL8 no matter what the RTL
  was built as. Harmless at the default where both formulas agree; at the board
  point it computes 2 AXI beats per burst where hardware has 1. That is
  [[PUMICE-028]]'s "overridable but never actually tested", made concrete.
- `BL_WORDS` used `BL // DFI_RATE`, correct only when device width == beat
  width. Now `(BL x device) / core`, matching `test_pumice_core_dfi.py`.
- The shared `sim_build` key was NUM_RANKS alone. A BL4 test would recompile
  the shared build out from under the BL8 suite in the same xdist worker,
  silently turning the tests that ran before it into tests of a different DUT.
  The key now carries every netlist-affecting parameter.

Geometry, read latency and refresh are pytest PARAMETERS now, not env knobs
(Sean, 2026-09-14) — an override nobody sets is how the board shape stayed
unrun.

**Three things the implementation had to get past, all worth knowing:**
- *Stale done.* The prefill leaves `gen_wr_done` high, so waiting on it
  directly returns instantly on the previous run and everything after inspects
  the PREVIOUS run's state. The first version "passed" a deliberately
  corrupted configuration in a quarter of the runtime. Fixed with
  `_wait_restart_done`, which waits for the restart to CLEAR done first.
- *ADDR_HASH does not compare in this build.* The board runs `data_mode=1`;
  in sim a reader given a deliberately wrong hash seed reports
  `beats_mismatched=0`, and so does one pointed at a page nobody wrote. Both
  mutations pass. The same mutations in LFSR mode fail loudly. Filed as
  [[PUMICE-038]] — **until it is fixed, a sim check written in data_mode=1 is
  decorative.** This test therefore uses LFSR.
- *LFSR + wrap must not revisit.* The wrap window holds
  `PAGE_BYTES/BURST_BYTES` distinct addresses; past that the walk revisits
  while the LFSR stream has moved on, so memory holds the last pass and the
  reader expects the first. Every point fails, controls included — a broken
  test, not a finding. The txn count is now capped to one pass and asserts it.
  (The board runs many passes because ADDR_HASH rewrites are idempotent.)

**The coverage hole is exact, and checked.** `test_ddr2_char_macro.py` has two
gap-bearing suites and BOTH drain the writer before the reader starts:
- `pacing_sweep_b2b` (~line 563) — `_start_writers` then
  `_wait_done(gen_wr_done)` then `_start_readers`.
- `ooo_pacing_schmoo` (~line 405, commented "Writes: preset memory") — same
  order, and its `_OOO_SCHMOO_STEPS` already includes `slow_same` at
  rd_gap=8 and `asym` at rd_gap=15.
So the gap values that fail on hardware are already in the matrix; what is
missing is running the two directions AT THE SAME TIME. The sim has never
exercised a reader gap with a writer still in flight, which is why this got to
the board. A new `test_type` that programs both and issues one concurrent
start — the board's `start_both` — should reproduce it directly.

**Second, smaller phenomenon, kept separate because it may be unrelated.** At
1+1 with the two ranges OVERLAPPING (cacheline), small mismatch counts appear
at some gaps BELOW 8 too -- 80 at gap 1, 122 at gap 3, 435 at gap 6 -- and
2+2 cacheline shows the same at gaps 10/13/14. The disjoint families (row_major
at 1+1) stay perfectly clean below 8. So overlap alone, at low generator
counts, produces sporadic small errors that the gap>=8 mechanism does not
explain. Do not fold the two together until one of them has a cause.

**Scope of the damage to published numbers:** gap 0..7 is clean, including the
4+4 concurrent case, so bandwidth at those gaps is trustworthy. Every gap >= 8
point in any concurrent sweep is measuring a broken configuration and must not
be quoted.

### REOPENED then RE-CLOSED 2026-09-16 — the first closure was premature

**The 2026-09-15 closure below was wrong and is kept for the record.** It rested
on a 0-of-192 `bank_gap_sweep` pass. That sweep runs **ONE rep per point**, and
`incremental / n_gen=1 / gap=14` was failing **8 of 10 reps** at 2-6 beats --
a point clean ~20% of the time passes a single-sample sweep one time in five.

Cause: the empirical `rtw_guard` over the derived minimum of 14 was one step
short. Gap 14 sat between the 13 and 15 the focused sweeps stepped, so nothing
probed it. Fixed in **735ea519e**, guard 4 -> 6, tRTW 18 -> 20:

    gap 14, incremental, n_gen=1, 6 reps per value
      tRTW=18 -> 5/6 failing [6,4,0,2,4,2]
      tRTW=20 -> 0/6    22 -> 0/6    24 -> 0/6    28 -> 0/6

Re-closed on DEEP plus BROAD evidence, not one pass:
  * repeat validation: **0 failing of 128 runs** (16 gaps x n_gen 1,2 x 4 reps)
  * full matrix: 192 records, 0 mismatched, 0 stray
  * char gate FULL: 213 passed, 3 xfailed, 0 failed

**Standard for any future claim on this task:** repeat every point. A single
pass over the matrix cannot distinguish 0% from 20%. This task was closed
prematurely TWICE -- once with gaps 8-12 fixed while 13-15 still failed, once
on the single-sample matrix. Both times the measurement was sound and the
inference from it was too strong.

### CLOSED 2026-09-15 — fixed and verified across the full matrix (SUPERSEDED, see above)

Board, bank_gap_sweep (3 families x 1..4 generator pairs x 16 gaps):
**22 of 192 failing points -> 0 of 192**. Zero mismatches, zero stray beats,
zero transaction-count errors. Read bandwidth median +0.9% (max +47.9% at
points that had been corrupting or stalling).

Fix: tRTW derived from MEASURED read DQ occupancy (`phy_rd_dq_busy`=14 from
the ILA) rather than from JEDEC, giving 18; plus a floor in pumice_top so a
JESD79-2-only derivation (which gave 3) cannot recreate the blind spot.

Two wrong models were held along the way and are recorded in the code:
deriving the window from `t_rddata_en + rddata_delay` (right number at
rden=6 only because 6+7=13 coincidentally equals the occupancy; it
under-derives for any shortened read path), and `Config.apply` deriving tRTW
from default alignment args while programming different ones.

Known cost, NOT fixed here: -17.4% bus bandwidth at gap 15, from paying the
fixed ~18-cycle turnaround on every direction switch. Realignment provably
cannot recover it (tRTW is alignment-independent). See PUMICE-039.

## PUMICE-042 — mc_clk timing is not preserved across the CDC to the DFI
**Status:** CLOSED 2026-09-16 (91db52b47)  **Priority:** P1

Direction turnaround (tRTW/tWTR) is enforced ONLY on the scheduler side, in
`mc_clk`. Between the scheduler and the DFI bus sits the async CDC command
FIFO, which preserves ORDER but not SPACING. On the `dfi_clk` side the only
column gate is DQ-occupancy pacing, and it is direction-blind:

    pumice_dfi_cmd_path.sv
      // A column command's burst owns the DQ bus for COL_BURST_CYC DFI cycles.
      assign w_col_ok = (r_col_pace == '0);
      ...
      if (w_fire && w_is_col) r_col_pace <= PCW'(COL_BURST_CYC - 1);

COL_BURST_CYC is ~2. So a RD followed by a WR is gated by 2 cycles at the DFI,
where tRTW requires 20.

**Why it normally hides:** the arbiter issues at roughly the DFI drain rate, so
the FIFO stays near-empty and the arbiter's spacing propagates unchanged --
tRTW appears honoured, coincidentally. Any condition that lets the FIFO BACK UP
converts a correct schedule into an incorrect command stream.

**First workload to expose it:** write batching (PUMICE-039). The drain bursts
commands in, the FIFO fills, and the cmd path drains them back-to-back --
compressing a 20-cycle RD->WR gap to 1. Every observation fits: the scheduler
scoreboard is silent (the arbiter DID space them), the ILA shows RD->WR
distance 1 on the DFI bus, there are exactly 2 violations per run (2 drain
entries), and `dfi_wrdata_en` co-asserts with `dfi_rddata_en`.

**Fix direction:** `r_col_pace` must reload direction-aware -- COL_BURST_CYC
for same-direction, the turnaround (tRTW/tWTR in DFI cycles) on a direction
change -- so the DFI side is independently safe instead of relying on the
scheduler's spacing surviving a FIFO. Shared datapath: wants a scheduler-TB
check and a board A/B behind it.

**Note:** PUMICE-037 was the same LAYER (below DFI) but a different cause
(tRTW derived too small). This is the enforcement not surviving the crossing.

### CLOSED 2026-09-16 — direction turnaround enforced on the DFI side

Separate turnaround counter beside the occupancy counter, armed by EVERY
column, reading the SAME TIMINGS CSRs the scheduler enforces (t_rtw_i/t_wtr_i
threaded core -> layer -> cmd path). No new CSR: a second copy of one timing is
how two enforcers drift apart, which is PUMICE-037's failure mode.

Board, batching enabled (was 4-152 mismatched beats/run):
  gap12 hi=2/lo=1   0 mismatched, bus +29.9%
  gap15 hi=2/lo=1   0 mismatched (0/8 reps), bus +25.0%
  gap15 hi=8/lo=4   1 in 1/8 reps -> PUMICE-043
Normal path unaffected: 192 records 0/0, read+bus BW median +0.00%.
Timing WNS +0.150. Char gate 213 passed, 3 xfailed.

FIRST ATTEMPT WAS WRONG and the board caught it by changing NOTHING -- same
corruption, same bandwidth. Inverted mux (a RD armed t_wtr=4 where the next WR
needs t_rtw=20) and armed only on direction CHANGES. A gate that blocks 4 where
20 is needed is indistinguishable from no gate; "no observable change" was the
tell. One counter also cannot express "same direction may go in 2, opposite
must wait 20".
