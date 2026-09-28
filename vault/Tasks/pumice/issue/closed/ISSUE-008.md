# ISSUE-008: the pumice sim has never run the board's DRAM geometry

> **Migrated from `PUMICE-028`** on 2026-09-27, when this area's flat
> `closed.md` was split into one file per item to match the rest of the vault.
> The legacy ID is cited throughout the repo -- RTL comments, DV code, handbook
> notes, commit messages and session memory -- so it is NOT rewritten at those
> call sites; `vault/Tasks/MIGRATION_MAP.md` and this line are how an old
> `PUMICE-028` reference resolves. Body below is verbatim from the flat page.
>
> Lane chosen by reading this item's own Status line and opening, not its title:
> a keyword pass over the 35 items misclassified 14 of them.



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
- And the real one: **write batching starved reads** ([[TASK-007]], fixed in
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

### 2026-09-20 (final): 16/18 at board geometry; the residue is ISSUE-002

Three of the four below were thresholds and are fixed in `4a729f568`:
`read_inflight`'s floor is derived from Little's law scaled by BL_WORDS (and
from the NOMINAL ring depth, not the built one, so the
`PUMICE_RD_RET_DEPTH=8` mutation still fails at BOTH geometries -- verified);
`refresh_bubbles` attributes on refresh-SIZED runs plus a majority-of-cycles
check instead of raw run count; and both paging tests assert against the
measured command-bus ceiling (`BL_WORDS / cmds_per_access`) where a flat 100%
is unreachable, leaving the default-geometry gate untouched.

The fourth was NOT a threshold. The close-page family reaches only ~63% of its
own command-bus ceiling and that is now **[[ISSUE-002]]**, with the tRRD /
tRCD evidence that rules out DRAM timing. The two paging tests fail at board
geometry reporting it by name -- deliberately, rather than being tuned green.

**Default 18/18. Board 16/18.** Remaining for THIS task: resolve or accept
ISSUE-002, then wire board geometry into the regression. `DFI_DATA_WIDTH` 128
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

**NOT caused by [[ISSUE-002]]'s arbiter change.** Verified by running the
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
