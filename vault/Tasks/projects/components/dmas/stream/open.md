<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# STREAM tasks — open (not started)

## STREAM-KMAP — finish the STREAM workbook so its maps prove the decisions
**Status:** open 2026-08-06  **Blocked on:** [[TOOLING-KMAP]] items 1-4

`projects/components/dmas/stream/docs/gen_signal_contracts_kmaps.py` is the
better of the two existing workbooks and still meets only two of the six
criteria in [[signal-contracts-and-kmaps]]: Gray-ordered, computed from cited
RTL -- but no axis equations, no sufficiency argument, no don't-cares, no
implicants. Its first pass found six defects the test suite had not, which is
the argument for FINISHING it, not for calling it done.

It already has per-block builders (`build_rd_engine_kmaps`,
`build_wr_engine_kmaps`, `build_scheduler_kmaps`, `build_desc_engine_kmaps`),
so the work is deepening each rather than starting over.

Priority targets, each with a silicon bug or known_issues entry behind it:

1. **Monitor cfg -> packet-class qualification (`stream_core`). DO THIS FIRST.**
   `cfg_compl_enable` was aliased to `int_cfg_*_mon_enable` and
   `cfg_threshold_enable` to `*_mon_perf_enable`. An axis table carrying each
   axis's DEFINING EXPRESSION would have shown two axes resolving to the same
   signal, immediately. Nothing in the test suite could see it (the FUB tests
   drive the ports directly; the board only sees packets). Small map, live
   failure, and the clearest possible demonstration of criterion 3.
2. **`axi_write_engine` drain strobe / WLAST.** The lost-WLAST deadlock was the
   SRAM drain decoupled from `m_axi_wvalid`; fixed by gating
   `axi_wr_sram_drain` on `m_axi_wvalid && m_axi_wready`. A map of the drain
   strobe with a stated sufficiency argument is the direct check, and
   `wr_w=burst_pause` remains the regression sentinel.
3. **`descriptor_engine` prefetch + fifo_threshold.** `cfg_prefetch_enable` and
   the fifo-threshold input were DEAD -- wired nowhere. A map listing axis
   equations with citations would have shown an axis that no RTL drives.
4. **`scheduler` timeout/error latch and clear.** A sticky CH_ERROR stranding
   the desc_fifo is exactly a latch/clear adjacency question. Note this is the
   SCHEDULER timeout (`SCHED_TIMEOUT_CYCLES`), NOT the monitor timeout -- two
   different mechanisms sharing a word, which is how the monitor's went
   untested at this level for so long.
5. **`stream_alloc_ctrl` / `stream_drain_ctrl` space accounting.** Credit-style
   arithmetic with unreachable regions that are only unreachable because of
   ordering guarantees elsewhere -- those guarantees belong in the don't-care
   citations (criterion 5).

Acceptance: every map above states its axis equations with citations, its
`depends_only_on` argument, its don't-cares with the invariant that makes them
unreachable, and a derived-minimal-vs-RTL verdict.

## STREAM-MONREGS — gate the monitor regfile on a parameter (present + decoded)
**Status:** open 2026-08-06

`stream_regs.rdl` includes and instantiates the monitor regfile unconditionally:

```
line  22:  `include "stream_mon_regs.rdl"
line 758:  stream_mon_regs MON @ 0x1000;
```

There is no parameter deciding whether that block is PRESENT or DECODED, while
`USE_AXI_MONITORS` already decides whether the monitors it configures exist.
The two must move together.

**Why it matters more than area.** On a `USE_AXI_MONITORS=0` build the monitor
registers still accept writes and read back the written value -- driving
nothing. A host arms `RDMON_TIMEOUT`, reads it back correctly, and concludes the
monitor is configured. There is no monitor. Read-back success is normally the
strongest evidence a host has that configuration took, and here it is
affirmatively misleading.

This is live: `build-perf` ships `USE_AXI_MONITORS=0` today, with the whole MON
window responding.

**Wanted:**
- A parameter (`USE_MON_REGS`, defaulting to `USE_AXI_MONITORS`) that gates both
  the regfile instantiation and its address decode.
- With it 0, accesses to 0x1000+ should return the bus error / no-response the
  decode already produces for unmapped space -- so "not built" is
  DISTINGUISHABLE from "built and set to zero". Silence is the honest answer.
- RAPIDS already has the hookup-parameter shape for this
  ([[project_rapids_beats_resync]]: monitors relocated to 0x1000 in a separate
  `include`d regfile under one APB slave with a USE_AXI_MONITORS hookup param).
  Follow it rather than inventing a second pattern.

**Test that should exist alongside it:** the monitors-off build must FAIL to
read the MON window. `dv/tests/top/test_stream_top_mon_cfg.py` covers the
monitors-on direction (register field -> cfg port); the negative direction needs
the parameter first.

Found while writing that test: with monitors ON, the MON window at 0x1000+ needs
`APB_ADDR_WIDTH=13`. At the 12-bit default every monitor register returns
0xDEADBEEF, which is indistinguishable from a hookup failure until you read back
-- see [[STREAM-KMAP]] item 1 for the same class of problem in map form.

---

## TASK-079: scrub the tests for completeness (stream)

**Priority:** P2. Blocks the coverage/formal push, not day-to-day work.
**Status:** open 2026-09-04. Raised by Sean: test scrubbing was meant to be
part of the kimi review packets and got dropped along the way. Applies to the
components suites as well as rtl/.

**ID note:** this area draws from the shared `TASK-nnn` sequence, whose
counter lives in [amba/INDEX.md](../../../../amba/INDEX.md). It is not a
per-area namespace -- take the number from there and bump it.

**Sequencing.** A FOCUSED pass, run after qc/humanize is finished everywhere
and BEFORE coverage and formal are driven clean.

**Scope:** `projects/components/dmas/stream/dv/tests/` -- 17 test files across fub/macro/top.

**The capability already exists and was simply never run here.**
`bin/review/run_batch.py` has a `testqc` mode alongside `qc` and `humanize`,
with `bin/review/TEST_REVIEWER_BRIEF.md` as its brief and
`bin/review/build_test_review_bundle.py` to build the units.

**Why this is not busywork.** A test that passes because the RTL is broken is
worse than no test. The template is apb5 (2026-09-04): nothing drove
`rsp_ready`, so the response skid filled and never drained, and the TB's
completion check returned True on exactly the state the defect produced. The
suite was green BECAUSE the RTL was broken.

**Area-specific:** stream has already produced two of the repo's clearest
"the test was wrong, not the RTL" cases -- the sram_controller alloc failures
that were the TB sampling `space_free` before its register pipeline settled,
and the scheduler write-timeout that a TB signal poke could not reach because
the value is register-driven on the top. Both are the inverse of the apb5 case
and both belong in the scrub's findings taxonomy.
**What "complete" has to mean, at minimum:**

- Every `test_*.py` actually exercises the DUT it names.
- No test asserts a condition the bug itself satisfies.
- Inputs the DUT needs are actually driven.
- gate/func/full levels mean something distinct, not three names for one run.
- No `run()` call pins `testcase=` to a single cocotb test. A pinned
  `testcase=` silently hides every OTHER `@cocotb.test` in that module, so a
  test can sit in the file for months and never execute. `test_apb5_master.py`
  did exactly this (2026-09-04) -- a witness added beside the basic test ran
  zero times until the pin was widened. A comma-separated list is the fix when
  a pin is genuinely wanted.
- A fix landed with a test has a mutation check recorded: the test was seen
  RED against the unfixed RTL. Without that the test is decoration.

**Related:** [[TASK-078]], [[COMMON-025]], [[MATH-010]], [[CDC-001]] are the
same task in the rtl/ areas.

---

## TASK-080: STREAM formal proofs read a hand-copied gaxi_fifo_sync, not the RTL

**Priority:** Medium. Nothing fails, which is the problem: a proof about a
copy says nothing about the module that ships.

**Status:** open 2026-09-11, found while retiring the same defect class from
the repo-root `formal/` areas (amba/cdc/common), where thirty tasks proved
hand-copied forks. This area was out of that job's scope.

- `formal/stream/stream_latency_bridge/gaxi_fifo_sync_formal.sv` is a
  hand-copied `gaxi_fifo_sync`: 155 lines against the real module's
  250, with 133 lines differing. It is read by:
  `stream_latency_bridge`.
- `formal/stream/_includes/monitor_pkg_formal.sv` is a package stub that
  no task reads -- an orphan.

Why forks exist, and why they are unnecessary: yosys's own SystemVerilog
frontend cannot read these modules (package-typed ports, casts, unpacked
array ports), so someone copied and simplified them. sv2v can read the real
RTL, and every one of the thirty repo-root forks turned out to be
convertible. See `vault/handbook/dv/formal.md` ("PROVING A FORK IS WORSE THAN
NO PROOF") for the method and the traps: judge a `[files]` entry by its
SOURCE, not its local name, and expect stale properties to surface once the
real module is read -- two of the repo-root conversions exposed properties
written for the fork, and one exposed a real AXI protocol bug (amba
TASK-094).

**Done when:** no `formal/stream` task reads a `*_formal.sv` copy of an rtl/
module, each converted task proves against the real RTL, and the two fork
files are deleted.

## TASK-090 — `.sv2v_prep` holds TRACKED generated files that `make clean` deletes
**Status:** open 2026-09-24  **Priority:** Medium

Found while fixing [[TASK-087]]. `formal/stream/stream_core/.sv2v_prep/` carries
**7 tracked `.sv` files** -- sed-preprocessed copies of the monitor sources --
and the same Makefile's clean target is:

```make
clean:
	rm -rf *_flat.v *_prove *_cover $(TMPDIR)     # TMPDIR := .sv2v_prep
```

So `make clean` deletes tracked files, and the next build regenerates them from
whatever the sources say then. Nothing compares the regenerated copy against the
committed one. That is the mechanism behind the drift TASK-087 recorded: the
prep layer was **376 insertions behind its sources**, including the whole
TASK-073 monitor fix. `.sv2v_prep` is not in any `.gitignore` (`git check-ignore`
returns nothing), so the files are tracked by default rather than by decision.

**This is now half-and-half, deliberately.** TASK-087's fix adds a prep step to
four Makefiles and leaves those NEW outputs UNTRACKED, because adding more
tracked generated artifacts would deepen exactly this problem. The result is one
directory with 7 tracked files and 1 untracked one. That is a knowingly
inconsistent state, recorded here rather than silently left for the next
session to trip over.

**Decide one way:**
- [ ] Untrack all of `.sv2v_prep/` and add it to `.gitignore` -- it is pure
      derived output, regenerated by a deterministic sed from tracked sources.
      Preferred: nothing is lost, and `make clean` stops being destructive.
- [ ] Or keep them tracked and remove `$(TMPDIR)` from `clean`, adding a
      content-diff `check-flat`-style target so drift is caught. This is the
      heavier option and still leaves generated files in git.

Either way the flats themselves (`*_flat.v`, tracked, 332 KB for stream_core)
have the same no-content-check gap, which is what the `check-flat` target in
`formal/FORMAL_TODO.md` proposes. See [[generated-rtl-discipline]].

## TASK-091 — stream_core's formal dependency list has rotted behind the monitor rework
**Status:** open 2026-09-24  **Priority:** Medium

Found while fixing [[TASK-087]], which got `stream_core_flat.v` regenerating and
PARSING again. Proving it is a further step, and it walks a chain of modules the
Makefile never learned about:

| missing module | referenced in | fixed here? |
|---|---|---|
| `stream_run_addr_gen` | `scheduler` (`g_addrgen.u_wr_addr_gen`) | YES -- moved to `misc/rtl` by 4aeaf3e63 |
| `dma_address_gen` | `stream_run_addr_gen` (`u_addr_gen`) | YES |
| `monitor_trans_cam` | `axi_monitor_trans_mgr` (`g_cam_bank[0].u_cam`) | YES -- 17 other formal Makefiles already list it |
| `axi_monitor_reporter_threshold` | `axi_monitor_reporter` (`g_thresh.u_thresh`) | **NO -- stopped here** |

Three were added; the fourth is where I stopped, because this is clearly not a
handful of omissions but the `axi_monitor_reporter_*` split and monitor rework
never propagating into this Makefile. `formal/FORMAL_TODO.md` already records
that rework as the reason 10 amba flats are 80-220 lines stale.

Current state: `make stream_core_flat.v` succeeds and the flat PARSES clean in
yosys (0 AST_AUTOWIRE). `make prove` fails at elaboration with
`DONE (ERROR, rc=16)` on `axi_monitor_reporter_threshold`.

**Do:**
- [ ] Walk the chain to the end rather than one module at a time -- the flat
      filelist for stream_core (`bin/filelists.toml`) already knows the real
      closure; prefer generating DEPS from it over hand-listing.
      See [[filelists]].
- [ ] Then re-prove and record a REAL verdict.

## TASK-092 — datapath_wr_test proof FAILS once it can finally elaborate
**Status:** open 2026-09-24  **Priority:** Medium

Uncovered by [[TASK-087]] + the dependency fixes in [[TASK-091]]. This unit
could not build at all (missing `stream_run_addr_gen` -> `dma_address_gen`);
with those added it elaborates, and the proof returns a genuine counterexample:

```
failed assertion formal_datapath_wr_test.ap_desc1_ready_state
  at formal_datapath_wr_test.sv:255.13-259.14   step 4
counterexample trace: datapath_wr_test_prove/engine_0/trace.vcd
DONE (FAIL, rc=2)
```

**This is a REAL result, not a build artifact.** `formal/FORMAL_TODO.md` says so
itself for this exact case: "If the proof fails after regeneration, that is a
REAL result about the current design."

**Why it went unnoticed:** the committed `datapath_wr_test_flat.v` was last
written by a1760aaf6 (2026-07-17) -- the SAME commit that added the
`stream_run_addr_gen` instantiation to `scheduler.sv`. So the flat has been
stale since the moment the dependency appeared, and `formal/FORMAL_TODO.md`
still lists this unit as `prove_boundary+prove_low8 PASS`. That PASS is a green
recorded against a two-month-old artifact -- [[running-regressions]] in
practice. The same caveat applies to `axi_write_engine_beats`, whose flat was
also stale (Aug 9) though it re-proves PASS.

**Do:**
- [ ] Read the counterexample and decide: RTL defect, or a harness assumption
      that went stale with the descriptor interface.
- [ ] Do NOT weaken the property to make it pass without that decision.
