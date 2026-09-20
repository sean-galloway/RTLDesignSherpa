<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# STREAM tasks — open (not started)

## TASK-073: build-mon host walks slvmon_apb with the wrong regmap

**Priority:** Medium — silent wrong-field writes, but build-mon is not going
near the board until it closes timing, so nothing is at risk today.
**Status:** open 2026-08-31. Found from the rtl/amba side while retiring
`dma_slave_monitors` ([[TASK-065]]).

Filed under STREAM because STREAM is the PROJECT. Genesys2 and NexysA7 are
boards -- they are folders that hold a build of a project, and a board does
nothing on its own, so a board directory is not where work is tracked. This is
the STREAM harness (`stream_harness.sv`) and STREAM's host tooling; it happens
to be the Genesys2 build of it. (First filed against the NexysA7 board area,
which was wrong twice over: wrong board, and a board is not an owner.)

`dma_slave_monitors` is gone, but its REGBLOCK outlived it and the APB window
got reassigned underneath the host:

- `Genesys2/stream/rtl/stream_harness.sv:452` routes `slvmon_apb` (@ 0x180000)
  to `u_slave_observer`.
- `axi4_intf_slave_observer.sv:518` instantiates **`obs_regs_top`**.
- `Genesys2/stream/build-mon/host/host_reg_walk.py:22,76-78` still walks that
  window with **`slvmon_device`**'s map, labelled "slvmon_apb
  dma_slave_monitors regblock".

The two maps are unrelated at the same offsets — at `0x024`, obs_regs has
`AXIS_MASK1` and slvmon_regs has `RDSLV_ADDR_RANGE_HIGH`. So a register walk,
or any configuration written through that window, touches the wrong fields and
nothing complains. Wrong-field WRITES are worse than a failure here, because
they look like they worked.

**Agreed fix (stream-genesys session, 2026-08-31): retarget the host at
obs_regs.** The window IS `u_slave_observer/obs_regs_top` now, so
`slvmon_device` is describing a block that is not there.

**Then the cleanup falls out.** On the RTL side `slvmon_regs` is already fully
orphaned: `slvmon_regs_top` is instantiated nowhere and no filelist pulls
`slvmon_regs_top.f`. Once the host points at obs_regs, the whole set —
`slvmon_regs.rdl`, `slvmon_regs.vlt`, the filelist, and the generated
RTL + regmap — is dead and deletes cleanly, the same shape as the four dead
packages removed in `65fa8cf0`. Regenerate only via `bin/peakrdl_generate.py`
([[feedback_peakrdl_generate_bin]]), and generate into the directory the
FILELIST consumes.

**Do not delete the regmap before the host moves** — `host_reg_walk.py`
imports `slvmon_device`, so removing it first breaks a script someone may be
running.

---

## TASK-058: Signal contracts + K-maps for the significant STREAM signals (prove-by-construction)

**Priority:** High
**Status:** [~] In progress (2026-07-29) — the canonical workbook already existed
(`projects/components/dmas/stream/docs/gen_signal_contracts_kmaps.py` ->
`stream_signal_contracts.xlsx`); this session brought it CURRENT: added the
`w_addrgen_start` decider K-map (the TASK-059 fix) + `w_is_ext` contract, fixed
the citation drift my scheduler edit caused (24 `CITES` line refs) so
`verify_citations` is green again, and recorded the explicit placement rule in
the canonical note [[signal-contracts-and-kmaps]] (component `docs/`, one per
block, update-in-place — the gap that nearly caused a duplicate). Remaining: the
run-base-generator flush-on-start (invariant **I10** below) and optional formal
SVA of the stated invariants.

**Update 2026-09-20.** The citation gate was RED again (21 drifts, not caused by
this area's edits -- `scheduler.sv` moved +3 in `db672cd03`, `stream_core.sv`
+26 in `4aeaf3e63`, the monitor files up to +195 in `657d413c1`). Restored to
green; `CITES` is 73 -> 83. Four findings came out of doing it:

1. **The saturation-recovery contract documented the DEFECT as the contract.**
   Every row was stale: `cmd_entry_reserve` 2 -> **4**, `BLOCK_MARGIN` 1 -> **3**,
   `MAX_TRANSACTIONS` `+4`/68 -> `+MON_TRANS_MARGIN`/**72**, thresholds 67 -> 69.
   `axi_monitor_base.sv:679-690` states plainly that reserve=2 (margin 1) is the
   mechanism behind the observer tracking loss (4096 observed vs 3073 tracked) --
   so the workbook was publishing the broken sizing as correct. Corrected.
2. **`stream_core.sv` carried the same stale arithmetic** in comments ("+4
   covers in-flight skid/handshake overlap", "8ch default = 68"), orphaned by
   `baac9a77a` when MON_TRANS_MARGIN became 8. Corrected (comment-only;
   `stream_top_ch8` re-elaborates clean).
3. **"invariant I10" is a dangling reference.** There is no I-numbering anywhere
   in the generator -- invariants are free text in the "Key invariant" column.
   The numbered list the status line above promises was never written. Rather
   than invent an I10 to match the prose, the invariant is now recorded in the
   required form and numbered locally (I1-I3).
4. **86 source labels are structurally uncheckable.** `verify_citations` only
   validates `CITES` quoted snippets; the `f"{SCHED}:924-940"`-style labels are
   line RANGES, so drift in them is undetectable by design. Confirmed real, not
   theoretical: `SCHED:924-940` labels the read-prefetch map, but line 924 is now
   a comment and the expression sits at 927. Not fixed here -- making ranges
   checkable is tooling work ([[TOOLING-KMAP]] step 5), which [[STREAM-KMAP]] is
   already blocked on.

**Run-base generator: documented, deliberately NOT fixed in RTL.** The hazard is
confirmed and now bounded rather than vague: `u_rd_addr_gen`/`u_wr_addr_gen` take
`.rst_n(rst_n)` (SCHED:1029, :1051) -- the BLOCK reset -- so `r_channel_reset_active`
never reaches them (I1); `start` re-arms only the walker and never clears
`i_addr_fifo` (ADDRGEN:152) (I2); depth is 4 per direction (I3). So a channel
reset mid-generation strands up to **4 stale bases per direction**, and the next
descriptor generates behind them. Landed as a three-part CONTRACT TABLE (terms ->
invariants -> decision table) on the "K-maps scheduler" sheet. The decision table
has NO illegal row: all eight combinations are reachable, so nothing structurally
prevents the case -- it is bounded, not excluded.

RTL was left alone on purpose. The task's own text calls this "a good candidate
for the signal-contract treatment", the earlier `gaxi_drop_fifo_sync` `drop_all`
attempt regressed working cases and was reverted, and that attempt exists in no
branch, reflog or stash -- so it cannot be inspected and re-attempting it blind
would just reproduce the regression. Recorded hypothesis for whoever picks it up:
`gaxi_drop_fifo_sync` blocks normal read/write for the duration of a drop, which
is the likely "flush/read-timing interaction". Note the block is shared with
RAPIDS since `4aeaf3e63`, so an RTL flush has two consumers.

Also worth knowing: **no table in the workbook used the 2026-08-28 required form
until this one.** The handbook calls term-list -> invariants -> decision-table the
governing requirement; the existing sheets are all the older shape. Converting
them is [[STREAM-KMAP]] scope.

**Remaining:** only the explicitly-optional formal SVA of the stated invariants.
Everything the status line above listed as outstanding is now either done or
consciously deferred with a reason, so High priority may no longer be right.

**Goal:** Maintain explicit **signal contracts** and **Karnaugh maps** for the
significant control/handshake signals in STREAM — **especially in the read and
write engines** (`axi_read_engine.sv`, `axi_write_engine.sv`) and the scheduler /
descriptor-engine / SRAM-controller handshakes — so the design is provably
correct **by construction** rather than only by directed test.

**Why:** STREAM has already produced several *interaction* bugs that a per-signal
contract would have forbidden up front, not caught after the fact — the
WLAST/drain lost-beat deadlock, the SRAM drain double-count deadlock, and now
the extended chained-transpose corruption (TASK-059 / known_issues). Each was a
cross-block pipeline hazard: a signal asserted (or sampled) one cycle off, or a
shared config register aliased across descriptors. A written contract per signal
(producer, consumer, valid window, mutual-exclusion / one-hot invariants,
back-to-back and reset behaviour) plus a K-map for the combinational deciders
turns these into things that are wrong *on paper* before they ship.

**Scope (significant signals — at least):**
- Engine handshakes: `m_axi_*valid/ready`, `*last`, the SRAM `drain`/`valid`
  pair, per-channel `grant`/`req`, `w_active`/registered-valid gating.
- Scheduler FSM enters/exits and the write-completion timeout.
- Descriptor-engine prefetch + extended `chunk1` fetch (`w_want_ext`,
  `g_ext_fifo`) and the `stream_run_addr_gen` config-latch enables.
- Address generation stride/index/wrap deciders (K-map the mode selection:
  burst vs per-beat, wrap on/off).

**Deliverable:** a contract note per significant signal (table: producer /
consumers / valid window / invariants / reset) and K-maps for the combinational
deciders, landed under the STREAM docs tree (HAS/MAS or a dedicated
`signal_contracts/` area) and indexed. Cross-link each contract to the RTL line
and to any known_issue it would have prevented.

**Related follow-up (from TASK-059's fix):** the run-base generator
(`stream_run_addr_gen`) can still retain queued bases if an extended descriptor
is aborted mid-generation by channel reset (channel reset does not reach that
block). A flush-on-start (`gaxi_drop_fifo_sync` `drop_all`) would close it; a
first attempt regressed the working cases on a flush/read-timing interaction and
was reverted. Low-severity latent robustness item — a good candidate for the
signal-contract treatment.

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
