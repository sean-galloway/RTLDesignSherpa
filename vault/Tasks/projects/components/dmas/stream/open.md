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

## TASK-083 — nothing gates RDL against its generated artifacts
**Status:** open 2026-09-23  **Priority:** Medium

Found while moving the perf registers into the RDL ([[TASK-084]] is the other
half of that session's residue). Editing `stream_regs.rdl` without running
`bin/peakrdl_generate.py` leaves the tree regen-dirty and NOTHING catches it:
the regblock RTL, both regmaps and the docs simply disagree with the `.rdl`,
and every test still passes because they all read the stale generated copies.

I did exactly this during the change and carried a 317-line divergence for
some time before an explicit regen-and-diff surfaced it. The pre-commit hook
runs 11 checks; none of them mention `regmap`, `peakrdl` or `rdl`:

```
declaration order · doc instantiation examples · staged .sv parse ·
port consumers · markdown links · filelist contract   (+ 6 more)
```

The check is cheap and already written as a one-off: regenerate to a TEMP
directory with an explicit `-o`, diff against the committed artifacts, fail on
any difference. That is the same regen-and-diff audit
[[generated-rtl-discipline]] prescribes, just wired to the hook.

Acceptance: a staged `.rdl` change with un-regenerated artifacts is REJECTED,
and the check proves it ran rather than proving it was quiet (a generator that
writes nothing also produces no diff -- the failure mode CRITICAL RULE #0 and
the `regen_bridges.sh` scar both warn about).

## TASK-084 — TB address->name lookup ignores the MON block offset
**Status:** open 2026-09-23  **Priority:** Low

`stream_regs.rdl:758` places the monitor regfile at an offset:

```
stream_mon_regs MON @ 0x1000;
```

so the mon block's raw `0x000-0x268` land at `0x1000+`. The TB's reverse
address-to-name lookup does not apply that offset, so every monitor register
prints as `UNKNOWN_0x11xx` in the APB read log even though the name is fully
resolvable from the regmap. From the baseline regression log:

```
APB READ:  UNKNOWN_0x11E8 (0x11E8) = 0x00000000
APB READ:  UNKNOWN_0x110C (0x110C) = 0x0000FFFF
```

108 registers are affected. This is cosmetic -- the reads themselves are
correct and the walk's pass/fail is unaffected -- but it defeats
[[registers-by-name]] exactly where a human is reading the log to
debug a monitor failure, which is when the name matters most.

Fix is in the lookup builder: walk child blocks with their instance offset
applied rather than flattening on raw child addresses.

## TASK-087 — sv2v regen fails on $display/$time inside a loop (2 of the 5 known cases)
**Status:** open 2026-09-23  **Priority:** Medium

`formal/FORMAL_TODO.md` lists five "Regen FAILED" entries and attributes them to an
"sv2v internal error in Convert/Package.hs -- package conversion bug or an RTL
construct sv2v v0.0.13 cannot handle". For two of them the construct is now
identified:

```
stream_core_flat.v:7007: ERROR: Don't know how to detect sign and width
                                for AST_AUTOWIRE node!
  preceded by: Identifier `\sv2v_autoblock_12.$for_loop$64[0].$time'
               is implicitly declared
```

The site is a debug print inside a `for` loop in `axi_write_engine.sv:914-930`:

```systemverilog
for (int i = 0; i < NC; i++)
    if (...) begin
        r_stuck_counter[i] <= r_stuck_counter[i] + 1;
        if (r_stuck_counter[i] == 1024)
            $display("[%0t] WR ENGINE STUCK ch%0d: ...", $time, i, ...);
    end
```

sv2v lowers the loop into `sv2v_autoblock_12` and leaves `$time` as an
implicitly-declared node yosys cannot size. The prints are UNGUARDED -- no
`ifdef`, no `translate_off`.

**Scope, measured -- this explains 2 of the 5, not all:**

| entry | $display | verdict |
|---|---|---|
| `stream/axi_write_engine` | 6 | CAUSE CONFIRMED |
| `stream/stream_core` | 0 own | explained: its flat includes axi_write_engine |
| `stream/axi_read_engine` | 0 | NOT explained -- separate diagnosis |
| `stream/monbus_axil_group` | 0 | NOT explained -- separate diagnosis |
| `converters/axi4_to_apb4_shim` | 0 | different cause (DEPS drift, per `formal/FORMAL_TODO.md`) |

Fix options: guard the debug prints behind an ifdef, or strip them in the
sv2v prep step the way the stream_core Makefile already seds `monitor_pkg`.
The second keeps the prints available in simulation.

Acceptance: `stream/axi_write_engine` and `stream/stream_core` flats
regenerate AND parse in yosys. The other two entries stay open under their
own diagnosis.

**Related staleness found the same day, worth folding in:** the flats are not
the only stale layer -- `formal/stream/stream_core/.sv2v_prep/*.sv` (tracked
sed output) was 376 insertions behind its sources, including the whole
TASK-073 monitor fix. Neither layer has a content check, which is what
[[generated-rtl-discipline]] prescribes. See also the `check-flat` target
`formal/FORMAL_TODO.md` already proposes.
