# TASK-003: scrub the tests for completeness (stream)
> **Was `TASK-079` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

**Priority:** P2. Blocks the coverage/formal push, not day-to-day work.
**Status:** open 2026-09-04. Raised by Sean: test scrubbing was meant to be
part of the kimi review packets and got dropped along the way. Applies to the
components suites as well as rtl/.

**ID note:** this area draws from the shared `TASK-nnn` sequence, whose
counter lives in [amba/INDEX.md](../../../../../../amba/INDEX.md). It is not a
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
**A concrete find already in hand (2026-09-24, from TASK-002).**
`dv/tests/top/test_stream_top_mon_cfg.py` checked `rb == 0xDEADBEEF` and reported
"the register is unreachable". Nothing in that DUT's closure can drive
0xDEADBEEF -- it appears only as an `LFSR_SEED` in `rtl/amba/shared` and as
`axi4_subtractive_slave`'s READ_FILL, and `read_apb_register` returns
`packet.fields.get('prdata', 0)`, defaulting to 0. So the branch is dead: an
assertion that cannot fire, which is exactly this task's "no test asserts a
condition the bug itself satisfies" clause in its inverse form.

`test_stream_top_regs.py` had the SAME defect and is **already fixed** -- do not
re-do it. It was worse there: the sentinel sat in that file's monitors-absent
`xfail`, which was TASK-002's own regression gate, so the gate could not observe
its fix and stayed XFAIL after it landed. Fixed under TASK-002 by adding
`StreamCoreTB.last_rsp_pslverr` and moving the predicates onto the real APB
error response. `test_stream_top_mon_cfg.py` is **also fixed now** (same change: the predicate
reads `tb.last_rsp_pslverr`, plus a vacuity guard asserting PSLVERR bound).

Stated honestly: that converts a NEVER-fireable check into a CONDITIONALLY
fireable one. mon_cfg builds with `USE_AXI_MONITORS=1`, where the MON window
answers and pslverr stays 0, so the branch did not fire on its passing run (1
passed, 357.52s, 30 MON accesses, 0 bind failures) and is not exercised on every
pass -- it guards an unreachable window, e.g. too narrow an `APB_ADDR_WIDTH`.
What IS proven live there is the bind guard. Both files are done; the wider
17-file scrub this task exists for is untouched.

**A second find (2026-09-24, measured while closing TASK-002).** Every test in
`dv/tests/top/` sets `COCOTB_RESULTS_FILE` in `extra_env`, and **no
`results_*.xml` is ever written** -- zero in `logs/`, zero under the stream
area, and zero repo-wide (439 test files set the variable). The `.log` file is
the only real record.

Scoped honestly: this is INERT CONFIG, not a broken pipeline. Both consumers
handle absence deliberately -- `bin/aggregate_test_results.py:648` prints "No
XML results found" and names three alternatives (`--run`, `--scan-dir`,
`--list`), and `bin/cov_utils/functional_coverage_tracker.py:110` takes its
directory as a parameter and returns `{}` when empty. So nothing is silently
losing data; 439 files just carry a setting that does nothing. Worth settling
whether the variable is inert with this cocotb-test version and should be
dropped, or should work and something discards it -- a suite should not
configure an artifact it never produces.

**A third find (2026-09-24): `logs/` hides stale evidence.** The per-test log
name carries the xdist worker id, which is reassigned between runs, so
`dv/tests/top/logs/` accumulates `test_*_gw0..gw7.log` from earlier runs at
wildly different sizes (75 KB next to 192 KB). Grepping "the log" for a test can
therefore read a PREVIOUS run's file and draw a confident conclusion from it. A
re-run also overwrites the log of the run it replaces, so a failure's evidence
is gone unless copied aside first. Anyone scrubbing these tests should check the
timestamp inside the log against the run they mean, or clear `logs/` first.

**One checklist item is now DONE, and it is a negative (2026-09-24).** The
"no `run()` call pins `testcase=` to a single cocotb test" item was swept across
all 18 `test_*.py` under `dv/tests/{fub,macro,top}`: **zero cocotb tests are
hidden.** Every `cocotb_test_*` name is dispatched from somewhere.

**Do not re-run this with a naive grep -- it gives a FALSE POSITIVE.** Matching
`testcase="..."` only sees string literals, and three files dispatch through a
VARIABLE, so they look unpinned or under-pinned:

| file | tests | how they dispatch |
|---|---|---|
| `macro/test_stream_core.py` | 6 | 4 literal pins + a helper at :1559/:1566/:1573 |
| `top/test_stream_top_advanced.py` | 6 | all 6 bound at :1033-1083, `testcase=cocotb_testcase` |
| `top/test_stream_top.py` | 3 | 1 literal + `_run_extended(...)` at :819/:826 |

My first pass scored those as "11 hidden tests". They were not hidden; the
regex could not see a variable pin.

The check that actually works is name-reachability, not pin-parsing: for each
`async def cocotb_test_X`, count occurrences of `X` in its own file. Exactly one
occurrence means nothing dispatches it. Two or more means it is reached, however
the wrapper is written:

```sh
for name in $(grep -oE 'async def (cocotb_test_[A-Za-z_0-9]+)' "$f" | awk '{print $3}'); do
  [ "$(grep -c "\b$name\b" "$f")" -le 1 ] && echo "UNREACHABLE: $name"
done
```

**Second checklist item swept (2026-09-24): "gate/func/full mean something
distinct" -- PARTIAL, not closed, with a finding list.**

Only **2 of 8** stream TBs gate work by `TEST_LEVEL`:

| TB | what it does with the level |
|---|---|
| `sram_controller_tb.py` | `:130` `self.config = self.test_configs[self.TEST_LEVEL]` -> num_beats / num_channels / beats_per_channel |
| `stream_latency_bridge_tb.py` | `:184` `_STREAM_BEATS = {'gate':8,'func':20,'full':64}`, `:189` picks num_beats |

The other six -- `datapath_rd_test_tb`, `datapath_wr_test_tb`,
`descriptor_engine_tb`, `perf_profiler_tb`, `scheduler_tb`, `stream_core_tb` --
read it, validate it, log it, and branch on it nowhere.

**Nine of 18 tests have NO depth scaling** (neither their TB nor their own body
gates work). Level only changes how many *cells* run, or nothing at all:

- `fub/test_descriptor_engine.py` -- and `:219` CLAIMS "TEST_LEVEL gates the depth"
- `fub/test_perf_profiler.py` -- and `:480` claims the same
- `macro/test_datapath_rd_test.py`, `macro/test_datapath_wr_test.py`
- `macro/test_stream_core_mon_classes.py`
- `macro/test_stream_performance_profile.py` -- `:492` only forwards it to `coverage_env`
- `top/test_stream_top_monbus.py`
- `top/test_stream_top_perf.py` -- no `parametrize` at all; `:229` reads `REG_LEVEL` from env
- `top/test_stream_top_mon_gate.py` -- LEGITIMATE: a contract test, now documented as such

Those two CLAIMS are the sharpest find: a documented contract the code does not
honour reads as working plumbing to the next person.

**A separate, isolated defect: `fub/test_scheduler.py:717` sets
`'TEST_LEVEL': 'basic'`.** `basic` is not a level -- `scheduler_tb.py:103` and
the shared contract `bin/TBClasses/shared/test_levels.py:67` both say
`('gate','func','full')` -- so the TB warns and falls back to `gate`, pinning
that cell to gate depth whatever `REG_LEVEL` says. It is the ONLY hardcode of
its kind (1 occurrence; 11 files use `'TEST_LEVEL': test_level`). The fix is two
parts, because `test_level` is not in scope there: `:670`
`def test_scheduler_extended(request)` never took it. Add it to the signature
(the area conftest provides `test_level` as a FIXTURE, so no `parametrize` is
needed) and replace the literal. Not applied here -- it needs a scheduler run to
verify.

**Three healthy patterns, for contrast:** TB-gated (`sram_controller`,
`latency_bridge`); body-gated (`regs:197`, `mon_cfg:262/:277`,
`scheduler:315`); collection-breadth (`stream_core:310`, `stream_top:173`
expand the parameter grid via `_params_for_level`). `test_stream_latency_bridge.py`
does BOTH halves and documents the split at `:255-256` -- use it as the model.

**Why this item is NOT closed.** Everything above is static. It shows the level
reaches a branch; it cannot show the work differs at runtime. Proving that needs
per-level op counts or runtimes across 18 files x 3 levels.

**Five traps, all of which produced a WRONG answer before being caught -- read
the lines, do not grade them:**
1. `grep 'testcase="..."'` misses variable pins -> scored 11 tests "hidden" that were not.
2. "Does the TB read TEST_LEVEL?" is the wrong question; `stream_core_tb` reads and only logs it.
3. An exclusion regex written as `not in (` / `log.info` misses `not in valid_levels` / `log.warning`, so validate+warn+default lines counted as "branches" -- this INVERTED the TB verdict (reported 6 gate / 2 don't; the truth is 2 / 6).
4. A reference COUNT is not behaviour: `performance_profile` scored 1 ref and is affected; `latency_bridge` scored 2 and is one of the healthiest.
5. `grep -c ... || echo 0` prints "0\n0" when grep exits 1 on zero matches, which then breaks `[ -n ]`/`-eq` tests.

The method that worked: for each `async def cocotb_test_X`, count `X` in its own
file (1 = unreachable); and for levels, dump every `TEST_LEVEL` line in the TB
and the test and read them.

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
