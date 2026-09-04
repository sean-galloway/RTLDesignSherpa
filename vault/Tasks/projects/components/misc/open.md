<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# misc — Open (accepted, ready to start)

### MISC-001: all RDL lives in the rdl directory

**Priority:** P3. Hygiene, but it is the kind that silently rots -- a stray
source has no obvious home, so the next person adds theirs beside it.
**Status:** open 2026-09-04. Raised by Sean: **all RDL must be in the `rdl`
directory.**

**The violation, exactly.** `projects/components/misc/` already has an `rdl/`
directory holding `dma_address_gen.rdl`, so the convention is established
here. Three more sit in `rtl/`:

| File | Current | Belongs |
|---|---|---|
| `obs_regs.rdl` | `misc/rtl/` | `misc/rdl/` |
| `slvmon_regs.rdl` | `misc/rtl/` | `misc/rdl/` |
| `tally_regs.rdl` | `misc/rtl/` | `misc/rdl/` |

**This is not a `git mv`.** Eleven files reference them by path, and they span
two areas -- moving the sources without the references breaks generation and
two FPGA builds:

- `obs_regs.rdl` — `misc/rtl/regs/generated/obs_regs_top_regmap.py`,
  `misc/dv/tests/fub/test_axi4_intf_observer.py`,
  `misc/dv/tbclasses/axi4_intf_observer_tb.py`,
  `Genesys2/stream/dv/tbclasses/stream_harness_tb.py`
- `slvmon_regs.rdl` — `misc/rtl/regs/generated/slvmon_regs_top_regmap.py`,
  `misc/rtl/filelists/slvmon_regs_top.f`
- `tally_regs.rdl` — `misc/rtl/regs/generated/tally_regs_top_regmap.py`,
  `misc/rtl/filelists/monbus_tally_axil.f`,
  `Genesys2/stream/rtl/filelists/monbus_tally_axil.f`,
  `Genesys2/stream/build-obs/host/host_reg_walk.py`,
  `Genesys2/stream/build-obs/dv/tests/test_stream_mon.py`

**Method.** Move the three, update all eleven references, then REGENERATE
rather than hand-edit the generated outputs -- the `*_top_regmap.py` files are
PeakRDL output and must come from `bin/peakrdl_generate.py`, which emits RTL,
docs and regmap in lockstep (a raw `peakrdl regblock` desyncs the regmap). Run
the misc tests and the Genesys2 stream build-obs host walk afterwards; both
consume `tally_regs` by name.

**Wider picture, not this task's scope.** The repo has 28 `.rdl` files and
misc is not the only area with them under `rtl/`: retro_legacy_blocks keeps
nine under `rtl/<block>/peakrdl/`, rapids four under `rtl/macro_beats/`,
stream two under `rtl/macro/`, pumice one under `rtl/macro/`. If the rule is
repo-wide rather than misc-local, that is a much larger task and should be
filed per area -- this block deliberately covers only misc, which is what was
asked for.

### MISC-002: scrub the tests for completeness (misc)

**Priority:** P2. Blocks the coverage/formal push, not day-to-day work.
**Status:** open 2026-09-04. The misc slice of the repo-wide test scrub that
was meant to ride along with the kimi review packets and got dropped.

**Sequencing.** A FOCUSED pass, after qc/humanize is finished everywhere and
BEFORE coverage and formal are driven clean.

**Scope:** `projects/components/misc/dv/tests/` -- 4 test files covering the
AXI4 interface observers and the tally/slave-monitor register blocks.

**The capability already exists and was simply never run here.**
`bin/review/run_batch.py` has a `testqc` mode alongside `qc` and `humanize`,
with `bin/review/TEST_REVIEWER_BRIEF.md` as its brief and
`bin/review/build_test_review_bundle.py` to build the units.

**Area-specific:** the observers are measurement-only blocks, which is the
hardest thing to test honestly -- a monitor that reports nothing looks
identical to a bus with nothing on it. Check that each test proves the
observer SAW something, not merely that it did not fault. The area also
carries the `axi4_intf_observer` work that a stream channel-3 hang was traced
to (the observer's `block_ready` replaying 49 ARs as 367), so its tests have a
history of passing while the block misbehaved.

**What "complete" has to mean, at minimum:**

- Every `test_*.py` actually exercises the DUT it names.
- No test asserts a condition the bug itself satisfies.
- Inputs the DUT needs are actually driven.
- gate/func/full levels mean something distinct, not three names for one run.
- No `run()` call pins `testcase=` to a single cocotb test. A pinned
  `testcase=` silently hides every OTHER `@cocotb.test` in that module.
  `test_apb5_master.py` did exactly this (2026-09-04).
- A fix landed with a test has a mutation check recorded: the test was seen
  RED against the unfixed RTL.

**Related:** [[TASK-078]], [[COMMON-025]], [[MATH-010]], [[CDC-001]],
[[BRIDGE-007]], [[PUMICE-018]], [[CONV-008]], [[APBX-007]], [[RLB-006]],
[[TASK-079]], [[TASK-080]] are the same task in the other areas.
