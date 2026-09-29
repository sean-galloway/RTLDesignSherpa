# TASK-003: scrub the tests for completeness (bridge)

> Migrated 2026-09-27 from `vault/Tasks/bridge/closed.md` as **BRIDGE-007** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.

**Priority:** P2. Blocks the coverage/formal push, not day-to-day work.
**Status:** CLOSED 2026-09-10. The testqc round ran end to end: twelve units,
nine clean, one seed finding, two CONFIRMED and both fixed in the shared test
template (a boundary probe that accepted any exception as the expected
SLVERR; a write-path error raise that was dead for AXI-Lite masters). Against
the checklist below: every generated test drives its DUT through the BFMs;
the two assertions a bug could satisfy are gone and replaced by ones that name
the response code; gate/func/full are measured distinct (48 of 48 tests level-
compliant, 60/113/171-style grids and per-cell depths confirmed in the logs);
the generated wrappers pin one cocotb test each by design and every cocotb
test in every module has a wrapper; and every fix landed this week carries a
recorded mutation check, including the two A5-3b ones. Two more findings of
exactly this task's kind surfaced while signing off A5-3b and were fixed the
same day: an AtomicStore expectation that had encoded the BFM's old plain-
write behaviour, and a concurrency phase whose ID reuse violated the rule it
was meant to exercise. Bridge FULL regression 249/249 on 2026-09-10.
Originally: open 2026-09-04. Raised by Sean: test scrubbing was meant to be
part of the kimi review packets and got dropped along the way. Applies to the
components suites as well as rtl/.

**Sequencing.** A FOCUSED pass, run after qc/humanize is finished everywhere
and BEFORE coverage and formal are driven clean. Doing it after coverage would
mean chasing numbers produced by tests nobody has audited.

**Scope:** `projects/components/fabric-gen-ip/bridge/dv/tests/` -- 39 test files, the largest components suite, and almost all of it is generated.

**The capability already exists and was simply never run here.**
`bin/review/run_batch.py` has a `testqc` mode alongside `qc` and `humanize`,
with `bin/review/TEST_REVIEWER_BRIEF.md` as its brief and
`bin/review/build_test_review_bundle.py` to build the units. The brief audits
test collateral against the project's test contract and treats the
CocoTBFramework as reviewed ground truth rather than an audit target. Start
there rather than inventing a method.

**Why this is not busywork.** A test that passes because the RTL is broken is
worse than no test, and the repo has already produced them. The template is
apb5 (2026-09-04): nothing drove `rsp_ready`, so the response skid filled and
never drained, and the TB's completion check returned True on exactly the
state the defect produced. The suite was green BECAUSE the RTL was broken. The
witness added with the fix counted 59 protocol violations across 70 bus
completions on the unfixed design that no prior test had noticed.
**Area-specific:** the suite is generated, so a defect in the test generator
is replicated across every configuration at once. Audit the generator's test
template first; a finding there is worth 39 findings in the output. Note also
that generated tests must be regenerated, never hand-edited (CRITICAL RULE #0).

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

**Audit 2026-09-09, AMBA5 focus (hand audit against the checklist; the
testqc round has still not been run).** Measured on a clean FULL run:
72 passed / 0 failed / 0 reruns, 40 files, 6m08s. 63/63 generator unit
tests, 21 of them AMBA5 validator rules.

*Premise check first.* "Full AMBA5" is not what the tree does, and the
tests match the tree, not the phrase. Support is the interop scope:
AXI5 master and slave ports with native sideband (nsaid/trace/mpam/mecid/
unique/poison) and STORE-class atomics; AtomicLoad/Swap/Compare are
DECERR'd at the master boundary by `axi5_atomic_filter` (A5-3 read-return
routing is still not built); mte/chunking rejected by the validator;
axil5 and apb5 are slave-only. Every AMBA5 fixture is 1x2, single
master, all ports 32-bit.

Findings, in impact order:

1. **Levels: 0 of 40 compliant** (`check_test_levels.py`). The jinja
   template `bridge_test_file.py.j2` never reads REG_LEVEL, never exports
   TEST_LEVEL, and the TBs never read it -- so `run-all-gate`, `-func` and
   `-full` run the identical suite. Both halves of the HARD REQUIREMENT
   are missing, suite-wide, from one template. One fix, 40 files
   (regenerate, never hand-edit).
2. **No SEED anywhere.** No generated test or TB reads SEED or seeds an
   RNG; the only env reads are the boundary-probe mode and the xdist
   worker id. Same template.
3. **One test drives an AXI5 port with the AXI5 BFM**
   (`test_bridge_1x2_rd_axi5_bfm5`: `AXI5MasterRead` + compliance
   checker, 6 reads, read side only). Every other AXI5 fixture is driven
   by the AXI4 BFMs; `AXI5MasterWrite`, `AXI5SlaveRead/Write` and the
   write-side compliance checker (ATOP_*, POISON_PROPAGATION,
   TRACE_CONSISTENCY, NSAID/MPAM/MECID checks all exist in it) are never
   instantiated. The AXI5-only inputs (awatop, awtrace, arnsaid, wpoison
   ...) are left undriven on those fixtures -- Verilator zeros them, which
   is why it works.
4. **Sideband and atomics are hand-poked.** The two `_sideband` tests and
   the `_atomics` test set `dut.cpu_*_axi_awatop/awtrace/wpoison/arnsaid`
   directly beside an AXI4 BFM and sample the far side with a pin
   sampler. They do check values end-to-end (nsaid/trace/unique on AR,
   rtrace on R, wpoison on W, btrace on B; STORE routed with data
   verified in memory, LOAD and SWAP DECERR'd) -- but Compare
   (`0b11xxx1`) is not exercised, and the protocol-level checks the BFM
   would add (ATOP burst-length, atop-vs-response) are absent. This is
   the [[feedback_always_use_axi4_bfms]] rule's AXI5 twin.
5. **APB5 slave driven by the APB4 BFM.** `bridge1x2_rw_apb5_tb` imports
   only `APBMaster/APBSlave`; the framework has `APB5Slave/APB5Monitor`.
   The A5-3 note's "hand-written check against the apb5 slave BFM" does
   not exist in the tree. axil5 is correct (`AXIL5SlaveRead/Write`).
6. **Untested shapes:** AXI5 through arbitration (no multi-master AXI5
   fixture, so sideband muxing in the xbar's b/r return is unexercised);
   AXI5 across a width converter (droppable sideband terminating mid-path
   is only a generation-time warning, never simulated); mte/chunking
   rejection is unit-tested only, which is correct for a rejection.

Clean on the checklist: TB separation (dv/tbclasses, three reset methods
present), sources from `.f` filelists, every `cocotb_test_*` is pinned by
exactly one `run()` (no hidden tests), memory-backed slaves verify DATA
not just routing, boundary probes cover decode edges.

Recommended order: (1)+(2) in the template and regenerate all 40; then
an AXI5-BFM write-side test with the compliance checker on `wr_axi5a`
(atomics incl. Compare) and `wr_axi5n` (poison/trace), and an APB5 BFM
on `rw_apb5`; then a 2x2 AXI5 fixture. Then the testqc round.

**(1)+(2) DONE 2026-09-09 (Sean: "fix levels please").** 41 of 41 compliant;
grid GATE 72 / FUNC 144 / FULL 216 cells; clean runs at every level with 0
reruns (GATE 72/72 5m10s, FUNC 144/144 9m47s, FULL 216/216 9m38s), and the
FULL run's sibling cells prove distinct depth: 4x4 boundary probe 4s / 5s /
40s, arbitration 16 / 32 / 96 transactions, monitor ERR_BP 128 / 256 / 512
reads, BRIDGE-011 40 / 80 / 128 writes, atomics 1 / 2 / 8 rounds. Depth
profile lives in `dv/tbclasses/bridge_levels.py`; the 8-line REG_LEVEL grid
is per wrapper file (the val/common form); SEED is exported per cell and
seeds one RNG per TB. Three things had to be fixed on the way, each worth
more than the levels:

* **The generator could not regenerate its own tests.** BRIDGE-009's
  internal subtractive slave was templated as a real slave (a BFM on
  prefix "subtractive", probes into a 4 GB window at 0x0), so every
  regenerated test failed at TB construction -- which is why nobody had
  regenerated since 1d442e76, and why the tree carried the real arbitration
  test that a43b032dd hand-edited into seven generated files while the
  template still emitted the TODO stub, two hand-written tests inside the
  generated 2x2 file, and a TB method the template lacked. Fixed: test and
  monitor-test generation see external ports only; the template emits the
  real arbitration test and the `set_slave_response_delay` / `txn_id`
  helpers; the 2x2 tracking tests moved to hand-written
  `test_bridge_2x2_rw_tracking.py`. All 36 tests + 36 TB classes are
  regenerated from the template, RTL byte-identical.
* **The bridge conftest stamped REG_LEVEL into `os.environ['TEST_LEVEL']`,
  and cocotb_test lets the environment override `extra_env`** -- so the
  first leveled FULL run executed all 216 cells at full depth while the
  grid reported three levels. Stamp removed here; the same block is in
  twelve other conftests: [[TOOL-016]].
* **`check_test_levels.py` never followed Pattern B imports**, so a project
  TB that read TEST_LEVEL and one that never did both printed
  `depth:never-read`. Fixed, plus a WARNING for the conftest stamp. Under
  the fixed tool: stream fub 2 of 7, apbx-xbar 0 of 6, misc 0 of 4, rlb 0
  of 9 -- unmeasured before, real now.

Also fixed: the gate monitor stress count sat exactly at the 64-entry err
FIFO depth, so the ERR_BP saturation assertion was a race against the drain
pump (11 variants won, mix_d peaked at 58); gate uses 2x depth.

**(3)-(6) DONE 2026-09-09 (Sean: "beef up the tests").** Template-level, so
every fixture got it, verified FULL 237/237 (45 files, 0 reruns):

* **(3) AXI5 ports are driven by the AXI5 BFMs.** The TB template picks the
  BFM family per port protocol -- `axi5` -> `AXI5Master/Slave{Read,Write}`
  (every AMBA5 sideband field is optional in the framework's binding rule,
  so one BFM fits any feature subset), `apb5` -> `APB5Slave` at the
  generator's 1-bit USER widths -- and arms an `AXI5ComplianceChecker` on
  every AXI5 master port; every generated test calls `tb.assert_compliance()`
  before PASSED. 14 TBs now drive AXI5 BFMs, 2 drive APB5.
* **(4) No pin pokes.** The sideband and atomics tests drive
  nsaid/trace/unique/poison/atop as BFM transaction arguments and read the
  echoed trace from the BFM result; the slave-side samplers stay as
  observation. Compare (`0b110001`) added: store forwards, load/swap/compare
  answered DECERR by the filter, asserted as the EXPECTED response.
* **(5) APB5 slave on the APB5 BFM** (template).
* **(6) Two new fixtures**, generated with their own tests plus a
  hand-written sideband test each: `bridge_2x2_axi5` (two AXI5 masters with
  distinct NSAIDs contending for an AXI5 slave -- every slave-side AW/AR
  NSAID must belong to its issuing master and the counts must match; trace
  echoes from the AXI5 slave, returns 0 from the AXI4 one) and
  `bridge_1x2_rd_axi5w` (32b AXI5 master into a 64b AXI4 slave -- data
  round-trips through the converter, trace returns 0; native path echoes).

Two framework findings on the way, both fixed in RDS-DV: the out-of-range
disagreement ([[BRIDGE-008]], closed) and `write_transaction` returning
`response=None` on an error B (19f866b) -- the generated `master_write` now
raises on an error response, which is how the atomics test caught that a
DECERR used to pass through the helper silently.

**The compliance checker was vacuous, and had been since 2026-08-09.**
Arming it in every TB is what exposed it: the first summary line printed
empty statistics. `AXI5ComplianceChecker.setup_monitors` built its channel
monitors without a `protocol_type`, so every AMBA5 sideband field was
REQUIRED; on any real port the AR monitor failed to bind, the failure was
caught and logged as a WARNING, the checker set `enabled=False`, and
`get_compliance_report()` returned `compliance_checking: disabled` -- which
the bfm5 sign-off test had been reading as "zero violations" for a month.
The AXI4 checker had the identical defect. Fixed in RDS-DV (9505cce,
6b35cc9): monitors take the BFMs' per-channel `protocol_type`, a setup
failure raises, and a structural unit test pins both. The generated
`assert_compliance()` now refuses a checker that is not `enabled` or that
performed zero checks. Measured after the fix on one gate cell: checker
active on AR/R, 294 checks, 2 AR transactions -- a verdict with something
behind it.

**Every AXI master port now carries a protocol checker, AXI4 as well as
AXI5 (2026-09-10).** The TB template arms `AXI4ComplianceChecker` on every
`axi4` master port alongside the AXI5 one, and `assert_compliance()` requires
the report to be `enabled`, `armed`, and to have performed a non-zero number
of checks before it will accept "zero violations".

Arming it found a second blind-checker defect, one layer below the one found
yesterday: `_has_channel_signals` concatenated the port prefix naively, so a
port written `cpu_m_axi` rather than `cpu_rd_axi_` resolved NO channels --
no monitors, `monitors_active` False, both loops returning immediately -- and
the report still said `enabled` with zero violations. `bridge_2x2_rw`
reported "0 violation(s) in 0 checks" and the `checks > 0` assertion caught
it. Fixed in RDS-DV (`09ef5dc`): the prefix is resolved against both
spellings, a checker that binds nothing logs a WARNING, and the report now
carries `armed` and `channels` so a caller can refuse a verdict with nothing
behind it. With that, `bridge_2x2_rw` checks both masters at 1790-4505 checks
per cell, zero violations.

**The testqc round is RUNNING (2026-09-10) -- the first on any
projects/components area.** Getting there needed three fixes to the review
pipeline, which is why no such round had ever run:

* `build_test_review_bundle.py` only looked under `val/<area>`. It takes a
  path now, so a Pattern B area can be bundled at all.
* It resolved `TBClasses.*` and `CocoTBFramework.*` imports but not
  `projects.components.<c>.dv.tbclasses.*` -- so a Pattern B bundle would
  have shipped its tests with NO testbenches and the reviewer could not have
  seen what the tests drive.
* `RTL_IFACES.sv` came out EMPTY: the bundler re-parsed the `.f` itself,
  skipping any line starting with `-` or `+` and never expanding
  `$REPO_ROOT`, which is 707 `-f` lines and 311 `$REPO_ROOT` lines across the
  bridge's filelists. It uses the repo's own `get_sources_from_filelist` now.
* `FRAMEWORK.py` is reduced to its API surface, which is what its GOLDEN
  banner says it is for. Full bodies were 364 KB of a 490 KB unit and pushed
  every single test over the size limit.

**Scope: 12 units, not 45.** The seven hand-written tests plus five
representative generated ones (simple rd, multi-master rw, mixed-protocol,
monitor stress, apb5). This task's own text says why: the suite is generated,
so "audit the generator's test template first; a finding there is worth 39
findings in the output" -- reviewing 45 near-clones would spend the budget
proving the same thing forty times.

*First unit's findings (part_01, test_bridge_1x2_rd):* one real, in code
written the same day -- `seeded_rng()` fell back to a FIXED seed of 0, and
`TBBase` drew a seed without publishing it, so a TB built outside the pytest
flow would freeze its address RNG while logging a seed that does not replay
the run. Fixed at both ends: TBBase now writes its drawn seed to
`os.environ`, and `seeded_rng` draws instead of pinning 0. Also acted on: the
generated TB reported `addr_width=64 / id_width=8` while every fixture's
ports are 32/4 -- vestigial template constants, now derived from the ports.
Everything else in that unit was confirmed against the contract.

*Round complete, 2026-09-10: all 12 units reviewed and triaged.* Nine came
back clean against the contract. One produced the seed finding recorded
above. Two were CONFIRMED, and both were the same class of defect -- an
assertion that the bug itself satisfies -- which is exactly what this task
was raised to catch, and both were in the shared test template, so each fix
propagated to all 45 generated tests at once.

**part_10 -- the boundary probe swallowed any exception as proof.** The probe
walked addresses past the end of the map expecting a decode error, and its
`except RuntimeError` accepted whatever came back. A timeout, a BFM teardown,
a driver bug and a genuine SLVERR were indistinguishable, so a decode defect
confined to addresses above the 64 KB seed cap would have passed the entire
suite. The reviewer's phrasing is worth keeping: the test proved that
something went wrong, never that the right thing went wrong.

**part_12 -- the write path's error raise was dead for AXI-Lite masters.**
`master_write` raised on a bad response, but the three BFM families report
failure three different ways: a dict with a response field, a raised
`RuntimeError`, and a bare integer code. Only the first was handled, so on
every AXI-Lite fixture the raise could not fire and the probe's expectation
was unreachable.

**The fix, in the template rather than the output.** A new `AxiResponseError`
carries the numeric response alongside the message, `master_write` and
`master_read` normalise all three BFM shapes into it, and both probes now
assert `is_slverr` instead of accepting any failure. A probe that cannot
determine the response code re-raises rather than passing. Regenerated across
all 26 configurations per CRITICAL RULE #0.

*Mutation check.* The discrimination was verified RED before GREEN: with the
old accept-anything handler the probes passed against a response the new
assertion rejects.

*A note for whoever reads the run logs.* The FULL run that validated this
reported 8 failures, and none of them were the bridge. All eight were one
shared file, `rtl/common/fifo_control.sv`, caught half-written by another
agent mid-conversion to the reset macro -- Verilator died on an unterminated
macro argument list at EOF. The tell was that every failure was a build exit,
not an assertion. On a shared tree, read the error kind before reading the
test name.


---
