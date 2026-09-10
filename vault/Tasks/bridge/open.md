<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# bridge — open


## BRIDGE-002 — AMBA5 bridge support (AXI5 ports alongside AXI4)
**Status:** open 2026-08-08
**Priority:** P1
**Owner:** TBD

Goal: a bridge that is AMBA4-shaped like today but accepts AXI5
masters/slaves at the boundary, with a native-AXI5 fabric as the
follow-on.

**Already in-tree (verified 2026-08-08):** `rtl/amba/axi5/` has full
master/slave wr/rd wrappers + `_mon`/`_cg` variants + stubs,
feature-parameterized (ENABLE_ATOMIC / POISON / TRACE / UNIQUE / MPAM /
MTE / MECID / NSAID, AXI_ATOP_WIDTH); `rtl/amba/apb5/` has APB5
master/slave/monitor; CocoTBFramework has AXI5 BFMs and
`axi5_compliance_checker`.

**Genuine gaps:** no AXI5<->AXI4 feature converter/terminator IP; no
`*_to_apb5` shim (bridge APB path is APB4-only).

**Phasing:**

1. **A5-1 interop boundary (AMBA4 fabric, AXI5 ports):** config gains
   `protocol = "axi5"` per port + optional `axi5_features = [...]`
   mapped to the wrapper ENABLE_* parameters; validator rules (axi5
   master -> axi4/apb slave allowed with feature-drop warnings;
   `atomic` requires a termination policy — default DECERR + monitor
   event); adapter generator instantiates `axi5_*` wrappers and emits
   the feature-gated signal set; fabric stays AXI4. DV: AXI5 BFM
   master + compliance checker on an existing config.
2. **A5-2 native AXI5 sideband:** extend generated `_pkg` structs with
   feature fields; pass-through on AXI5->AXI5 paths (trace, unique,
   poison, MPAM/NSAID).
3. **A5-3 atomics + APB5:** AWATOP returns data on the R channel — the
   crossbar needs AW-issued R-response routing and read-return ID
   tracking (the hard part; design note before coding). New
   `*_to_apb5` shim for APB5 slaves.

**Done looks like (A5-1):** an `axi5` port type generates, validates,
simulates green with the AXI5 BFM + compliance checker, and feature
signals terminate per policy at the AMBA4 fabric boundary.

**Progress (2026-08-08):** A5-1 core LANDED for AXI5 masters —
`protocol = "axi5"` + `axi5_features` config, validator split
(sideband nsaid/trace/mpam/mecid/unique allowed; atomic/poison/mte/
chunking rejected naming their delivering phase; AXI5 slaves rejected
until A5-2), axi5_slave_{wr,rd}[_mon] boundary wrappers with
feature-gated external ports (no region — AXI5 dropped it) and full
tie/open termination at the AXI4 fabric, bridge_1x2_rd_axi5 fixture
in the manifest (+_mon variant), 10 new unit tests (37 total), sim
smoke green with the AXI4 BFM driving the base subset. axi5+mon is
supported (monitor surface verified identical to axi4's).
**A5-1 SIGNED OFF (2026-08-09):** both remaining items landed —
bridge_1x2_wr_axi5 fixture (wr emission path exercised: aw/w/b
surface with awtrace/awunique/btrace, sims green) and
test_bridge_1x2_rd_axi5_bfm5.py, a hand-written test driving the AXI5
port with the real AXI5MasterRead BFM plus AXI5ComplianceChecker on
the same prefix: 6 reads across both slaves data-correct, 708
compliance checks, 0 violations, status PASSED. The BFM resolved the
sideband pins (artrace/arunique) as optional signals on the DUT.
Note for A5-2: the BFM issues trace-clear transactions by default
(traced_transactions=0 in the report) — asserting sideband VALUES
end-to-end belongs with the native-sideband work.

Next: A5-3 (atomics + APB5).

**A5-3 design note (2026-08-09):** three slices, in order of
tractability. Facts on the ground: the axi5 wrappers already
transport AWATOP feature-gated through their skid path (both
families); the DV BFM's `atomic_operation` is write-shaped
(`write_transaction` + atop — it does not collect an R return); the
converters IP has `axi4_to_apb4_{convert,shim}` as the template and
`apb5_pkg` provides apb4<->apb5 m2s/s2m conversion functions.

*Why read-return atomics are the hard part in THIS fabric:* AWATOP
classes — `01xxxx` AtomicStore (B-only response), `10xxxx`
AtomicLoad, `11000x` AtomicSwap/Compare (original data returns on
the R channel, using the AW ID). The bridge splits wr and rd into
separate wrappers, adapters, and xbar paths per port; every R-return
tracker (slave adapter rd-side FIFO/CAM pushing on AR handshake,
master adapter r_slave_select FIFO, xbar rready gating on rid_valid)
learns only about ARs. A load-class atomic issues on the wr path and
returns on the rd path — invisible to all three trackers, so the R
response would hang. Fixing it properly needs a per-ID tracking
block SHARED between a port's wr and rd adapters (cross-adapter
ports through the bridge top), pushed on atomic-AW handshake, plus
per-ID (CAM) rather than in-order tracking on the master rd path.
The AXI spec's "an atomic's ID must not be concurrently in use by
reads" rule keeps routing unambiguous once tracked.

- *A5-3a — store-class atomics, native transport:* `atomic` becomes
  connectivity-gated exactly like poison (every connected path
  AXI5-both-ends + atomic-enabled + width-matched); `aw.atop[5:0]`
  joins the sideband spec table and rides the fabric structs by the
  slice-2 mechanism unchanged. NEW RTL: a small atomic filter at the
  atomic-enabled master boundary (fub side, before the structs) —
  read-return ATOP (`awatop[5]==1`) is NOT forwarded: the filter
  swallows the AW + its W burst and generates a local DECERR B (the
  A5-1 termination policy, narrowed from "all atomics" to
  "read-return atomics"), with a monitor event on mon variants.
  Store-class forwards natively; the external slave performs the op.
  The filter is a real little FSM (must consume W beats) — build it
  as reusable IP (rtl/amba/axi5/axi5_atomic_filter.sv) with its own
  val tests before wiring it into the generator.
  *Filter IP DONE (2026-08-10):* control-plane-only design (handshakes
  + atop + id + wlast; payload routes around it): route queue pushed
  per AW / popped at WLAST steers or sinks W bursts, response queue
  drains local DECERRs when downstream B is idle. W stalls until its
  AW is queued (deadlock-free — AW never depends on W). Documented
  limitation: a local DECERR can pass a same-ID in-flight write's B,
  which the AXI atomic ID rule already forbids a compliant master
  from observing. val/amba/test_axi5_atomic_filter.py green (mixed
  forward/swallow traffic, multi-beat discard, DECERR ids/order);
  -Wall lint + decl-order + registry-audit clean. *A5-3a DONE
  (2026-08-10, commit be2fd6bc):* aw.atop[6] in the sideband table +
  external surface; 'atomic' connectivity-gated (validator check
  generalized over gated features); master adapter inserts the
  filter pref_axi_* -> fub_axi_* on atomic-enabled wr paths
  (handshakes + B payload through the filter, the rest passes
  around); filelist emission -f's the filter closure. Fixture
  bridge_1x2_wr_axi5a (+_mon) sims 2/2 green; hand-written atomics
  test: plain/AtomicStore forward with atop intact at the slave AW
  and land in memory, AtomicLoad/Swap DECERR locally with no slave
  AW and no memory write; 52 generator unit tests; 23/23 bridges
  regenerate, pre-existing byte-identical. A5-3 remaining: only
  A5-3b (read-return atomics), deferred until a consumer exists.
- *A5-3b — read-return atomics:* the shared per-ID tracking block
  above. Design that block standalone first; defer until a concrete
  consumer exists (nothing in-tree issues AtomicLoad today, and the
  BFM cannot check the return path yet either).
- *A5-3c — APB5 slaves (independent, do first):* new converters IP
  `axi4_to_apb5_shim` = the axi4_to_apb4 conversion core + the
  apb5_pkg m2s/s2m conversion functions + PWAKEUP generation (assert
  with PSEL, deassert after the transfer) + user-signal ties;
  slave_adapter_generator gains a protocol="apb5" branch mirroring
  the apb one; validator apb5 constraints mirror APB4's (rw-only,
  32-bit). DV: apb5 slave BFM exists (CocoTBFramework apb5), so a
  bridge_1x2 fixture with one apb5 slave closes it.
  *Step 1 DONE (2026-08-10, commit f6f30762):* the shim IP itself —
  converters/rtl/axi4_to_apb5_shim.sv (pin-superset wrapper over the
  apb4 shim; PAUSER/PWUSER tied '0 out, PWAKEUP/PRUSER/PBUSER
  terminated in; mirrors apb5_slave.sv pin-for-pin) + its closure
  filelist; lint/audit/decl-order clean.
  *Step 2 DONE (2026-08-10):* protocol="apb5" through the whole
  generator stack per the map below — all 14 protocol-test sites,
  the Axi4ToApbShim component's protocol switch, bridge-top +
  adapter + instance external surfaces (5 extra pins), validator/
  config whitelist, filelist emission, and the TB template's three
  apb branches (APB4 BFM drives the APB5 port: same transfer
  protocol, extras terminate in the shim). Fixture
  bridge_1x2_rw_apb5 (+_mon) in the manifest; sims 2/2 green;
  50 generator unit tests; 22/22 bridges regenerate — RTL
  byte-identical for all 21 pre-existing (TBs picked up one
  semantically-neutral template line). A5-3c CLOSED; next is A5-3a
  (store-class atomics + the axi5_atomic_filter IP).
  *Step 2 implementation map (as executed):* treat apb5
  as "the apb branch + 5 extra external pins" everywhere:
  (a) Axi4ToApbShim component gets protocol='apb4'|'apb5' (module
  name swap + connect_apb4_master emits the 5 extra pairs);
  (b) slave_adapter_generator: extend the protocol tests at lines
  ~90/97, ~328/330, ~507, ~634, ~724 to include 'apb5' and add the 5
  signals to _generate_apb_external_ports for the apb5 case;
  (c) SlaveAdapterInstance: allow 'apb5', external-interface branch
  += the 5 signals; (d) bridge_module_generator external apb port
  emission + validator (validate_protocol whitelist, and
  validate_apb_constraints applies to apb5 too) + config_loader
  protocol whitelist; (e) bridge_generator.py filelist emission: apb5
  slaves -f axi4_to_apb5_shim.f instead of the apb4 one; (f) fixture
  bridge_1x2_rw_apb5 (axi4 master rw, one axi4 + one apb5 slave) +
  generated tests + a hand-written check against the CocoTBFramework
  apb5 slave BFM; regen all bridges, zero drift on the existing 21.

**A5-3d — AXI5-Lite slaves (protocol="axil5"): LANDED 2026-09-05.**
Follows A5-3c beat for beat -- treat axil5 as "the axil branch plus the
AXI5-Lite sideband".

*The IP first:* `converters/rtl/axi4_to_axil5{,_wr,_rd}.sv`, wrappers over
`axi4_to_axil4_{wr,rd}` (AXI5-Lite keeps the AXI4-Lite transfer protocol
unchanged, so burst decomposition and response folding are inherited) plus
closure filelists. Sideband disposition is FORWARDED (lock/user/wuser, and
buser/ruser returning) / TIED (loop, mpam, mecid, nsaid, trace, poison) /
TERMINATED (bloop, btrace, rloop, rtrace, rpoison). Two design calls worth
recording:

- **The tied group has no `ENABLE_` parameter.** They are driven `'0`
  unconditionally, so a knob for them could not change the design --
  worse than no knob, because a reader sets it and believes something
  happened. Only `ENABLE_LOCK` and `ENABLE_USER` exist. Verilator agrees:
  the modules lint clean with UNUSEDPARAM *unwaived*.
- **The tied group's PORTS do exist.** An AXI5-Lite boundary whose shape
  changes with a config knob cannot be wired to a fixed external
  completer. Always present, always driven.

*One real bug, found and fixed before commit:* the AW/AR sideband must be
HELD, not passed through. The core decomposes, so one AXI4 AW handshake
becomes N AXI5-Lite ones, and `s_axi_awready` drops on acceptance -- the
master then presents the NEXT transaction's AW while beats 2..N are still
going out. The first version passed it combinationally, and burst A's beats
carried burst B's USER from beat 0. The fix mirrors the core's own
`r_aw_active ? r_aw_addr : s_axi_awaddr`. Only OVERLAPPING bursts can catch
it; sequential traffic cannot. Mutation-checked: RED against the unfixed
RTL, GREEN after.

*Generator, per the A5-3c map:* (a) new shared table
`bin/bridge_pkg/axil5_sideband.py` -- port names, widths, directions and
the ENABLE_ mapping in ONE place, read by the adapter, the shim component
and the bridge top, so the three port lists cannot drift; (b)
`Axi4ToAxilShim` gains `protocol='axil4'|'axil5'` (module-name swap +
sideband pairs + parameter suffix); (c) slave_adapter_generator protocol
tests extended and `_generate_axil5_sideband_ports`; (d)
SlaveAdapterInstance + bridge_module_generator external surfaces; (e)
validator/config_loader whitelists, plus `validate_axil5_features`:
`axi5_features` on an axil5 port accepts ONLY `user`/`exclusive`, and
REJECTS a tied group by name rather than ignoring it, so the config cannot
imply something it does not do; (f) filelist emission -f's the axil5
closures; (g) TB template picks the AXIL5 BFMs, with the import made
conditional so bridges without an axil5 slave stay byte-identical.

**Verified:** 63 generator unit tests (10 new, incl. one asserting the
table and the RTL name the same ports); fixture `bridge_1x2_rw_axil5` in
the batch manifest; 24/24 bridges regenerate with the 23 pre-existing
byte-identical in RTL *and* TB classes; the generated bridge lints at
parity with its axil4 sibling (13 PINCONNECTEMPTY vs 26, no new class);
generated bridge test 2/2 green; converter suite 8/8 across three levels.

**Not done, deliberately:** axil5 as a bridge MASTER protocol. apb5 is
slave-only too; a master-side AXI5-Lite requester is a different piece of
work and nothing in-tree needs one.

*Adjacent finding, NOT fixed here:* `make verilator` in
`projects/components/bridge/rtl` fails -- measured 2026-09-10 as 13 of 38
variants, all PINMISSING on one instance, and NOT deliberate: see
[[BRIDGE-013]]. (This note previously said "all 36 variants, entirely from
pre-existing PINCONNECTEMPTY on deliberate open pins"; both halves were
wrong, which is what a gate nobody runs buys you.) The `mon`
variants additionally surface real WIDTHEXPAND/UNDRIVEN warnings inside
`rtl/amba/monitor/*`. Both predate this change (the RTL they fire on is
byte-identical to HEAD) and want their own pass.

**A5-2 design note (2026-08-09):** two slices.

- *Slice 1 — AXI5 slave ports, interop mode:* LANDED 2026-08-09.
  `axi5_master_{wr,rd}[_mon]` boundary wrappers on axi5-protocol
  slave ports, same feature whitelist, sideband terminates at both
  boundaries. Mixed-protocol fixture bridge_1x2_rd_axi5s (axi4 master,
  one axi4 + one axi5 slave) in the manifest; 46 generator unit
  tests; 19/19 bridges with the 18 pre-existing byte-identical; sims
  green incl. the mon variant. Known benign dangle: the axi5 slave
  adapter's xbar_*_arregion input (fabric has region, AXI5 doesn't).
  Deferred with slice 2: wr-channel axi5-slave fixture (wr path
  generated/compiled, not simulated).
- *Slice 2 — native sideband pass-through:* LANDED 2026-08-09.
  Implementation matches the design note below: shared spec table
  `bin/bridge_pkg/sideband.py` (feature -> per-channel struct fields:
  nsaid[4]/trace/mpam[11]/mecid[16]/uniq on aw+ar, trace on b+r,
  poison on w+r; `uniq` because `unique` is an SV keyword); `_pkg`
  structs carry the bridge-wide feature UNION (pure-AXI4 bridges
  byte-identical — zero-drift held across all 19 pre-existing
  bridges); master adapters pack own-feature fields from the
  wrapper's fub sideband on the DIRECT width arm and '0 on converter
  arms; the xbar forwards request fields unconditionally (non-native
  sources are already '0) and muxes b/r fields from featured slaves
  only; slave adapters ride `xbar_<slave>_axi_<sig>` nets into the
  axi5_master_* wrapper via the component's new `native_sideband`
  flag. Validator: `poison` moved from phase-gated to
  connectivity-gated (every connected path AXI5-both-ends +
  poison-enabled + width-matched, else ERROR — dropping POISON would
  launder corrupted data); droppable sideband that terminates
  mid-path now prints generation-time warnings. mte/chunking stay
  phase-gated.
  **Verified:** 47 generator unit tests (3 new poison rules); new
  native fixtures bridge_1x2_{rd,wr}_axi5n (+_mon) — the wr one
  closes the deferred wr-channel-AXI5-slave-sim item and exercises
  poison + per-slave feature asymmetry; hand-written VALUE tests
  drive arnsaid/artrace/arunique/awtrace/wpoison and assert the same
  values at the far boundary + rtrace/btrace return paths + rtrace=0
  from AXI4 slaves (closes the A5-1 deferred values item); all
  interop axi5 fixtures re-simed green with the new plumbing.

### BRIDGE-007: scrub the tests for completeness (bridge)

**Priority:** P2. Blocks the coverage/formal push, not day-to-day work.
**Status:** open 2026-09-04. Raised by Sean: test scrubbing was meant to be
part of the kimi review packets and got dropped along the way. Applies to the
components suites as well as rtl/.

**Sequencing.** A FOCUSED pass, run after qc/humanize is finished everywhere
and BEFORE coverage and formal are driven clean. Doing it after coverage would
mean chasing numbers produced by tests nobody has audited.

**Scope:** `projects/components/bridge/dv/tests/` -- 39 test files, the largest components suite, and almost all of it is generated.

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

Still owed on this task: the external testqc review round.


---

### BRIDGE-013: in the _mon variants the subtractive slave's monitor is built and left unconnected

**Priority:** P2. Not lint noise -- the lint gate is pointing at a real
disconnection, and 13 of 38 variants fail on it, which is why the gate has
been reporting nothing useful.

**Found by** running the bridge lint gate 2026-09-10 (BRIDGE-007 follow-up).
`make verilator` in `projects/components/bridge/rtl`: **13 of 38 variants
FAIL, 427 `%Warning-PINMISSING`, and every one of them is the same
instance** -- `u_subtractive_adapter` in a `*_mon` top.

**The mechanism.** In a `_mon` variant the generated `subtractive_adapter`
declares **24 monitor ports** (`i_mon_time`, `monbus_{rd,wr}_{valid,ready,
packet,timestamp}`, `cfg_{rd,wr}_*`) and instantiates a monitor behind them
(`subtractive_adapter.sv:255` wires `i_mon_time` and `monbus_valid` into the
submodule). The bridge top instantiates that adapter and connects **none of
them**. So the subtractive slave's monitor is elaborated, occupies area, and
its monbus output goes nowhere; its cfg inputs float. The non-`_mon`
variants emit zero such ports, so this is specific to the monitor build.

BRIDGE-009's subtractive slave also reports unmapped accesses through its
sticky `SUBTRACTIVE_STATUS` / `SUBTRACTIVE_ADDR` cfg registers and
`unmapped_irq`, which DO reach the top -- so the observable BRIDGE-009
behaviour is intact and the tests that cover it are honest. What is lost is
the monbus path: an unmapped access never produces a monbus packet in a
`_mon` bridge, and nothing says so.

**The generator says it is deliberate, and the RTL disagrees.**
`bridge_generator.py:796` reads "The subtractive catch-all has no monitor
wrapper (it reports on its own monbus port)" -- but in `_mon` variants the
adapter generator emits one anyway and the top does not wire it.

**Two ways out, and it is a design decision:**
1. **Connect it.** Add the subtractive's monbus as a source on the
   monbus arbiter tree so an unmapped access is reportable like any other
   error. Costs an arbiter input per `_mon` bridge and changes the monbus
   topology (and the tally/coverage expectations of the `_mon` tests).
2. **Stop emitting it.** Suppress the monitor and its 24 ports on an
   INTERNAL slave, matching what the generator comment already claims.
   Cheaper, removes dead area, and makes the lint gate meaningful.

(2) matches the stated intent; (1) is the one to take if an unmapped access
ought to be visible on monbus. Either way the lint gate goes green and starts
reporting real findings again -- do NOT waive PINMISSING to get there, which
would hide exactly this class.

**Correcting the record:** the note carried on [[BRIDGE-002]] said `make
verilator` fails on "all 36 variants, entirely from pre-existing
PINCONNECTEMPTY on deliberate open pins". Measured: 13 of 38, all
PINMISSING, one instance, not deliberate.
