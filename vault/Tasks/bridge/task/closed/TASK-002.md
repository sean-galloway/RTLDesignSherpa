# TASK-002: AMBA5 bridge support (AXI5 ports alongside AXI4)

> Migrated 2026-09-27 from `vault/Tasks/bridge/closed.md` as **BRIDGE-002** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** CLOSED 2026-09-10. Every phase landed: A5-1 (AXI5 masters on
the AMBA4 fabric), A5-2 (AXI5 slaves, native sideband through the structs),
A5-3a (store-class atomics, filter for write-only ports), A5-3b (read-return
atomics native on rw ports, with the out-of-range answer and the response-mux
invariant guard), A5-3c (APB5 slaves), A5-3d (AXI5-Lite slaves). Verified by
the bridge FULL regression on 2026-09-10: 249 passed across 27 fixtures with
the AXI5 compliance checker armed on every AXI5 master port. Deliberately not
done, and not owed by this task: AXI5-Lite and APB5 as MASTER protocols
(slave-only by decision; nothing in-tree needs a requester), and the
"native-AXI5 fabric as follow-on" from the original goal, which the sideband
structs made unnecessary for every feature anyone has asked for. Either wants
its own task if it ever becomes real.
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

Next: A5-3 (atomics + APB5). [All of A5-3 landed by 2026-09-10; see the slices below.]

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
- *A5-3b — read-return atomics: LANDED 2026-09-10.* The consumer the
  deferral was waiting on was built alongside it: the AXI5 slave BFM now
  performs atomics on its memory model and returns the original data on R,
  and the AXI5 master BFM collects it. With that, the fabric side.

  *What the design note above got right, and what it did not need.* A
  read-return atomic is invisible to every AR-fed tracker, that part held.
  But the "per-ID tracking block SHARED between a port's wr and rd
  adapters" did not need to exist: the master adapter's wr and rd paths are
  one module, so the atomic AW simply pushes into the existing AR->R
  slave_select FIFO. What that FIFO needed was a DUAL push (an AR and an
  atomic AW can handshake in the same cycle; AR takes the first slot, the AW
  the second) and the AW's own single-target gate requiring two free slots.
  The AW is the last entry pushed, so it becomes the active target. In-order
  routing stays sound because the single-target rule already guarantees
  every live entry shares one slave. Per-ID tracking is needed only at the
  SLAVE adapter, where reads and atomics from the same requester return in
  an order no FIFO can predict: `rtl/amba/axi5/axi5_atomic_rr_tracker.sv`
  (its own val test, gate/func/full) records (AWID -> requester) at every
  AW with AWATOP[5], answers combinationally from RID, and an R beat it
  claims is routed by its tag and does not pop the in-order FIFO. The
  atomic AW's awready is held while it is full. The BRIDGE-010 sim check
  skips tracked beats and reports an RID that matches both a tracked atomic
  and the FIFO head: two requesters aliasing one ID at a slave, which this
  fabric never disambiguated.

  *The out-of-range case, found while writing the test.* A read-return
  atomic whose address nobody owns decodes to the subtractive slave, which
  answers DECERR on B and knows nothing about R. With the master adapter now
  holding an R-return slot for it, that beat never coming would have wedged
  every later read on the port behind the stuck head: BRIDGE-009's hang,
  reborn on the atomic path. So the master adapter answers those itself: the
  tracker entry carries a `local` flag and the AW's ID, and when it reaches
  the head the R mux presents one DECERR beat with that ID while holding
  every slave's rready off. The rw fixture's sram range was halved
  (0x8000_0000, 0x4000_0000) so 0xC000_0000 and up is genuinely unmapped
  and the test can exercise it: B and R both DECERR, then a plain read and
  an in-range atomic still complete. Mutation-checked RED: with
  `r_local_head` forced to zero the OOR atomic's R never arrives.

  *One invariant the dual push nearly broke, and the guard that now names
  it.* The crossbar's response mux is an OR-merge; it is a mux only while at
  most one connected slave's tracker head belongs to a given master, which
  the master adapter's single-outstanding-target gate guarantees. With the
  AR->R FIFO empty, an AR and an atomic AW to DIFFERENT slaves both pass
  their target rule in the same cycle, and the first dual push happily held
  both -- two slaves then drove one master's R lines and the ORed IDs sent
  beats to the wrong per-ID queues. It surfaced as a seed-dependent read
  starvation in the sign-off test (two cells of three, one seed base), and
  passed clean under another base. The AW now yields in that cycle. And
  every generated crossbar carries a sim-only `$countones(...) > 1` guard on
  each master's response-mux select vector, so the invariant slipping is a
  named error in the cycle it happens rather than a starvation a thousand
  cycles later. That guard is the one change to the 26 pre-existing
  bridges' RTL (their `*_xbar.sv`); adapters are byte-identical.

  *Where the filter stays.* A write-only atomic master has no R path, so it
  keeps the A5-3a `axi5_atomic_filter`; `rr_atomic` on the master adapter
  is exactly "atomic AND rw". Validator: an rw atomic master's connected
  atomic slaves must be rw (else DECERR-by-filter would have been the honest
  answer, and now there is no filter) and must not use enable_ooo (the CAM
  read path has no hook for the return tracker; it is also unexercised, no
  fixture sets it). Filelist emission pulls the filter only for write-only
  atomic masters and the tracker only for rw atomic slaves.

  *Also fixed on the way.* The AXI5 slave BFM used to write an
  AtomicStore's operand as a plain write; it now performs the store-class
  ALU op, and the A5-3a test's expectation (memory == operand) was that old
  behaviour written down. It now expects old + operand.

  *Verified.* Fixture `bridge_1x2_rw_axi5a` (+mon), the rw twin of the
  A5-3a fixture. 27/27 bridges regenerate; the 26 pre-existing are
  byte-identical in RTL (the 2x2_axi5 TB picked up one line pairing its
  slave BFMs). Lint gate 40/40 clean. 71 generator unit tests (5 new: the
  two validator rules, generation of both atomic fixtures, and that the
  write-only one still gets its filter). Hand-written
  `test_bridge_1x2_rw_axi5a_atomics.py`: AtomicLoad ADD/SET/UMAX, Swap,
  Compare match and mismatch on both slaves, each checked three ways (R data
  is the pre-op value, memory holds the post-op value, a plain read agrees),
  then reads and atomics in flight together across and within slaves; 16 /
  112 read-return atomics routed at func / full. Mutation-checked RED: with
  the tracker's hit removed from the slave adapter's rid_valid, the R beat
  is never routed and the test dies on "atomic read-return timeout".

  *Checker.* `AXI5ComplianceChecker` treats a read-return atomic AW as an
  outstanding single-beat read (RLAST and ordering checks apply) -- but only
  on an interface that has an R channel, since on a write-only port the
  boundary filter answers with DECERR on B and no R can ever come; the first
  version registered it regardless and the A5-3a test then reported every
  second atomic as reusing a live ID. It flags an
  atomic whose ID is still in use by an outstanding read or write
  (ATOMIC_ID_IN_USE), and flags an R beat with no outstanding request
  (R_WITHOUT_REQUEST) -- previously such a beat was silently ignored. The
  first version of the hand-written test tripped the ID rule itself at full
  depth: it rotated 14 IDs over 32 in-flight transactions, so a word's four
  transactions reused IDs a still-outstanding word held, and two read
  coroutines then shared one per-ID response queue. It now runs in batches
  of three words so twelve distinct IDs cover everything in flight.
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

*Adjacent finding, now RESOLVED:* `make verilator` in
`projects/components/bridge/rtl` used to fail -- measured 2026-09-10 as 13
of 38 variants, all PINMISSING on one instance, and not deliberate. (An
earlier version of this note said "all 36 variants, entirely from
pre-existing PINCONNECTEMPTY on deliberate open pins"; both halves were
wrong, which is what a gate nobody runs buys you.) [[BRIDGE-013]] was the
cause and is closed: an internal slave no longer gets a monitor built and
left unconnected. Re-measured after the fix, same day: 38 of 38 variants
elaborate with zero errors and zero warnings, the `mon` variants included,
so the WIDTHEXPAND/UNDRIVEN noise this note attributed to
`rtl/amba/monitor/*` went with them. Nothing owed here.

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
