<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# bridge — open

## BRIDGE-003 — All six *_mon_monitor stress tests fail (pre-existing)
**Status:** open 2026-08-08
**Priority:** P1
**Owner:** TBD

The full bridge DV run (2026-08-08, on `fix/bridge-xbar-num-slaves-param`
after the BRIDGE-001 fixes) shows all six monitor stress tests failing:
1x2_rd_mon, 1x2_rd_regblock_mon, mix_a/b/c/d_mon (`test_*_mon_monitor.py`).
Verified pre-existing: `test_bridge_mix_d_mon_monitor` fails identically
in a worktree at the branch's base commit, so this is NOT fallout from
the NUM_SLAVES / package-import / sweep work — 25/25 non-monitor tests
pass with all of that landed.

Owner note (2026-08-08): likely a COMMON issue in the monitor
`block_ready` path — another agent is already working that block.
Hold off on independent diagnosis here until that lands; then rerun
the six stress tests before doing anything bridge-side.

**Done looks like:** all six monitor stress tests green from clean
builds on this branch (or a documented decision that the stress
expectations changed with the monbus rework).

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
