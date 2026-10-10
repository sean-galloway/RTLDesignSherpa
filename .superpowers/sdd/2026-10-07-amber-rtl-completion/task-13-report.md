# Task 13 Report: SymbiYosys control-layer proofs (tiny geometry SETS=16 / WAYS=2 / 64B / 64b)

Date: 2026-10-09 (close-out 2026-10-10)
Author: implementer (Task 13)
Branch: shared `main`
Commit: 0233b6a2d (formal/amber README); sdd docs commit follows

## Verdict

DONE (owner ruling 2026-10-10). All eight task runs PASS: pf prove+cover,
victim prove+cover, snoop_resp prove+cover, control cover, control
liveness prove, and the control safety prove — non-vacuous PASS
(boolector, depth 126, bound 104, 68 min, run against the current disk
state on 2026-10-09; files unchanged since). A final clean re-run of the
safety prove (launched 2026-10-10 11:34) died silently at step 55, the
third such death (see notes); per owner ruling the recorded PASS on
identical content stands as the verdict rather than burning further
hours on a loaded box. Gate PASS (checked=4 CURRENT=4). Step 4 PASS
(274/274).

## Deliverables

Four SymbiYosys proofs under `formal/amber/`, house sby pattern copied from
`formal/common/gaxi_fifo_sync/` (`[tasks] prove/cover`, `smtbmc z3`,
`read_verilog -formal -sv <block>_flat.v` + `formal_<block>.sv` wrapper,
`prep -top`, `delete t:$print`, `includes/reset_defs.svh` mapping, Makefile
with the tooling-TASK-026 `check-flat` target):

| Directory | DUT closure in flat | Proves |
|---|---|---|
| `formal/amber/amber_control/` | amber_pkg + amber_pending_fill_bypass + amber_victim + amber_control | (1) no stale data after external write, (2) no deadlock/livelock under fair arbitration |
| `formal/amber/amber_pending_fill_bypass/` | amber_pkg + amber_pending_fill_bypass | (1) leaf: pf state accuracy, beat-mask monotonicity |
| `formal/amber/amber_victim/` | amber_pkg + amber_victim | (3) victim handoff |
| `formal/amber/amber_snoop_resp/` | amber_pkg + gaxi_skid_buffer + axi4ace_snoop_slave + amber_snoop_resp | (4) AC/CR/CD ordering, one closed response |

Plus `formal/amber/specialize_params.py` (see Toolchain findings) and the
`.sby` / Makefile / wrapper / flat per directory.

## The safety/liveness split (and why the depth is 126 for both)

amber_control carries two proof obligations of very different shape, and
one wrapper serves both poorly:

- **Safety** (no stale data after an external write, write-effect exactness,
  grant-cycle CRRESP vs the spec copy, FSM integrity): BMC to depth **126**
  with the behavioral tag model. Depth is the DERIVED worst-case span of the
  safety claims, not a guess: the poison arc (install a line, invalidate it
  externally, look it up) costs init 16 + install transaction (35 + up to
  2x20 snoop detours) + invalidating snoop (20) + lookup (2) ~ **113**; the
  write-effect claims span one transaction (16 + 75 = 91); grant-cycle
  claims <= 20 post-init. An earlier depth-60 estimate ignored detours and
  was under-derived -- caught before it could under-prove the poison claim.
  K-induction was tried first (2 s closing lemmas added: one-hot
  `sn_return_q`, `sn_stale_q -> sn_ref_q==I`); the poison invariant is not
  transition-closed without importing per-set tag uniqueness (a full
  functional-correctness coupling), so BMC at the derived depth is the
  smallest sound choice.
- **Liveness** (bounded residences + whole-request bound 104): quantifies
  over ALL tag behaviors, so the tag store is a **free environment** in
  `formal_amber_control_live.sv` -- the strongest abstraction, and it
  removes the memory whose SMT store chains dominated solver time. Depth
  **126** = init 18 + bound 104 + margin, so the timer bound is exercised
  to its full value (no vacuous tail).

Both wrappers carry the identical fair-environment table.

## Per-proof assumption / abstraction inventory

### amber_control (proofs 1 and 2)

Abstractions:

- **Tag array: exact abstract model** (smallest sound choice). The wrapper
  holds a 16x2 store of `{tag[21:0], state[2:0]}`, resets to Invalid, and
  applies every port-A write the DUT performs. This is precisely
  `amber_tag_array`'s semantics (synchronous write, combinational read) at
  the tiny geometry, so the DUT's lookup/snoop reads see exactly what the
  real array would hold. No "assume the init walk completed" is needed: the
  walk's net effect (all Invalid) is the model's reset state, and the walk's
  writes are applied as they happen. The poison property is checked on this
  model, so a dropped or misdirected invalidation write fails the proof.
- **Data arrays: values not claimed.** Port-A/B read data only feed `rsp_data`,
  the victim-line gather, and CD data — never any MESI-state decision. The
  state proofs therefore never branch on data values; the unclaimed return
  payloads are tied to 0 in the wrappers (`ctrl_data_b_rdata` in
  `formal_amber_control.sv`, `ctrl_cddata` in `formal_amber_snoop_resp.sv`)
  — sound precisely because no property claims those payload values.
- **Replacement engine: free input** (`repl_way`); any victim way is legal.
- **fill / drain partners: free inputs with well-formedness + fairness.**
- **snoop responder side: free inputs** (`snoop_req/type/addr`, `cdready`).

Assumptions (each an environment obligation, recorded in
`formal_amber_control.sv`):

| # | Assumption | Why it is sound |
|---|---|---|
| A-reset | house protocol: reset asserted at time 0, released after 2 cycles, never re-asserted | house pattern |
| A-fill-1 | `fill_done` only after `fill_start` seen, one pulse per launch | D-12 partner contract (done pulses) |
| A-fill-2 | fill done forced within 12 cycles of start (fair partner) | fairness, not an RTL bound; the bounded-residence assertions are the contrapositive of deadlock |
| A-fill-3 | `fill_done` implies all 8 beats strobed (RLAST contract); beats arrive in order 0..7, one strobe per beat, only between start and done | AXI R-channel data-before-RLAST, in-order beats |
| A-drain | drain done only after start, one pulse, forced within 6 cycles | D-12 + fairness |
| A-cd | `cdready` stalls at most 1 cycle per beat (fair manager) | fairness |
| A-sn-1 | snoop grant spacing >= 6 cycles | fair arbitration: the fabric cannot outrun the CPU path indefinitely |
| A-sn-2 | at most 2 snoop grants per accepted CPU request | fair arbitration: the CPU gets guaranteed slots |
| A-cpu-1 | `req_valid` only at IDLE | the blocking frontend's contract (`ctrl_req_ready == IDLE`) |
| A-cpu-2 | one outstanding CPU request | blocking design contract |

None of these assume the Task-7 bug fixes away; `ap_hit_wr` pins the
`:944` one-hot write exactly as the sim suites do.

Properties (all live in the model — see "Toolchain findings" for why that
statement is verified, not assumed):

- `ap_no_stale_after_ext_write` — after an invalidating snoop completes on
  an installed line, no way of that set presents the poisoned tag in a
  valid state until a (re)install writes the set. (Proof 1.)
- `ap_inv_write_lands`, `ap_fill_install`, `ap_pend_install`,
  `ap_hit_wr` — the write effects (invalidation, fill commit with
  upgrade/victim way + pending-effect state, E->M promotion with the hit-way
  one-hot) land exactly as specified.
- `ap_grant_crresp` — at the grant the CRRESP equals an **independent spec
  copy** of the HAS Table 3.0 decode evaluated at the resolved reference
  state (pf > stale-victim > victim-buffer > installed hit > Invalid), and
  the resolution matches the DUT's own `sn_ref_grant`.
- `ap_cd_gating`, `ap_stale_nodt`, `ap_victim_cd_data` — CD beats present
  exactly when servable (pf per-beat gate included), stale victim answered
  with no data transfer, victim-buffer CD beats sourced from the staged line.
- `ap_fsm_onehot`, `ap_never_error` — one-hot FSM never corrupts, never
  sticky-ERRORs.
- Bounded liveness (proof 2): `ap_fill_bounded`, `ap_drain_bounded`,
  `ap_victim_bounded`, `ap_snoop_bounded`, `ap_txn_bounded` (whole
  request-to-response < 120 cycles under the fair constraints). Bounds are
  generous (~2x the honest worst path) so a FAIL means real starvation.

### amber_pending_fill_bypass (proof 1, leaf)

- No abstractions (leaf has no memories). All inputs free.
- One environment assumption: `pf_load` never arms an Invalid state
  (control only ever loads S/M install states) — the leaf's in-system use.
- Properties: state accuracy (armed register holds exactly the loaded
  addr/state), match implies armed, a match is answered at the post-fill
  state never pre-fill Invalid, beat mask monotonic while armed,
  `pf_beat_valid` is the mask bit at the presented index, load > clear >
  beat priority.

### amber_victim (proof 3)

- No abstractions, no assumptions (all inputs free — the guard must hold
  even for a broken requester).
- Properties: never loaded while busy (a load requested while valid is
  ignored, contents unchanged); handoff payload exact and stable while
  valid; occupancy ordering (load lands -> valid, holds until clear, clear
  empties, clear-wins-over-load priority, clear on empty retires nothing);
  `busy == valid`, `empty == !valid`; valid implies a load landed.

### amber_snoop_resp (proof 4)

- Abstraction: ACE manager pins and the control side are free environment
  (with the assumptions below); the transport (`axi4ace_snoop_slave` +
  three `gaxi_skid_buffer`) and the SR FSM are the DUT.
- Assumptions: house reset; AXI AC valid held until accepted; fair control
  grant (`ctrl_snoop_ready` within 2 cycles in SR_LOOKUP); fair control
  data (`ctrl_cdvalid` within 2 cycles in SR_DATA, `ctrl_cdlast` exactly on
  the 8th beat — the amber_control CD contract); fair manager
  (`crready`/`cdready` stall <= 2); `ctrl_crresp`/`ctrl_cddata` fully free.
- Properties: R1 every pin CR belongs to an accepted, unclosed AC (AC/CR
  count never negative); R2 CR only after CDLAST at the FUB (the responder
  ordering contract; DT-responses); R3 CR payload integrity at FUB and at
  the pins via a ghost model of the CR skid FIFO (depth 4); R4 one closed
  response per AC; R5 channel coherence (FUB CR only in SR_RESP, CD only in
  SR_DATA, request only in SR_LOOKUP); bounded service (accept -> pin CR
  closes < 64 cycles under fairness).

## Toolchain findings (important, house-relevant)

1. **yosys 0.62+95 (oss-cad-suite) has no working `bind`.** The SV frontend
   parses `bind` and stores the property module as `$abstract\...`, but no
   pass ever instantiates it — the properties are **silently dropped** and
   sby reports PASS vacuously. This burned two debugging rounds: an early
   "PASS" had zero `$check` cells in the model. Detection: count
   `FLAVOR "assert"` in `model/design_smt2.smt2` (0.62 merged
   `$assert/$assume/$cover` into `$check` + FLAVOR), or `dump | grep cover`.
   **Every proof in this task was verified to contain its assertions in the
   sby model before its PASS was accepted.**
2. **yosys native SV frontend rejects hierarchical references**: `dut.sig`
   parses but creates an implicit UNDRIVEN wire ("is implicitly declared"
   warning) — the assertion then checks an anyseq wire. Another silent
   vacuous-pass path.
3. **yosys native SV frontend cannot read `amber_pkg`** (`return {..}` and
   `return x;` in functions are unsupported), so wrappers carry a local
   Verilog-2005 spec copy of the Table 3.0 CRRESP decode as the formal
   cross-check of the pkg function.
4. **yosys `expose` works** (adds module output ports for internal wires)
   and is the internal-observability mechanism used here — but it must run
   while the target module is the one hierarchy elaborates. On a
   parametrized DUT (or any `#()` override) hierarchy derives a `$paramod`
   and the exposed ports / bind are lost. `formal/amber/specialize_params.py`
   (run in both Makefiles' flat recipes) deletes the DUT's parameter
   declarations and substitutes the tiny-geometry constants, making the DUT
   truly parameterless. Unlisted modules (the leaf cells, the ACE
   transport) keep their parameters and receive constant overrides — no
   behavioral change. `check-flat` regenerates through the same transform
   so `--check-flats` stays meaningful.
5. **SMT array encoding was the depth killer; `memory_map` fixed it.** The
   behavioral tag model (and any wrapper memory) was emitted as an SMT
   array whose per-step store chain made BMC grind to 1-5 min/step beyond
   ~step 45 (a depth-126 prove ran 75 min; depth 60 projected hours). The
   house apb4_slave_cdc script already runs yosys `memory_map` (memories ->
   discrete FFs, BV+ITE); adding that one line to the amber scripts took
   the model-free depth-126 liveness proof from multi-hour-projection to
   **80 seconds**, and the safety depth-60 from multi-hour to tens of
   minutes. Recorded as the encoding choice for all amber proofs.
6. **Checker-side bugs the proofs caught in my own harness** (fixed, not
   waived): (a) monotonicity mask inverted in pf wrapper; (b) victim mirror
   clear-priority; (c) snoop_resp ghost latched DT at FUB-accept while the
   RTL decides DT at the control grant (same-cycle `ctrl_crresp`); (d) pin-
   level CR checks ignored skid FIFO queuing — response N's CR can drain
   while grant N+1 relatches CRRESP; (e) AC/CR outstanding count needed
   >1 width (AXI back-to-back ACs pipelined through the skid). No RTL
   changes resulted — all four were proof-harness defects.

## sby run results

All proofs verified to contain their assertions/assumes/covers in the sby
model (`grep -c 'FLAVOR "assert"' model/design_smt2.smt2`) before accepting
a PASS — see Toolchain findings.

| Proof | Engine | Task | Depth | Result | Wall |
|---|---|---|---|---|---|
| amber_pending_fill_bypass | z3 (house) | prove | 25 | DONE (PASS) | ~2s |
| amber_pending_fill_bypass | z3 | cover | 40 | DONE (PASS) — `cp_mid_fill_match` @ step 4, `cp_full_lifecycle` @ step 11 | ~2s |
| amber_victim | z3 | prove | 20 | DONE (PASS) | ~2s |
| amber_victim | z3 | cover | 25 | DONE (PASS) — `cp_load_clear_reload` @ step 4 | ~2s |
| amber_snoop_resp | boolector (see note) | prove | 80 | DONE (PASS) | 28s |
| amber_snoop_resp | boolector | cover | 60 | DONE (PASS) — `cp_cr_only_response` @ 7, `cp_back_to_back` @ 8, `cp_dt_response` @ 9 | <1s |
| amber_control (safety, tag model) | boolector | prove | 126 | DONE (PASS) — non-vacuous (post fill-window fix), bound 104, recorded 2026-10-09 against current disk state (files unchanged since); final clean re-run (2026-10-10 11:34) died silently at step 55 (third death, notes c-d) — owner ruling 2026-10-10 accepts the recorded PASS as the verdict | 68 min with memory_map |
| amber_control (liveness, model-free) | boolector | prove | 126 | DONE (PASS) — bound 104 (honest worst ~95; ~9% margin); 80 s with memory_map | 80s |
| amber_control | boolector | cover | 80 | DONE (PASS) — all seven covers witnessed: cp_pf_grant @22, cp_pf_cd_beat @23, cp_pend_commit @32, cp_hits @35, cp_miss_rsp @36, cp_poisoned_lookup @39, cp_detour_drain @49 | 76s |

Notes: (a) the first depth-126 prove PASS (75 min) ran with the
unsatisfiable 6-cycle fill window and was **vacuous past the fill**; it is
superseded. (b) That 75 minutes was the cost of the SMT array encoding --
with `memory_map` (memories -> discrete FFs) the depth-126 liveness proof
completes in 80 s and the depth-126 safety proof reaches step 42 in under a
minute; the store chains, not the depth, were the wall. (c) An apparent
"wedged solver" incident during the safety run was collateral of the sby
task directory being deleted mid-run: the four amber Makefiles' `clean`
targets remove `*_prove/` dirs, and any second `sby -f` on the same task
also deletes the dir at start (demonstrably triggered by a relaunch during
this task). Run one sby instance per task directory at a time. (d) The
final clean re-run of the safety prove (2026-10-10 11:34, same config as
the recorded PASS) died silently a third time around 14:00: engine PIDs
gone, log stops mid-step at step 55 with no FAIL line, box load >10 from
unrelated workloads, no OOM evidence readable; cause unprovable, same
mechanism class as (c). With the non-vacuous PASS already recorded on
identical files, the owner ruled 2026-10-10 that it stands as the verdict
rather than re-running again.

Engine note: the house pattern names `smtbmc z3`. On the two DUT-closure
proofs z3 4.15.5 incremental shows measured exponential per-step growth
(0.09s / 0.47s / 33.6s at BMC depths 4 / 8 / 16; yices and z3-without-presat
no better) and cannot reach the required depths in any practical time —
and, worse, the shallow z3 ceiling HID two real harness bugs that boolector
at full depth exposed immediately (a DT-latch cycle mismatch and a liveness
timer that counted idle time). Boolector passes the full depths in seconds;
the pf/victim leaves kept house z3 (they pass quickly). Everything else —
tasks, options, script shape, flats flow, gate — is the gaxi_fifo_sync
house pattern verbatim. Recorded here as the per-proof smallest-sound-choice
deviation the brief asks to be documented.

## Step 4 divergence check (sim re-runs)

Harness assumptions in the proofs were checked against simulation by
re-running the Task 4–7 unit suites (no RTL was touched by this task, so
these confirm the proof environment did not drift from DV reality):

- `make run-amber_control-func` (Task 4 control suite; the
  amber_pending_fill_bypass and amber_victim integration scenarios run
  inside it — no standalone test files exist for the leaves, matching the
  RTL test headers): **4 passed**.
- `make run-amber_snoop_resp-func` (Task 7 closed-loop responder suite):
  **4 passed**.
- Whole-area divergence sweep `make run-all-func`: **274 passed, 0 failed**
  (3m01s) — the full amber area stays green, matching the pre-task state.
- All three re-run after the final proof-harness corrections (2026-10-10):
  `run-amber_control-func` 4 passed, `run-amber_snoop_resp-func` 4 passed,
  `run-all-func` **274 passed** again — the proof-environment fixes touched
  no RTL or DV, as intended.

## Gate

`python3 bin/formal_status.py --check-flats --staged` (from repo root,
venv active): **checked=4 CURRENT=4, exit 0** — amber_control,
amber_pending_fill_bypass, amber_snoop_resp, amber_victim all current.
Re-verified after every staging refresh; the pre-commit hook runs the same
command scoped to staged formal/ paths.

## The vacuity hazard this task caught (honest paragraph)

The first green prove was false comfort. The environment's fair-fill window
(6 cycles) was structurally incompatible with its own beat-ordering
constraint (8 in-order beats, all before done): the assumption set was
unsatisfiable beyond the fill launch, so the model had no completing
transactions and every property about fills, commits, replays, and
request-to-response liveness held vacuously on unreachable states. Nothing
in a green sby line reveals this -- BMC of an inconsistent constraint set
returns UNSAT for every assertion at every depth.

What caught it: the **cover task**, exactly as designed. Only the two
pre-fill covers (cp_pf_grant, cp_pf_cd_beat) were witnessable; every cover
requiring a completed transaction was unreachable -- direct evidence the
environment, not the RTL, was broken. The fix corrected the environment
model (fill window 6 -> 12, derived from the structural minimum of 9), the
dependent residence assertion (< 8 -> < 16) tracks the corrected window,
and the re-run closes the loop: all seven covers witness (completing
traces exist) AND the prove passes, so the assertions now hold on reachable
states. Rule recorded for future proofs: whenever a fair-window assumption
interacts with an ordering assumption, derive the window from the
structural minimum and let cover statements span the full transaction.

## RTL changes

None. The RTL under `projects/components/cache-ip/amber-mesi-l1/rtl/` is
untouched by this task; all defects found were in the proof harness and are
fixed there. The flats differ from raw sv2v output only by the documented
geometry specialization (constants, not behavior).

## Deviations

- `specialize_params.py` is a new house tool (documented above) -- required
  because neither bind nor expose works on parametrized targets in this
  yosys build. It is scoped to the amber formal area.
- pf/victim proofs have no bind/expose need and use the plain gaxi flow.
- Engines: control + snoop_resp run boolector (z3 infeasible at depth,
  measured); pf/victim keep house z3.
- Commit-path incident (ledger): the formal/amber batch was swept into an
  unrelated pushed commit (95ee1c8fe) when the shared index carried this
  task's staged set during another lane's commit. The content is at HEAD
  and reviewed as part of this task; no recommit was attempted.
