# TASK-022: the byte-granular RAPIDS has no formal proofs of its own

**Priority:** P2 -- the product tree is unproven while the stepping stone is
proven. Not urgent (the byte tree is board-characterized and its suites are
green), but it is the largest coverage gap the rapids TASK-019 closure exposed.
**Status:** CLOSED 2026-10-04. Both macro dirs prove green (snk depth 15,
src depth 16), mutation batteries done, suite-wide prove/cover re-run green
2026-10-04. Scope DECIDED 2026-10-02 -- see "Decide first".
**Owner:** TBD

## The gap

`formal/rapids/` holds 11 proof directories. **Nine are `*_beats`**; the only
un-suffixed ones are `ctrlrd_engine` and `ctrlwr_engine`, which both trees
share. So every proof that is specific to a design proves the beat-granular
stepping stone -- the tree rapids TASK-019 explicitly described as "kept
runnable and green, not maintained forward".

Nothing proves `scheduler.sv`, `axi_read_engine.sv`, `axi_write_engine.sv`,
`snk_data_path_axis.sv`, `src_data_path_axis.sv`, `alloc_ctrl`, `drain_ctrl`,
`descriptor_engine` or the byte SRAM controllers.

**Census of all 23 byte modules against `formal/rapids` (measured by the
RLB-cleanup session, 2026-10-01), which widens this gap beyond how it was
first filed:**

| Group | Count |
|---|---:|
| proven, and only because `ctrlrd`/`ctrlwr` are shared | 2 |
| the `_beats` twin is proven, the byte one is not | 9 |
| **UNPROVEN IN BOTH TREES** | **12** |

The twelve are `scheduler_group`, `scheduler_group_array`, `rapids_core`,
`rapids_snk`, `rapids_src`, `snk`/`src_data_path`, `snk`/`src_data_path_axis`,
the two `_axis_test` wrappers, and `monbus_axil_group_2in` (no beats twin at
all; shared, like ctrlrd/ctrlwr). **The macro level has never been proven in
either granularity.** So the beats suite covers 9 of the 21 non-shared modules,
and this is not "the byte tree is unproven while the stepping stone is proven"
-- more than half the tree is unproven at any granularity. That also settles
"Decide first" on arithmetic: porting the nine cannot reach even half the gap,
and the twelve have nothing to port from.

Also missing from the original list: the byte `latency_bridge` (`rtl/fub/`) is
unproven while `latency_bridge_beats` has a proof. Deprioritise it, though --
NEITHER latency_bridge is instantiated in any design. `latency_bridge` appears
only in `dv/tb/latency_bridge_tb_top.sv` and `latency_bridge_beats` only in its
own TB plus its formal wrapper; the beats top closure is 69 sources with no
latency_bridge in it, and STREAM has its own `stream_latency_bridge`.

## Why it matters more than a straight port would suggest

The byte tree is not the beats tree with wider counters. It added logic that
has no beats equivalent, and it is exactly the kind of logic formal is good at:

- the ingress barrel shifter and its spill/hold across memory beats, plus the
  mirror shifter on egress -- a byte-placement invariant, and the kind of thing
  a directed test samples rather than proves;
- the packet-record queue and its ready contract (`s_axis_tready` held low
  until a channel's record exists), which is a liveness property;
- WSTRB generation from offset and remaining length, and the first/last-beat
  masking -- a sizing invariant over the 4 KB boundary split;
- per-channel reset reaching every latching stage (the rapids TASK-019
  channel-reset work), where "a channel recovers without aresetn" is a property,
  not a test case.

## Decide first

- [x] scope: DECIDED 2026-10-02 (Sean) -- the smaller set aimed at the
      byte-specific logic above, not a port of the nine. The arithmetic in
      the census settles it: porting cannot reach half the gap, and the
      twelve have nothing to port from.
- [ ] does the beats formal suite stay once the byte proofs exist? DEFERRED
      2026-10-02 -- decide when the byte proofs exist; the answer should
      match how long the beats tree itself stays.
- [x] proof mechanism: DECIDED 2026-10-02 (Sean) -- PORT-LEVEL HARNESS ONLY.
      No new in-RTL properties of any kind; internal invariants are restated
      at module boundaries or the signal is exposed. This matches the only
      mechanism that has ever worked in this tree (see the finding below).
- [x] the 64 existing in-RTL concurrent assertions: DECIDED 2026-10-02 (Sean)
      -- DELETE all 64 (32 per tree, 14 files). Dead text whose maintenance
      cost was already paid (the arbiter-request comment); nothing compiles
      them and nothing may start to.
      **DONE 2026-10-01, commit bf5db01b7** (Workstream A). Census correction
      recorded there: the split was 40 byte-tree / 24 beats-tree, not 32/32
      (fub_beats has no ctrlrd/ctrlwr). Zero `ifdef FORMAL` blocks and zero
      real `assert property` remain in the RAPIDS trees; STREAM's own
      `axi_read_engine.sv:643-661` block is outside the 64 and survives.
      Residue closed 2026-10-02: the doc generator's citation gate was broken
      by the deletion's line drift (23 tuples + prose refs); renumbered
      mechanically, `gen_rapids_signal_contracts_kmaps.py` exits 0 again.

## Done when

- [x] `formal/rapids/snk_data_path_axis/` proves the byte sink macro (shifter +
  packet-record queue + fill allocator + write engine closure) at port level:
  byte fidelity, record/ready contract, AW/W legality, per-channel reset.
  DONE 2026-10-03 (commit 958687317, depth 15).
- [x] `formal/rapids/src_data_path_axis/` proves the mirror on the source side.
  DONE 2026-10-04 (commit f26b893f5, depth 16).
- [x] If the macro dirs blow the measured budget (Sean's call at the DIR-1
  checkpoint): `formal/rapids/axi_write_engine/` at fub level instead.
  NOT NEEDED -- both macro dirs held the budget.
- [x] Mutation check per property; each `ap_*` present in the emitted smt2;
  `make -C formal/rapids prove-all` and `cover-all` green; flats regenerated
  from current RTL and git-diff clean. DONE 2026-10-04: snk 16/16 + src 21/21
  `ap_*` in the emitted smt2; all 13 flats CURRENT; 13/13 covers and 13/13
  proves green (src_data_path_axis via its committed depth-16 run, the other
  12 re-run live this day).
- Adjacent gap, OUT OF SCOPE here: `axi_read_engine` AR-side legality
  (4 KB split etc.) has no byte-tree proof; file separately if wanted.
- Beats-suite retirement stays DEFERRED (see "Decide first").

## Notes

- DIR 1 status 2026-10-02 — **DONE, committed 2026-10-03**: harness + flat +
  Makefile + .sby; 16 `ap_*` + 12 `cp_*`. **Prove depth 15 PASS in 1:04:09**
  (bitwuzla, single core; step 13 ~24 min, step 14 ~40 min of it). Cover
  depth 40 re-run same day: 12/12 `cp_*` reached, deepest witness step 14.
  smt2 re-grep on the final run: 16/16 `ap_*` present (see the grep trap at
  the end of this note). Earlier that day: **Prove
  depth 14 PASS in 26 min** (bitwuzla, single core). Cover depth 40 PASS in
  27 s; deepest witness step 14 (cp_kill_inflight). sby depth semantics,
  measured this session: `depth N` checks steps 0..N-1 (the depth-14 log's
  last "Checking assertions" is step 13), so a CEX at step 14 is exactly one
  past a depth-14 bound. With the full shadow state the per-step cost
  explodes past step 12 (~16 min at step 14, ~27 at 13 on a loaded box;
  depth 16 > 2 h), and the probe's "depth 50 in 38 s" figure did not survive
  the shadow packet queue + per-beat expectation FIFO. Three CEX loops were
  real harness bugs, not DUT bugs: PQ slot recycling (pop frees slots
  before W drains), lazy-pop push indexing, and the fill-vs-drain ordering
  insight -- the DUT forms a memory beat at EVERY accept (mid-packet
  included), so expectations are captured per beat at FILL time. smt2 grep:
  all 16 `ap_*` present, none dropped. Mutation battery (7 breaks): 6
  CAUGHT in-budget -- tstrb-shift (ap_wstrb_eq_shadow@11), hold-load-zero
  (ap_byte_equality@13), tready-no-record (ap_tready_needs_record@2),
  4k-cap (ap_aw_4k@10), wlast-early (ap_wlast_count@11), BUG-014-revert
  (ap_tready_needs_record@4); the 7th, dropping the hold-OR, was NOT caught
  at depth 14 -- **RESOLVED: rerun at depth 17 CAUGHT ap_byte_equality at
  step 14**, one step past the old bound, i.e. a depth artifact, not a
  property hole (that mutation corrupts only INTERMEDIATE beats of 3+-beat
  packets; first beats are unshifted and spill flush beats take r_hold_data
  directly). Prove depth therefore re-pinned 14 -> 15 so the deepest witness
  and every observed CEX are in-budget -- and the depth-15 re-prove then
  PASSED, so the pin is verified, not assumed.
- DIR 2 status 2026-10-03 — harness + flat + Makefile + .sby exist (untracked
  until the close commit); cover depth 40 PASS (12/12). Prove FAILED at step 13
  on `ap_strb_eq_shadow_1b`. **Root cause: a harness modeling bug, not a DUT
  bug.** The trace showed the DUT popping its record queue at a packet's EMIT
  (its count one lower during the final beat's presentation) while the shadow
  popped at the HANDSHAKE; with the shadow queue full, a legal push during a
  stalled final beat wrapped the shadow write pointer onto the occupied head
  slot and overwrote the in-flight packet's record (head bytes changed 2 -> 16
  mid-presentation; the first-beat expectation then mismatched). Fix: shadow
  storage depth 4 -> 8 (max legal occupancy is DUT depth 4 + skew 1 = 5; the
  wrap onto an un-popped slot becomes unreachable). PQD itself is unchanged —
  `ap_pq_ready_eq` still models the DUT's own depth-4 queue exactly, and the
  pop timing stays handshake-based, so no other assertion or cover moved.
- CEX #2, same session: after the PQ fix the prove still failed at step 13,
  now on the MID-packet `ap_strb_eq_shadow` -- a second, independent harness
  bug. The first-beat branch set `s_emit_i <= 0`, but s_emit_i is the index of
  the NEXT expected emit, so every mid-packet beat was checked against the
  closed form one emit low (a 12-byte off=0 packet's second beat: predicted
  pop 0 / 8 lanes; DUT emitted pop 1 / 4 lanes). The completing-beat
  snapshot's `s_emit_i + 1` had masked this at captures, and the bug was
  unreachable before ~step 13 because the AR->R->SRAM->drain->emit latency
  puts every SECOND beat at step ~12-13 -- which is also why DIR 1's battery
  never saw it. Fix: `s_emit_i <= 4'd1` in the first-beat branch (the
  single-beat retire sub-branch is unaffected: s_emit_i is only read while
  s_pkt_act). Both fixes are in the close commit.
- DIR 2 close 2026-10-04 — **Prove depth 16 PASS in 1:45:45** (bitwuzla,
  single core; step 14 ~40 min, step 15 ~58 min of it). smt2 re-grep on the
  final run: 21/21 `ap_*` present -- DIR 2 carries 21 properties (DIR 1 has
  16); the `ap_beats` trap name is the DUT's `w_cap_beats` wire here too.
  Mutation battery, 6 breaks all CAUGHT: strb_invert_v2
  (ap_byte_total_1b + ap_strb_eq_shadow_1b), hold_load_zero
  (ap_byte_equality_1b @14), ready_forced (ap_pq_ready_eq @6), cap4k_break
  (ap_ar_4k @6), arlen_cfg_break (ap_arlen_caps @5), pop_during_reset
  (ap_out_needs_rec + ap_reset_no_new_out). A 7th candidate,
  emit_without_record, was dropped as architecturally ineffective -- the
  mutation is port-unobservable (DUT and shadow read the same stale slot)
  -- and replaced by ready_forced. Cover depth 40 PASS, 12/12 `cp_*`,
  deepest witness step 14 (cp_flush/cp_hold_prime/cp_interleave).
- smt2 grep trap, measured 2026-10-02: `grep -o 'ap_[a-z0-9_]*' design_smt2.smt2`
  returns a 17th name, `ap_beats` -- that is the DUT's `w_cap_beats` wire
  (axi_write_engine), not a property. The property count is 16.
- Flat-file discipline applies from day one: a committed sv2v snapshot that is
  not regenerated leaves a proof green against RTL that no longer exists. That
  has already happened in this area -- rapids BUG-011.
- `vault/handbook` has the formal method (sv2v flatten, in-RTL ifdef FORMAL
  properties, mutation-checking every new assertion, harness vacuity traps);
  this task does not restate it.

## Finding 2026-10-01: the 64 in-RTL properties have never been compiled

Measured by the RLB-cleanup session while scoping this task, in both trees;
the three structural checks independently reproduced here.

**`ctrlrd_engine` is the whole finding in one line:** it has a PASSING formal
proof, its source carries 8 `assert property` statements, and its flat contains
**zero**. Its Makefile passes no `--define=FORMAL`, so the `ifdef FORMAL` block
is never compiled. The proof is its harness's properties and nothing else.

That generalises:

- **64 concurrent `assert property` statements across 14 files**, 32 per tree,
  symmetric. fub/: axi_read_engine 4, axi_write_engine 5, ctrlrd_engine 8,
  ctrlwr_engine 8, descriptor_engine 6, scheduler 3; macro/: scheduler_group 4,
  scheduler_group_array 2 -- and the identical counts in every `_beats` twin.
- **0 of 11 rapids proof Makefiles pass `--define=FORMAL`.** Not one outlier --
  none of them.
- **No committed `*_flat.v` anywhere under `formal/` contains `assert
  property`.** Repo-wide the figure is 103 across 27 files; rapids is 64 of them.

### It is not a forgotten flag

Both sv2v settings were tried and neither carries these properties:

- **WITH `--exclude=Assert`**: sv2v passes the SVA through verbatim and yosys
  rejects it -- `syntax error, unexpected '@'` at the first assertion. Adding
  `-sv` to `read_verilog` does not help; `disable iff` and `|->` are beyond the
  frontend.
- **WITHOUT it**: sv2v deletes them silently. The flat goes from 4 assertions to
  0, and the proof then passes while checking nothing.

The second is the dangerous half, because it looks like success.

**Immediate vs concurrent is the dividing line** (verified here): 22 committed
`*_flat.v` files DO contain an immediate `assert(...)`, and 0 contain `assert
property`. So immediate assertions survive sv2v into the flats and concurrent
SVA does not -- which is why a rule that says "in-RTL properties are compiled
and checked" is half true and misleading.

### The cost is real and already paid

`axi_read_engine`'s block carries a comment explaining that the arbiter now sees
`r_arb_request` rather than the live `w_arb_request` "after the request pipeline
added for 8-channel 100 MHz timing closure". Someone reasoned about a property's
correctness through a timing change that could never have been checked. That is
maintenance spent with no coverage returned.

### Consequence for this task's scope

The byte-specific invariants this task exists for -- the ingress barrel shifter's
hold/spill, the packet-record ready contract, WSTRB generation across the 4 KB
split -- are all internal, and the only mechanism that has ever worked in this
tree is the port-level `formal_<block>.sv` harness. So an internal property needs
either the signal exposed on the boundary or the property restated at it. That
constraint should be settled before any proof is written, not discovered during.

It is also the route Sean's 2026-09-03 decision requires. **Two questions are
with Sean:** whether NEW internal properties are permitted at all, and what
becomes of the 64 existing ones -- delete, convert to harness properties, or keep
as documentation. The second is new information for that decision: in this tree
RTL assertions break no tool, because nothing compiles them.

### Method note

Count `assert property` with comment lines excluded --
`grep -E "assert property" FILE | grep -vE "^\s*(//|\*|/\*)"` -- and require the
file to contain an `ifdef FORMAL` block. A plain grep counts prose: `drain_ctrl`
and `drain_ctrl_beats` each contain the string once, inside a comment saying the
author deliberately used a procedural check instead. (This caught me: I "corrected"
64 to 66 off an unfiltered grep, and the two extra hits were that comment.)

Handbook: `vault/handbook/dv/formal.md` (985bc3b4b) now carries the general rule.
