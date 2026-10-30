<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# jet_control: Lookup/Commit Pipeline

**Status:** planned contract. `jet_control` replaces amber's blocking
`l1_control` FSM as the cache's control core. The arrays, replacement
engine, and snoop responder it drives are the unchanged `l1_*` FUBs.

## The split

Amber serializes everything through one FSM (LOOKUP → HIT_*/MISS_* → REPLAY
per transaction). jet splits control into two concurrent halves:

- **Lookup stage** — one request at a time: tag+state read on port A and
  the MSHR CAM match in the same window (the PoS, ch01). Outcome classes:
  `HIT`, `MISS_ALLOC`, `MERGE`, `STALL`.
- **Commit pipeline** — one fill completion at a time: merged store data
  written (amber D-4 write-merge at commit), tag install, MSHR retire,
  response handoff to `jet_rsp_seq`.

The two halves meet only through the arrays' write port (arbitrated, below)
and the MSHR file. Amber's global FSM states map onto per-entry progress:
each MSHR entry independently walks {allocated → fill launched → beats
landing → committing}; there is no global MISS_VICTIM/MISS_FILL state.

## Lookup classify (one request, one window)

Inputs: tag/state lookup (port A), MSHR CAM match, WB-buffer match, the
set's outstanding-victim-way claim count, and the oracle-equivalent state
decode from `l1_pkg`.

| Class | Condition | Action |
|---|---|---|
| HIT | line resident (S/E/M), no pending-fill hazard | serve from port A; write hits take the W port subject to fill-beat/commit-merge priority (J2); responses release in order |
| MERGE | line not resident, MSHR match, same class, entry not committing | append the request's sequence tag to the entry's merge list; no new traffic |
| MISS_ALLOC | line not resident, no MSHR match, resources free | allocate MSHR entry; claim victim way from `l1_repl`; if victim dirty, capture to WB buffer (J5); launch fill |
| STALL | MSHR full; or WB full AND dirty victim; or set oversubscribed (WAYS outstanding in this set); or cross-class wait (write miss behind a read fill, J3); or the matched entry is committing | hold the request at the front end; retried next cycle |

The STALL classes are the whole congestion story (J6): they never drop a
request, and each has a bounded release condition (an entry retires, a
drain completes, a fill commits).

## Commit pipeline

On `fill_done` for entry E (fill engine order = alloc order, single AXI4
read ID):

1. **Merge store data.** If E's requester (or any merged requester) is a
   write, its byte-enable merge lands on the just-filled beats (D-4
   semantics, identical to amber's).
2. **Install the tag** with E's install state — S, or M when PassDirty was
   received (amber's #106 rule), or M for a write fill.
3. **Apply deferred snoop effects.** Any snoop that hit E's pending entry
   recorded its post-commit effect (downgrade to S / invalidate to I) in
   the entry; it applies now, ordered after the install (amber's
   `pending` semantics from the gem5-derived oracle).
4. **Retire E** and hand the response data to `jet_rsp_seq` for every
   sequence tag on E's merge list.

## The anti-livelock hold-off (J4/Chinnakonda §10.9)

When an upgrade (CLEAN_UNIQUE) for line L completes, `jet_control` holds
off snoop service to L until the granted write's commit lands — a fixed,
small number of cycles, guaranteed by construction (the commit needs only
the W port for one beat and the tag port for one write). The hold-off never
extends past that commit; §8.2's "temporary block" permission is the whole
license, and ch05/01 carries the bounded-window formal property.

## Illegal states

The sticky CTRL_ERROR contract is inherited: a reserved state encoding or
an unreachable transition drops the pipeline to ERROR, exactly as amber's
(the DV illegal-state scenario pins it).

## Task 8 implementation notes (integration, as landed)

- **Sticky CTRL_ERROR, landed.** `ctrl_error_o` latches when the commit
  FSM or the snoop-service FSM presents a reserved encoding (the commit
  FSM's `default:` still recovers the state to `C_IDLE`; the flag is
  sticky).  While latched the lookup stage accepts nothing
  (`tag_req_o` gated) and `jet_top` dead-stops the GAXI boundary;
  reset is the only exit.  `test_jet_core.py::IllegalStateError` pins it
  (force a reserved `r_cmt_state`, observe the sticky
  `ctrl_state == AMBER_CTRL_ERROR`, recover through reset).
- **Killed-upgrade demote, landed** (closes the Task-7 known gap below):
  a snoop service that resolves an array hit on the in-flight upgrade's
  own line to Invalid now sets `r_upgr_killed`, and the CU commit
  installs I instead of blindly resurrecting M (`C_CU_INSTALL`).  The
  held write's response still echoes (the response tag was spent at the
  accept); the write's data is dropped with the invalidated line.  That
  last part is a fabric-contract corner, not a jet corner: the pair
  fabric's same-line serialization (the peer's snoop and our CLEAN_UNIQUE
  cannot interleave) keeps it off the rig — the demote is the defensive
  contract that turns a would-be silent M resurrection into a clean,
  visible Invalid.  `test_jet_core.py::KilledUpgrade` drives the corner
  through the real ACE port and scores the demoted install.  The same
  fabric argument covers the analogous killed-write-fill shape (a
  write-class fill whose pend_eff invalidates: responses echo, the merge
  data drops with the I install) — jet has no replay path by design
  (J4 re-sequencing replaces amber's replay), so these corners are
  documented demotes, not refetches.
- **The fill-engine contract moved to the launch level.**  The MAS text
  below assigns "start no beat stream while `cap_busy_o` is high" to the
  engine; the real `l1_fill` (single-outstanding
  F_IDLE→F_AR→F_R→F_DONE, no accept output, common-ip unchanged) cannot
  be gated, so `jet_top`'s launch adapter enforces it instead: a
  presented launch is accepted exactly when the engine is idle AND
  `cap_busy_o` is low AND the current cycle is not a dirty-victim alloc
  (the capture opens one cycle ahead of `cap_busy_o`).  Fills serialize
  through the one engine in launch order (the single-AXI4-read-ID
  contract); the adapter carries the in-flight fill's MSHR identity for
  beat routing.  Pinned by RTL assertions in `jet_top` and the
  `WindowedFillStart` scenario's every-cycle check.
- **The amber frontend needed a skid.**  `l1_cpu_frontend`'s pulse-style
  `req_valid` (presented only in a cycle `ctrl_req_ready` is already
  high) deadlocks jet's hold-until-accepted lookup and closes a
  combinational loop through the classify; a 2-deep `gaxi_fifo_sync`
  (DECISION D-6) between the frontend and the lookup stage holds the
  request until `lkup_ready_o`.  The response side backpressures
  `jet_rsp_seq` with the frontend staging FIFO's room (read-only
  `stage_wr_ready` tap) so a backed-up CPU channel cannot overflow the
  depth-2 staging queue.

## Task 5 implementation notes (lookup stage, as landed)

The lookup stage is combinational classify around a small amount of
sequential state (init walk, victim-capture engine, fill-launch hold,
drain-arbiter stub, upgrade tracker, claimed-way scoreboard) — there is no
global FSM; a stalled request is simply not accepted and retried next
cycle. Where the table above was silent, the landing pinned:

- **Upgrades classify at lookup.** An S-write hit launches `JET_CLS_CU`
  (jet_pkg extension) to the fill engine; no MSHR entry, no victim. One
  upgrade is outstanding at a time (single tracker), and the upgrade's
  (set, way) counts as a claim for victim selection. Task 6 made the
  tracker hold the full request context (seq tag, beat, be, wdata) and
  clear it only at the upgrade's own CU commit, qualified by the
  completing fill's identity through the completion queue.
- **The pending-fill hazard is a claimed-way scoreboard** in jet_control
  (per live MSHR entry: the claimed set+way). A tag hit on a claimed way
  is suppressed (the doomed victim's data is being captured/overwritten)
  and the request falls to the miss path.
- **The WB drain race is a STALL** under the `wb_full_dirty_victim`
  reason: a miss whose line sits in the WB buffer (or is mid-capture)
  waits for the drain — the refetch must not race the outstanding
  writeback (§10.10.1). Bounded by the drain.
- **Write-hit W-port yield is a hold, not an accept**: during a fill beat
  stream the write hit is simply not accepted (`lkup_wr_yield_o` marks
  it); it retries next cycle and lands when the stream releases the port.
- **Merge-list full** (an entry already carrying MSHR_COUNT requesters)
  stalls `mshr_full`.
- **The fill launch is a one-deep hold register** (`fill_start` held until
  `fill_accept`); an alloc/upgrade with the register occupied holds (not a
  congestion stall).
- **Fill-engine contract:** the engine must not write an entry's fill
  beats before that entry's victim capture has completed
  (`cap_busy_o` low) — the beats land in the claimed victim way.
- **Victim policy is updated at the alloc** (claim == the update); the
  commit must not `repl_update` again at install.
- **The victim proposal is claim-aware** (Task 6): a proposed victim way
  already claimed by a live entry of the set stalls the alloc
  (`set_oversubscribed`; release: the conflicting entry's commit).
  `l1_repl` has no claim-mask input (common-ip is shared), so the check
  lives in jet_control — it makes RANDOM (which can repeat a way) and LRU
  under hit reordering (which can re-propose a claimed way once every
  other way has been touched) safe. A `translate_off` assertion pins that
  no two live claims ever share a (set, way).
- **jet_mshr** grew the overlay-free lookup probe
  (`lkup_reg_match_o/idx/cls`): the classify drives the alloc from the
  match outcome, so it must see the registered-entries-only match or the
  two would form a combinational loop through the alloc-first overlay.
  Two `translate_off` assertions pin the integration: a granted alloc
  never duplicates a live entry's line, and `alloc_set_i` is always the
  alloc line's own set field.
- **jet_rsp_seq** orders release before deposit in its sequential block:
  when the ring is full and a release frees the head slot, the freed tag
  is re-granted in the same cycle and the lookup stage may deposit the new
  request's hit completion immediately — the deposit must survive the
  release (the old record's response left on the wire that cycle).

## Task 6 implementation notes (commit pipeline, as landed)

The commit pipeline is a small FSM (C_MERGE → C_INSTALL → [C_PEND] →
C_DEPOSIT → C_RETIRE, plus the CU tail C_CU_MERGE → C_CU_INSTALL →
C_CU_DEPOSIT) fed by a **fill-completion queue**: every fill launch
(alloc or upgrade) is pushed at `fill_accept`, and `fill_done` marks the
oldest un-done entry — the single AXI4 read ID completes fills in launch
order, so the queue resolves each `fill_done` to its entry/upgrade
identity without a done-side index. Where the commit section above was
silent, the landing pinned:

- **The entry context is snapshot at the commit start** (one cycle; the
  jet_mshr commit read port is otherwise the lookup stage's merge-room
  probe, so merges hold for that cycle). The merge list is frozen from
  the cycle after `fill_done` (a merge landing on the done cycle itself
  is still appended and included in the snapshot); a merge onto a
  fill-done entry stalls `commit_in_progress` (release: the retire).
- **Store data lives in a jet_control sideband** (per entry, per
  merge-list slot: we/beat/be/wdata, recorded at the alloc/merge
  accepts). The MSHR stays a MAB — it holds no data.
- **A read requester's response beat is captured from the data array at
  its own position in the requester order** (during the D-4 walk), so a
  read observes exactly the writes that precede it and never a later one;
  deposits then replay the captured beats in tag order.
- **pend_eff is a second tag write after the install** (C_PEND), so the
  order is observable and pinned by DV; the claimed way stays claimed
  until the retire, keeping hits on the committing line suppressed (they
  fall to the MSHR match and stall `commit_in_progress`).
- **Any hit on the in-flight upgrade's line stalls** (`cross_class_wait`)
  until the CU commit lands — the held write's data merges only there,
  so a read overtaking it would return stale data.
- **The commit wins the deposit port; hit accepts hold** in deposit-phase
  cycles (bounded by the merge-list depth; no deposit is ever dropped).
  The data W port orders fill beats > commit store merge > write-hit
  merge, the tag W port orders init > commit install/pend > E→M
  promotion, and the port-A read address is the commit's during the
  read-capture cycles (read hits hold).
- **A CU commit** merges the held write onto the resident line (D-4),
  installs M, echoes the write data as the response, and clears the
  upgrade tracker.

## Task 7 implementation notes (snoop path, as landed)

The snoop service is a small side FSM (SN_DATA beat stream → SN_EFFECT
effect slot) around a combinational grant-cycle resolution, on the
`l1_snoop_resp` core-facing contract (the AC accept cycle IS the grant —
the transport latches the CRRESP that cycle, so every deferral is through
`sn_safe_o`, which must be address-agnostic: an address-dependent safe
would close a combinational loop through the transport's accept mux).
Where the contract text was silent, the landing pinned:

- **Match order WB > MSHR > array**, combinational at the grant.  The
  WB∩MSHR same-line double match (rule 4) is *unreachable*: a refetch of
  a WB-resident line stalls on the drain race (Task 5), so no MSHR entry
  can name a line the buffer holds; the WB-first order is defensive.
- **PF_GUARD is a grant-time deliverability gate**: a pending-fill answer
  promises DataTransfer/PassDirty only when every fill beat has landed
  (`&beats_rcvd`); the guarded answer keeps the post-fill row's
  IsShared/WasUnique (never the Invalid row) and streams nothing.  A
  pending fill's post-fill state is M for an RU fill, S for RNSD
  (`sn_install`); PassDirty never disturbs this — the bypass answers
  before the RRESP exists, exactly as amber's pf load-time state.
- **The anti-livelock hold-off is the commit-window gate, not a counter**:
  `sn_safe_o` covers the CU's grant cycle itself (the completing fill's
  class resolves combinationally through the completion queue) and every
  cycle a fill is done-but-unretired (`r_fq_cnt != r_fq_undone`, which
  also covers the active commit — the pop lands at the retire).  The
  bound is the CU commit's own length (grant → C_CU_MERGE → C_CU_INSTALL
  → C_CU_DEPOSIT: 5 cycles with nothing queued), guaranteed by
  construction, never event-dependent; the window closes at the pop, two
  cycles past the tag install.  DV measures it (`anti_livelock_window`).
  Precision on the aggregate (RESOLVED in Task 11): `w_any_done` re-arms
  on every `fill_done`, so a sustained max-rate fill stream can hold
  `sn_safe_o` low for as long as the stream continues — the per-window
  bound holds, but the aggregate was workload-dependent and the formal
  liveness harness (L3) produced a 113-cycle starvation counterexample
  that is scale-free in the fill rate.  The fix is the pending-snoop
  throttle below: with new CPU accepts blocked, no new fills allocate,
  the outstanding fills (≤ MSHR_COUNT) complete and commit in bounded
  time, and `w_any_done` clears — the aggregate snoop wait is now bounded
  by the pipe drain (fills × commit length + capture windows), never by
  the workload.
- **The commit never runs during a snoop service** (C_IDLE start gated on
  the service idle): a pend record for the about-to-commit entry lands
  before the snapshot, and SN_EFFECT's tag write is contention-free.
  Both directions are bounded (service ≤ FILL_BEATS+2 cycles; a commit
  start waits at most one service), so the interlock is liveness-clean.
- **The other bounded `sn_safe_o` windows**: the init walk, an active
  service (one snoop at a time, inherited), and a victim capture
  streaming on port B (a snoop to a mid-capture dirty victim cannot be
  served yet — the WB entry validates at capture completion; unrelated
  snoops are held with it because safe is address-agnostic; bounded by
  FILL_BEATS plus any in-flight snoop stream).  Snoop acceptance never
  gates on WB occupancy, fill state, or drain state
  (`snoop_never_waits_on_wb_full`).
- **A WB snarf snapshots the whole line at the grant** — the entry may
  retire mid-stream in its BRESP cycle (the ships-in-the-night corner);
  the stream serves the snapshot.  An array/MSHR stream reads the data
  array on port B (the fill's claimed way for a pending fill), pausing
  the victim capture (jet_wb_buffer tolerates the pause; bounded by the
  service length).
- **pend_eff I-sticks lives in the sn_eff drive**: the record port write
  is unconditional in jet_mshr, so the priority (an armed invalidate
  dominates a later downgrade) is resolved here via a per-entry shadow
  (`r_sn_pend`, cleared at the alloc; exact because this module is the
  record's only driver).  `snoop_hit_pending_entry` pins it.
- **Snoop priority over new CPU accepts** is a hold, not a stall: the
  lookup stage accepts nothing from the grant through SN_EFFECT (bounded
  by the service length — FILL_BEATS+2 in CD *handshakes*, extended by
  cdready backpressure, which the fabric legitimately applies), so the
  snoop's port-B/CRRESP view is race-free.  Since Task 11 the hold starts
  EARLIER: a *pending* snoop (`sn_want_i` — an AC valid at the transport,
  granted or not) throttles new accepts while the safe window is still
  closed, so the commit-window aggregate above can never starve the
  snoop.  The throttle gates only the classify accept — the commit
  pipeline, fill beats, WB capture/drain, and an in-progress service
  never depend on new accepts — and the remaining `sn_safe_o` terms stay
  bounded under it (`r_cap_busy` is one ≤FILL_BEATS-beat capture per
  dirty-victim commit and no new allocs means no new captures;
  `w_cu_completing` is the single CU grant cycle — the hold-off above is
  unchanged).  `jet_top`/`jet_ace_top` derive `sn_want_i` from a registered count of
  AC handshakes not yet granted (the transport's skid hides an accepted
  AC from the pins, and a combinational AC-valid tap would close a
  combinational loop through the fabric).  DV pins the bound under sustained miss streaming
  (`snoop_starvation_bound`); the formal harness proves it (L3).
- **Known gap — RESOLVED in Task 8** (kept for the record): a snoop to
  the *in-flight upgrade's own line* before the CU grant is served at
  the installed S; the effect is now carried by `r_upgr_killed` and the
  CU commit demotes to I (see the Task-8 notes above).  The pair
  fabric's same-line serialization keeps the corner off the rig; the
  demote is the defensive contract, pinned by `KilledUpgrade` in the
  core TB.


## W-port arbitration

One write port feeds: fill beats (fill engine), hit/merged store data
(port A writes), WB capture reads are on port B. Priority: **fill beats >
commit store merge > write hits** (J2): a fill once in its beat stream
finishes it (bounded: FILL_BEATS cycles), then commit merges (bounded by
the merge-list depth), then write hits proceed. This is the liveness-safe
order — fills retiring is what frees MSHR entries. The tag write port
orders init walk > commit install/pend > E→M promotion, and the response
deposit port orders commit deposits > hit deposits; the held side retries
next cycle (all holds bounded, no deposit is ever dropped).

## Interface sketch (planned)

| Signal group | Dir | Content |
|---|---|---|
| `lkup_*` | in | request from the front end (addr, we, be, wdata, seq tag) |
| `lkup_rsp_*` | out | hit data / accept-stall to the front end |
| `tag_*` / `dat_*` | out/in | array port A drive/read |
| `repl_*` | out/in | victim request/way from `l1_repl` |
| `mshr_*` | out/in | alloc/match/retire to `jet_mshr` |
| `wb_*` | out/in | capture/drain-status to `jet_wb_buffer` |
| `fill_*` / `drain_*` | out/in | engine launch/done (incl. `fill_ar_done_i`, the AR-acceptance progress input of the Task-9 pre-AR snoop rule — ch02/05) |
| `cpl_*` | out | completions to `jet_rsp_seq` (seq tag, data) |
| `sn_*` | in/out | snoop service interface from `l1_snoop_resp` |
| `mon_*` | out | MonBus event taps (ch04) |
