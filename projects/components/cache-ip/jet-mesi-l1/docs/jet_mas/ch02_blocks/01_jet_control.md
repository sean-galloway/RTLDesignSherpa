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
| `fill_*` / `drain_*` | out/in | engine launch/done |
| `cpl_*` | out | completions to `jet_rsp_seq` (seq tag, data) |
| `sn_*` | in/out | snoop service interface from `l1_snoop_resp` |
| `mon_*` | out | MonBus event taps (ch04) |
