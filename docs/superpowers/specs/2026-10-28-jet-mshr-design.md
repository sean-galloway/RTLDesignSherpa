# jet-mshr — lockup-free MESI L1 (amber + MSHRs)

Date: 2026-10-28
Status: DRAFT for owner review
Applies to: `projects/components/cache-ip/jet-mesi-l1/` (+ reuse of
`cache-ip/common-ip/` primitives, unchanged)

## Goal

Implement jet: the lockup-free upgrade of amber, per the J1–J7 rulings
recorded in `jet-mesi-l1/PRD.md` v0.2 and the jet HAS v0.3 (both closed
2026-10-28). Amber's coherence protocol, arrays, interfaces, and
observation carry over unchanged; jet adds the MSHR file, hit-under-miss,
miss merging, and a decoupled writeback path — and measures the delta.

## The rulings (one line each, PRD is binding)

- **J1** — MSHRs: fully associative CAM keyed by line address; `MSHR_COUNT`
  2–16, default 4.
- **J2** — hit-under-miss: reads AND writes to any resident line during
  fills; W port arbitrates fill beats over write hits.
- **J3** — merge: exact-line aliases only, same class joins, cross-class
  waits for commit then proceeds (no escalation).
- **J4** — ordering: out-of-order internal completion, in-issue-order CPU
  responses (GAXI has no IDs); snoop-on-pending-line answered at the
  post-fill state by a per-entry bypass (PF_GUARD semantics).
- **J5** — eviction: dirty victim captured to a global writeback buffer at
  miss start; fill proceeds immediately; drains retire oldest-first;
  `VICTIM_DEPTH` 1–4, default 2.
- **J6** — congestion: strict stall (MSHR-full stalls new misses, WB-full
  stalls only dirty-victim misses); snoops arbitrate ahead of new CPU
  accepts.
- **J7** — the claim: amber's cache_sim trace suite + Genesys2 pair rig,
  identical traces, four MonBus metrics (hit-latency distribution under a
  miss stream, MSHR occupancy histogram, sustained fill bandwidth,
  drain/fill overlap), `MSHR_COUNT` swept 2/4/8/16.

## Non-goals (YAGNI)

- Multiple AXI4 read IDs / parallel fills on the memory port (see "fill
  serialization" below) — a future elaboration, not v1.
- Speculative prefetch, adaptive replacement, QoS, multi-banked parallelism
  beyond the MSHRs (PRD non-goals).
- MOESI O-state, directories, ACE DVM/barriers (amber non-goals, inherited).
- No changes to amber's RTL. Common-ip primitives are reused as-is; anything
  jet needs that amber doesn't have is new jet RTL, not an amber edit.

## Design

### 0. Reuse inventory (from `cache-ip/common-ip/rtl/`, unchanged)

`l1_pkg` (state encodings, CRRESP decode, fill classes), `l1_tag_array`,
`l1_data_array` (2R+1W), `l1_repl` (LRU/PLRU/FIFO/RANDOM), `l1_fill` (AXI4
read-master fill engine), `l1_drain` (AXI4 write-master drain engine),
`l1_pending_fill_bypass`, `l1_monlite`. Amber's `amber_ace_issue` pattern is
the model for jet's ACE-facing request issue; `amber_pair_fabric` hosts the
pair rig unchanged (two jets instead of two ambers).

### 1. `jet_mshr` — the CAM file (J1)

One row per outstanding miss:

```
{ valid, line_addr, fill_class (RNSD/RU), expected_install_state,
  victim_wb_slot, merge_list (requester seq tags), fill_beats_rcvd }
```

Ops: `alloc` (new miss), `match` (exact-line CAM — used by merge, by the
hit/pending hazard exclusion, and by the snoop bypass), `retire` (fill
committed). Allocation stalls when full (J6). No aging: a fill once started
always retires, so liveness reduces to fill-engine progress.

### 2. Miss flow and fill serialization (honest scope note)

Amber's single AXI4 read master (one ID) means **fill data returns in AR
issue order** — fills serialize on the memory port regardless of MSHR
count. Jet's concurrency win comes from the three places amber blocked:

1. hits (reads+writes) proceed while fills are outstanding (J2);
2. aliases merge instead of re-fetching (J3);
3. dirty victims drain decoupled from the fill they were evicted for (J5).

MSHRs let the cache *accept and queue* misses back-to-back so the fill
engine never goes idle between unrelated misses (AR pipelining), which is
where the bandwidth win comes from at this serialization. Parallel fills
(multi-ID) are a measured future step if the sweep shows the memory port is
the residual bottleneck — the J7 occupancy histogram tells us.

### 3. `jet_wb_buffer` — writeback buffer (J5)

`VICTIM_DEPTH` rows of `{valid, line_addr, data, state}`. A dirty victim is
captured (`victim_load`) when its miss allocates; the fill proceeds without
waiting for the drain. The drain engine empties the buffer oldest-first,
independent of fill state. Snoops hitting a buffered victim are served from
the buffer with amber's SINK_WB_ACK semantics. WB-full stalls only new
dirty-victim misses.

### 4. `jet_rsp_seq` — response sequencer (J4)

CPU requests take a sequence tag at accept. Responses (hit data, fill
commit replays, merged requesters) release to the GAXI response port in tag
order; internal completion is out of order. Depth = max in-flight CPU
requests = `MSHR_COUNT` + hit pipeline depth.

### 5. Snoop path (J4/J5)

Amber's pending-fill bypass generalizes to N entries: AC address matches
the MSHR CAM → answer at the entry's expected post-fill state (PF_GUARD:
only when the fill can actually deliver), snoop's state effect applied
post-commit. WB-buffer match → SINK_WB_ACK service from the buffer.
Neither path ever stalls the snoop behind a fill or drain (Chinnakonda
§7.8). Snoops arbitrate ahead of new CPU accepts (J6).

### 6. `jet_control` — the restructured core

Amber's blocking FSM (LOOKUP→…→REPLAY per transaction) becomes: a lookup
stage that classifies each accepted request (hit / miss-alloc / merge /
stall), N in-flight miss contexts tracked by `jet_mshr`, and the commit
logic (tag write + data writeback of merged writes + response enqueue).
The amber control FSM's *per-transaction* states map onto per-MSHR-entry
progress instead of a global pipeline state. The gem5-derived FSM oracle
(`amber_fsm_oracle`) still pins coherence semantics per line — that model
is timing-free and carries over unchanged.

### 7. Observation (J7 feed)

Existing monlite taps (hits, misses, snoops, evictions, transitions) plus
jet adds: MSHR alloc/merge/retire events and a current-occupancy gauge,
WB-buffer occupancy, response-queue stalls. Same 128-bit MonBus packets,
same tally agents.

### 8. Formal targets (tiny 16-set/2-way geometry, per amber D9)

- J5/J6 liveness: oldest-entry progress, drain progress, snoop progress,
  and the composed corner (MSHR-full + WB-full + snoops pending →
  progress).
- Inherited safety re-run with MSHRs present: the `ap_grant_crresp`-class
  decode pins and the pending-fill-bypass invariants, generalized per
  entry.

## DV plan

Mirror amber's ladder: `jet_mshr` and `jet_wb_buffer` unit TBs →
`jet_control` core TB → `jet_top` / pair rig. The control TB reuses
`AmberControlTB` machinery (monitor, LRU model, oracle_step, snoop driver)
with the per-transaction slice checks replaced by an event-stream
scoreboard: per-line coherence checks stay lockstep against the oracle;
timing/ordering checks become windowed properties (a fill must start within
W cycles of allocation, responses must release in tag order). The
BUG-001/002 lesson applies directly: the eviction accounting and corpse-slot
handling in the shared TB code are already fixed — jet's TB inherits that
fix through the same base classes.

## Measurement plan (J7, frozen)

Trace suite: the cache_sim corpus used for amber's characterization. Board:
Genesys2 pair rig (two jets + shared memory + MonBus tally), after the
amber rig-upgrade task (formal TASK-001) lands. Report: the four metrics
above, `MSHR_COUNT` ∈ {2, 4, 8, 16}, amber vs jet side by side; cache_sim
concurrency model cross-check or documented gap.

## Implementation phases (for the plan that follows spec approval)

1. `jet_pkg` + `jet_mshr` + unit TB.
2. `jet_wb_buffer` + unit TB; drain-engine integration.
3. `jet_rsp_seq` + hit-under-miss in the lookup stage.
4. `jet_control` composition; amber oracle lockstep at FUNC.
5. Snoop-during-miss (per-entry bypass + WB-buffer service); formal
   harness at tiny geometry.
6. FULL soak grids (geometry × MSHR_COUNT × VICTIM_DEPTH); pair-rig DV.
7. Genesys2 pair-rig bring-up + the J7 measurement sweep.

## References

- Kroft, "Lockup-Free Instruction Fetch/Prefetch Cache Organization," ISCA
  1981 — the original MSHR paper (citation only, paywalled; see
  `cache-ip/References/README.md`).
- Farkas & Jouppi, "Complexity/Performance Tradeoffs with Non-Blocking
  Loads," WRL 94-3, 1994 — the lockup-free design space behind J1/J3/J6
  (`cache-ip/References/Farkas_Jouppi_1994_WRL-94-3_Non-Blocking_Loads.pdf`).
- Chinnakonda, *Designing a Multiprocessor Cache Subsystem* — §7.8/§8.2/
  §8.3/§10.10 forward-progress, deadlock, starvation, and sizing guidance
  (cited through the jet HAS).
- gem5 Ruby `MESI_Two_Level-L1cache.sm` — the executable protocol spec the
  amber/jet oracle derives from (`cache-ip/References/gem5-ruby-protocols/`).
