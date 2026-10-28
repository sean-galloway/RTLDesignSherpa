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
  2–16, default 8 (book-formula sizing, §9.10.4).
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

Book terminology (Chinnakonda §9.8): this is a **MAB (miss address
buffer)** — it holds addresses and miss context, NOT line data; fill beats
write straight into the data array (highest W-port priority, per J2), which
is the book's small-area scheme whose forwarding path is just the regular
cache read path (§9.10.2). Amber's FILL_WRITE flow is already this shape.

One row per outstanding miss:

```
{ valid, line_addr, fill_class (RNSD/RU), expected_install_state,
  victim_way, victim_wb_slot, merge_list (requester seq tags),
  fill_beats_rcvd }
```

Ops: `alloc` (new miss), `match` (exact-line CAM — used by merge, by the
hit/pending hazard exclusion, and by the snoop bypass), `retire` (fill
committed). Allocation stalls when full (J6). No aging: a fill once started
always retires, so liveness reduces to fill-engine progress.

**Set-oversubscription rule (book §9.10.2, frontend victimization):** each
in-flight miss claims its victim way at alloc. Misses to one set are capped
at WAYS outstanding — the (WAYS+1)-th miss to a set stalls until one of its
set-mates commits (freeing a way claim). Without this, two fills could
claim the same victim way.

**Sizing (book §9.10.4 formula):** entries ≈ miss occupancy ÷ line-return
time, plus ~2 margin. At the pair rig's ~50–100-cycle memory latency plus
an 8-beat fill (occupancy ≈ 58–108 cycles) and an 8 B/cycle return (line
per 8 cycles), that is N ≈ 7–13 + 2 — centered on 8–16. Ruled the same
day: **default 8** (amended from the initial 4); range 2–16 and the
2/4/8/16 sweep unchanged — the sweep is the experiment either way.

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

`VICTIM_DEPTH` rows of `{valid, line_addr, data, state, bresp_seen}`. A
dirty victim is captured (`victim_load`) when its miss allocates — frontend
victimization, which the book prefers: victim read overlaps the miss issue,
2 array accesses per miss instead of 3 (§9.10.2). The fill proceeds without
waiting for the drain. The drain engine empties the buffer oldest-first,
independent of fill state.

Per the book's victim-buffer occupancy rule (§10.10.1): the **address** is
held until BRESP (a read to the same address must not be issued while the
write is outstanding — the RAW hazard the address retention protects), but
the **data** portion can be released once the last beat is accepted. Jet
keeps it simple: the entry's snoop-visible lifetime runs to BRESP; splitting
address/data lifetimes is a later area optimization if the buffer shows up
in the sweep.

Snoops hitting a buffered victim are served from the buffer — the book's
"snarfing" (§10.8.1), which is amber's SINK_WB_ACK semantics. This is also
what closes the ships-passing-in-the-night corner (§10.12.2): a WriteBack
in flight (pre-BRESP) plus a clean-invalidating snoop to the same line is
answered from the buffer, never "not present".

WB-full stalls only new dirty-victim misses. Snoops never wait on the WB
buffer (they snarf), so the classic "snoop stuck behind a full write
buffer" deadlock (§8.2 case 5) is closed by construction.

### 4. `jet_rsp_seq` — response sequencer (J4)

CPU requests take a sequence tag at accept. Responses (hit data, fill
commit replays, merged requesters) release to the GAXI response port in tag
order; internal completion is out of order. This is the book's Pause Q
(§9.8): a miss "goes to sleep" (its seq tag sits in the MSHR entry's merge
list) and is "woken" when the fill commits. Depth = max in-flight CPU
requests = `MSHR_COUNT` + hit pipeline depth.

### 5. Point of serialization and the anti-livelock rule (book §10.7, §10.9)

Jet's **point of serialization is the lookup stage** (tag read + MSHR CAM
match): accesses to the same line serialize as a linked list behind the
MSHR entry (merge list); accesses to different lines proceed in any order.
This is exactly the book's PoS model, with the MSHR entry playing the
bank's role for its line.

**CU/upgrade anti-livelock (book §10.9, §8.1 case 1/4):** after an upgrade
(CLEAN_UNIQUE) for line L is granted, snoops to L are held off — *briefly
and finitely* — until the write hit completes its commit. The book's rule:
once you own the line, finish the store before reacting to incoming snoops,
otherwise two CPUs can shoot each other's ownership down incessantly. The
hold-off is bounded by the commit latency of an already-granted write
(temporary block, explicitly permitted by §8.2's closing note — never an
event-dependent indefinite block).

**Starvation (§8.3):** no unbounded fixed priority anywhere. Jet's two
priority points are both bounded by construction: fill beats over write
hits on the W port (bounded by an 8-beat fill stream), snoops over new CPU
accepts (bounded snoop service, no allocation). No timeout counters needed
at these two points; any future arbiter added to jet must follow the
timeout-counter rule.

### 6. Snoop path (J4/J5)

Amber's pending-fill bypass generalizes to N entries: AC address matches
the MSHR CAM → answer at the entry's expected post-fill state (PF_GUARD:
only when the fill can actually deliver), snoop's state effect applied
post-commit. WB-buffer match → SINK_WB_ACK service from the buffer.
Neither path ever stalls the snoop behind a fill or drain (Chinnakonda
§7.8). Snoops arbitrate ahead of new CPU accepts (J6). The only snoop
hold-off jet permits is the bounded anti-livelock window of §5.

### 7. `jet_control` — the restructured core

Amber's blocking FSM (LOOKUP→…→REPLAY per transaction) becomes: a lookup
stage that classifies each accepted request (hit / miss-alloc / merge /
stall), N in-flight miss contexts tracked by `jet_mshr`, and the commit
logic (tag write + data writeback of merged writes + response enqueue).
The amber control FSM's *per-transaction* states map onto per-MSHR-entry
progress instead of a global pipeline state. The gem5-derived FSM oracle
(`amber_fsm_oracle`) still pins coherence semantics per line — that model
is timing-free and carries over unchanged.

### 8. Observation (J7 feed)

Existing monlite taps (hits, misses, snoops, evictions, transitions) plus
jet adds: MSHR alloc/merge/retire events and a current-occupancy gauge,
WB-buffer occupancy, response-queue stalls. Same 128-bit MonBus packets,
same tally agents.

### 9. Formal targets (tiny 16-set/2-way geometry, per amber D9)

- J5/J6 liveness: oldest-entry progress, drain progress, snoop progress,
  and the composed corner (MSHR-full + WB-full + snoops pending →
  progress).
- Anti-livelock: the §5 upgrade hold-off window is bounded (a granted
  upgrade's write commits within a fixed cycle bound, snoops to the line
  resume after).
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
concurrency model cross-check or documented gap. Latencies are quoted
**load-to-use** (request accept → data usable), never internal miss
latency, per the book's §9.10.3 quoting rule.

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
- Chinnakonda, *Designing a Multiprocessor Cache Subsystem* — the design
  follows it directly: MAB-vs-FB structure and Pause Q (§9.8), frontend
  victimization and set-oversubscription (§9.10.2), MAB sizing formula
  (§9.10.4), load-to-use quoting (§9.10.3), victim-buffer BRESP occupancy
  and snarfing (§10.10.1, §10.8.1), point of serialization (§10.7), CU
  livelock (§10.9), deadlock/starvation rules (§8.2/§8.3), L2/BIU
  ships-in-the-night (§10.12.2). Local conversion at
  `/mnt/data/github/calibre/books/designing-a-multiprocessor-cache-subsystem/`.
- gem5 Ruby `MESI_Two_Level-L1cache.sm` — the executable protocol spec the
  amber/jet oracle derives from (`cache-ip/References/gem5-ruby-protocols/`).
