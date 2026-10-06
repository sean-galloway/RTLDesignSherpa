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

# amber — Pre-Hardware Architecture Specification (Pre-HAS)

**Version:** 0.3 (draft, 2026-10-06)
**Status:** architecture sketch written while the PRD decisions are still
OPEN. This document records **no decisions**. "PROPOSED" marks a working
default put forward so the decision rows can be argued with concretely; a
decision becomes DECIDED only when [PRD.md](../../PRD.md) records a name and
a date. When the decisions close, each PROPOSED item here is either ratified
into the full `amber_has` chapter book (the stream/andesite convention) or
overridden and this file edited.
v0.2 (2026-10-06): D2 landed in the PRD — CPU-side is a **GAXI slave**.
F9 now answers probe-during-fill with a **pending-fill bypass** instead of
an unbounded stall. Q1 answered — `amber_fabric` carries **both** rig
attachments and the `RIG` elaboration parameter generate-selects.
v0.3 (2026-10-06): Q1 re-answered by the owner — both rigs as **two tops**,
`amber` (pair rig) and `amber_ace` (onyx rig), on a shared `amber_core`.
No `RIG` parameter: the rig is whichever top you instantiate.

**Governing documents:**
[PRD.md](../../PRD.md) (binding) ·
[onyx PRD D7](../../../onyx-ace-ccu/PRD.md) (snoop-port contract) ·
[jet PRD](../../../jet-mesi-l1/PRD.md) (what must stay constant) ·
[GLOBAL_REQUIREMENTS.md](../../../../../../GLOBAL_REQUIREMENTS.md) ·
[cache simulator](../../../../../../bin/apps/cache_sim/) (golden model)

---

## 1. Intent of this document

The PRD carries eleven decision rows and has closed three: **D2** (CPU-side
is a GAXI slave), **D4** (snoop transport is ACE-shaped AC/CD/CR), and
**D8** (observation through `*_monlite` wrappers only). The Pre-HAS makes
the open rows concrete: for each, it sketches the feature the way a working
default would build it, so the architecture can be reviewed before any RTL
exists. It is deliberately cheap to change — one file, no chapter skeleton
yet.

## 2. Feature sketches

### 2.1 Core datapath — the blocking bet

- **F1 — Blocking single-outstanding pipeline.** A miss freezes the front
  end until the fill completes and the original request replays. No MSHR, no
  hit-under-miss, no merge logic — that deletion is the entire point; it is
  jet's delta (jet J1–J5).
- **F2 — Geometry as elaboration parameters** (D1 OPEN). PROPOSED default
  profile 32 KiB / 64 B lines / 4 ways (128 sets) as the DV matrix centre of
  gravity; ranges 4–32 KiB, 32–64 B, 2–8 ways.
- **F3 — Pluggable replacement** (D7 OPEN). PROPOSED: true-LRU as the
  correctness reference (the cache simulator models it exactly), tree-PLRU
  as the FPGA-area variant; FIFO/random kept because the sim models them
  too. Policy is an elaboration parameter, never a code hack, so the
  sim↔RTL cross-check holds for every policy both sides implement.
- **F4 — Write policy** (D5 OPEN). PROPOSED: write-back + write-allocate —
  MESI's M state earns its keep, and dirty-victim handling is where blocking
  simplicity pays. Write-through/no-allocate retained as a bring-up mode
  because it deletes the victim path entirely.
- **F5 — Whole-line fills.** One burst per fill; sub-line fill granularity
  is a non-goal. Burst length derives from `LINE_BYTES / (BUS_WIDTH/8)`.

### 2.2 Coherence

- **F6 — MESI state per line** (D6 OPEN). PROPOSED plain MESI; MOESI's
  O-state recorded as a later elaboration upgrade, not v1 — ownership's win
  (dirty-transfer reduction between caches) is a measurement for the pair
  rig, not a v1 requirement. Insurance: allocate a 3-bit state field now
  (MESI needs 2; MOESI needs 3) so the upgrade is an encoding change, not an
  array rebuild.
- **F7 — ACE snoop responder** (D4 DECIDED — sketched, not re-decided).
  `amber_snoop_resp`: a thin adapter speaking raw ACE AC/CR/CD on the
  outside per the onyx D7 contract (IHI 0022 the definition) and driving a
  bus-agnostic probe interface inside. The cache core never contains ACE —
  only the adapter does; that is exactly why D4 was chosen (onyx, or a real
  ACE interconnect, can supersede the custom bus without touching cache
  RTL).
- **F8 — Snoop/local arbitration — the culsans problem.** Probes must not
  starve and CPU tag latency must stay bounded. PROPOSED: tag array on the
  dual-port `sdpram_core` — port A for CPU lookups, port B for snoop
  lookups; data array port A for CPU/fill, port B for snoop readout feeding
  CD. No arbitration stall in the common case; the *control* collision
  (miss FSM vs snoop FSM wanting the same array control port) resolved with
  snoop-priority round-robin inside `amber_control`.
- **F9 — Probe-during-fill, answered by a bypass** (direction set
  2026-10-06: add the bypass). Blocking means a fill is usually in flight,
  and a probe against a pending line must not observe pre-fill state. The
  answer is not an unbounded stall: amber keeps one pending-fill register —
  single outstanding by construction — recording {line address, state being
  installed, data availability}. A probe matching it is answered from the
  register: CRRESP reflects the post-fill state, and required CD beats are
  forwarded from the fill stream as its beats arrive. A probe that misses it
  takes the normal tag path. The snoop response is bounded either way. The
  correctness target sharpens rather than relaxes: *the bypass must be
  state-accurate* — a probe against a pending fill observes exactly the
  post-fill state, never pre-fill — alongside the response-bound liveness
  target. jet reopens the generalisation (jet J4/J6): multiple outstanding
  fills turn the register into a pending-fill table, which is jet's problem,
  not amber's.
- **F10 — CRRESP response matrix** per MESI state, mirroring the RDS-DV ACE
  BFM default matrix as corrected in cocotb-framework 1.2.0 (MakeInvalid on
  M/O invalidates without data transfer — the bug the release fixed). The
  matrix ships as an explicit table in the full HAS.

### 2.3 Fabric side — where the two deployment rigs meet

- **F11 — The two rigs.** *Pair rig* (amber D10): two ambers + shared
  memory, snoops peer-to-peer on the D4 port, misses are plain AXI4 to
  memory. *Onyx rig*: misses become coherent transactions toward onyx; onyx
  owns the memory side and drives the snoops. One cache core, two fabric
  attachments.
- **F12 — Fabric side: two tops on one core** (Q1 answered 2026-10-06:
  do both, as two tops). The rig-agnostic cache core is shared; the fabric
  difference is confined to the top wrapper and its master stack:
  - `amber` — the pair-rig top. Misses are plain AXI4 to memory on the
    house `axi4_master_rd/wr` wrappers; snoop encodings never driven; the
    ACE snoop-responder port faces the peer cache.
  - `amber_ace` — the onyx-rig top. Fabric side is the existing
    `rtl/amba/ace/axi4ace_master_rd` / `axi4ace_master_wr` modules (ACE
    fields and RACK/WACK auto-pulse already in place), driven by a thin
    `amber_ace_issue` coherent-transaction issuer mapping cache events to
    the onyx D2 subset — read miss → ReadShared / ReadUnique (by desired
    exclusivity), write promotion → CleanUnique / MakeUnique, dirty
    eviction → WriteBack, clean eviction → Evict. Memory masters not
    exposed; the snoop-responder port faces onyx.
  No parameter selects between them: the rig is whichever top is
  instantiated. Both tops are compiled, and both are exercised in the DV
  matrix — `amber` against a peer + memory environment, `amber_ace`
  against an onyx environment (§5).
- **F13 — Fill/drain engines** (D3 OPEN, direction: house wrappers). Fill =
  one AR burst, whole line. Drain = a small victim buffer (PROPOSED depth 1)
  + one AW burst. Single outstanding by construction — no reorder buffers.

### 2.4 Observation (D8 DECIDED — sketched, not re-decided)

- **F14 — `amber_monlite` wrapper.** MonBus event set: hit (read/write),
  miss with class split (cold/capacity/conflict, when the golden model
  supplies the class), snoop (type, hit/miss, response class), eviction
  (clean/dirty), MESI state transitions, fill/drain start+end. Tallied by
  `monbus_tally_axil` exactly like every other component; the wrapper never
  stalls the observed port — drop-and-count. The observer's own gate cost
  is measured present vs absent (F18), so "the observer does not perturb
  what it measures" is a quantified claim, not an assertion.

### 2.5 Verification & formal surface (D9 OPEN — direction proposed)

- **F15 — Pattern-B cocotb grids.** GATE/FUNC/FULL over the
  geometry × policy × rig matrix. Instruments already exist: the RDS-DV
  `AXI4ACESnoopMaster` BFM drives amber's snoop port and `AXI4ACEMasterRead/
  Write` drive the fabric side (cocotb-framework 1.2.0).
- **F16 — Golden-model parity.** Trace replay from
  `bin/apps/cache_sim/` at identical geometry + policy; hit/miss/miss-class
  counts must match exactly (PRD success criterion 1). The replacement
  policy parameter (F3) is what keeps this check meaningful across policies.
- **F17 — SymbiYosys targets** (PRD criterion 2): no stale data served after
  an external write (F9 ordering); no deadlock/livelock under fair
  arbitration. Proof surfaces named now so the RTL is built proof-shaped:
  `amber_control` FSM, `amber_snoop_resp`, tag-array port sharing, victim
  buffer handoff.

### 2.6 Cost & characterisation (PRD criterion 4)

- **F18 — Synthesis sweep.** Geometry params × replacement policy on Nexys
  A7 and/or Genesys 2; LUT/FF/RAM/fmax recorded in `docs/` the way pumice
  characterised. Includes the F14 observer-present vs absent delta.

## 3. Proposed block architecture

Proposed module set (`amber_*` prefix, per the cache-ip convention):

| Module | Role | PRD anchor |
|---|---|---|
| `amber` | Pair-rig top: `amber_core` + plain AXI4 master stack + snoop responder toward the peer | D10 |
| `amber_ace` | Onyx-rig top: `amber_core` + ACE master stack + coherent-transaction issuer + snoop responder toward onyx | D10, F12 |
| `amber_core` | Shared rig-agnostic core, instantiated by both tops | — |
| `amber_cpu_frontend` | GAXI slave (D2 decided); request accept, response return, replay latch | D2 |
| `amber_control` | Blocking pipeline FSM: lookup → hit / miss → evict → fill → replay; owns tag-array control arbitration (F8) and the pending-fill bypass register (F9) | D1, D5 |
| `amber_tag_array` | `sdpram_core` tag + state store (3-bit state field, F6) | D11 |
| `amber_data_array` | `sdpram_core` data store | D11 |
| `amber_repl` | Pluggable replacement (policy elaboration parameter) | D7 |
| `amber_victim` | Dirty victim buffer + drain trigger | D5 |
| `amber_fill` / `amber_drain` | AXI4 read/write engines; plain `axi4_master_rd/wr` under `amber`, `axi4ace_master_rd/wr` under `amber_ace` | D3 |
| `amber_snoop_resp` | ACE AC/CR/CD adapter; bus-agnostic inside — faces the peer in `amber`, onyx in `amber_ace` | D4 |
| `amber_ace_issue` | Coherent-transaction issuer for the onyx D2 subset — `amber_ace` only | F12 |
| `amber_monlite` | Observation wrapper (D8) | D8 |

**Miss data flow:** frontend accept → tag lookup (port A) → miss →
`amber_repl` picks victim → dirty? `amber_victim` + drain engine WB → fill
engine AR burst → data array write + state install → original request
replays from the frontend latch → response.

**Snoop data flow:** AC arrives at `amber_snoop_resp` → tag lookup (port B)
→ line state determines CRRESP and whether CD beats follow → response
driven. Conflict with an in-flight fill resolves per F9.

**Observation taps sit on control-FSM decision points, not the datapath** —
the F8 port split means the datapath need not be touched to observe it.

## 4. Interface sketches (shapes, not pinouts)

| Side | Sketch | Anchor |
|---|---|---|
| CPU-side | **DECIDED (PRD D2, 2026-10-06): GAXI slave** — house BFM/monitor coverage and skid/FIFO plumbing already exist, and STREAM can attach as first real consumer without an adapter. Must express single-beat reads, write-allocate fills, byte enables. | D2 |
| Fabric-side | Two tops, shared core (F12): `amber` = plain AXI4 masters to memory + AC/CR/CD snoop responder toward the peer; `amber_ace` = `axi4ace_master_rd/wr` + `amber_ace_issue` toward the CCU (onyx D2 subset: ReadShared / ReadUnique / CleanUnique / MakeUnique / WriteBack / Evict) + the same snoop responder toward onyx. The rig is the top you instantiate — no mode parameter. | D3, D4 |
| Observation | MonBus through `amber_monlite`; no other debug surface. | D8 |
| Register block | **None.** Parameter-only IP; all visibility through MonBus tallies, unlike every other component's APB CSR. Recorded explicitly so it is a decision and not an accident. | — |

## 5. Parameter sketch (illustrative — feeds the DV matrix)

| Parameter | PROPOSED default | Range / set |
|---|---|---|
| `SETS` | 128 | 16–512 |
| `WAYS` | 4 | 2–8 |
| `LINE_BYTES` | 64 | 32–64 |
| `REPL_POLICY` | `lru` | `lru, tree_plru, fifo, random` |
| `WRITE_POLICY` | `wb_wa` | `wb_wa, wt_na` |
| `VICTIM_DEPTH` | 1 | 1–2 |
| `BUS_WIDTH` | 64 | 32–128 |

Rig is **not** a parameter: it is the top you instantiate — `amber` or
`amber_ace` (F12). Derived: tag width = `ADDR_WIDTH − $clog2(SETS) −
$clog2(LINE_BYTES) + 3` (state field, F6); fill beats =
`LINE_BYTES / (BUS_WIDTH/8)`.

## 6. Open questions this sketch surfaces

| # | Question | Where it resolves |
|---|---|---|
| Q1 | ~~One mode-parameter `amber_fabric` vs separate adapters per rig~~ — **RESOLVED 2026-10-06:** two tops on a shared `amber_core` — `amber` (pair rig) and `amber_ace` (onyx rig); no rig parameter, both compiled, both in the DV matrix (F12) | Full HAS implements it |
| Q2 | ~~GAXI vs plain valid/ready CPU-side~~ — **RESOLVED by PRD D2 (2026-10-06, Sean): GAXI slave** | `amber_cpu_frontend` RTL |
| Q3 | Geometry default vs Nexys A7 RAM budget (F2) | With the F18 cost sweep |
| Q4 | 3-bit state field headroom for MOESI (F6) | Cheap now, expensive later — recommend taking the insurance |
| Q5 | ~~Probe-during-fill stall bound~~ — **RESOLVED 2026-10-06: add the pending-fill bypass** (F9); formal targets become bypass state-accuracy + response bound | Full HAS implements it; PRD criterion 2 depends on it |
| Q6 | Replacement default: LRU reference vs tree-PLRU area (F3) | D7 closure, informed by F18 |

## 7. What the full HAS will add

The chapter book per the stream/andesite convention: front matter; purpose,
conventions, definitions; use cases / key features / system context;
graphviz block diagram; data flow; pin-level interfaces; performance
targets; integration (clocking, reset, verification). The MAS follows when
micro-architecture decisions land (array banking, pipeline staging). This
Pre-HAS is the draft those books grow from — sections 2–6 above map onto
chapters 2–5.

## 8. Cross-references

- [amber PRD](../../PRD.md) — binding requirements; decision record
- [onyx PRD D7/D2](../../../onyx-ace-ccu/PRD.md) — snoop-port contract and
  coherent-transaction subset the ONYX rig speaks
- [jet PRD](../../../jet-mesi-l1/PRD.md) — J-rows hold amber constant; nothing
  here may silently pre-decide jet (F9's stall policy is amber's; jet J4/J6
  explicitly reopen it)
- [References/AMBA_ACE_Interface_Definition.md](../../../References/AMBA_ACE_Interface_Definition.md)
  and [References/gem5-ruby-protocols/](../../../References/gem5-ruby-protocols/)
  — protocol definition and golden-protocol source
- RDS-DV cocotb-framework 1.2.0 ACE BFMs — the DV instruments F15 assumes

---

**Last Updated:** 2026-10-06
**Maintained By:** amber architecture (pre-decision working document)
