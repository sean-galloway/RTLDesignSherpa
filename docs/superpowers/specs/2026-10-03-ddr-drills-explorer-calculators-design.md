# ddr_drills: Bank Explorer + Refresh Calc + Bandwidth Calc — Design Spec

- **Date:** 2026-10-03
- **Status:** design approved in-session; awaiting spec review
- **App:** `bin/apps/ddr_drills/` (deployed at `/ddr_drills/` on the GitHub Pages project site)
- **Precedent pattern:** `docs/superpowers/specs/2026-10-03-fifo-depth-app-design.md`

## 1. Intent

Extend the flagship drill app with three new mode tabs, per the user's approved pick from a
10-item recommendation list (full list recorded in the session; the other 7 items — FIFO
companions, universal-RTL fundamentals, CRC/cache standalone apps — are follow-up batches,
out of scope here):

1. **Bank Explorer** (`explorer`) — per-bank FSM visualization (idle → row-active →
   precharging) with live timing countdowns and a legality quiz: "tRCD expired — can you
   issue READ? tRAS violated?" This is the headline feature; see §5 for the numeric-timing
   dependency discovered during design verification.
2. **Refresh Calc** (`refreshcalc`) — refresh overhead calculator: tREFI, tRFC, 1x/2x/4x
   temperature derating, all-bank vs per-bank rolling granularity → % bandwidth lost and
   worst-case stall.
3. **Bandwidth Calc** (`bwcalc`) — bus width × data rate × efficiency, encoding overhead
   (none / 8b10b / 128b130b / 64b66b), lanes → raw vs effective GB/s, with DDR5/GDDR6/HBM3/
   PCIe preset cards.

Educational goal: the three places where memory-controller understanding actually lives —
bank-state legality, refresh cost, effective bandwidth — each drillable against all 11
packs in the app today.

## 2. Verified facts this design rests on

- Mode contract: `DDRD.<name>Mode = { mount(el, pack), unmount() }` (`js/app.js:3,72`).
  Registration = nav `<button data-mode="<name>">` + `<section id="mode-<name>">` +
  `MODE_IDS` in `js/app.js` + `<script>` tag in `index.html` + matching `require()` in
  `test/run_tests.js`. Tabs today: `quiz`, `timing`, `scenario`, `sandbox`, `timingref`,
  `commands` (6 → 9).
- **The engine is structural-only.** `js/engine.js` schedules ACT/PRE/RD/WR/RDA/WRA with no
  timestamps; pack `timingParams` entries are prose `{symbol, name, definition, chapter,
  appliesTo}` for the reference tab; `scenarioTweaks.turnaround` values are text
  placeholders (`'(tWTR bubble)'`). There are **no machine-readable timing numbers** in the
  app today.
- Numeric timing source: `/home/seang/github/cold_storage/MemorySpecs/docs/<tech>/
  ch06_electrical_timing_package/{01_core_timing,02_turnaround_timing,03_refresh_timing}.md`
  — per-technology markdown with concrete values (e.g. DDR4 refresh table: tREFI1 7.8 µs,
  tRFC 160/260/350/450 ns by density; 2x/4x pairs). Working source for transcription; pack
  citations stay JEDEC-style per house rules (see §4.3).
- Repo JEDEC PDFs (`reference/ddr_lpddr_specs/`) cover only DDR2/LPDDR2 — insufficient
  alone; the MemorySpecs tree covers all 11.

## 3. Goals / success criteria

- Three new tabs work for every pack, from `file://` and on the deployed site, mobile-first.
- `node bin/apps/ddr_drills/test/run_tests.js` green: existing suites unchanged (13,733
  assertions) + new suites for the three models.
- `selftest.html` green (it loads the same suites).
- Tab behavior with a pack lacking optional data degrades gracefully (structural-only
  legality, calculators unaffected).
- ASCII only, no dependencies, no ES modules, seeded RNG where randomness is used.

## 4. Non-goals

- No changes to the existing 6 modes' behavior, the engine, the scenario generators, or
  the mutators.
- No launcher / GitHub Pages workflow changes (app directory unchanged; tab list lives
  inside the app).
- No new packs. No questionBank additions (the explorer quiz is generated, not banked).
- FIFO-companion / universal-RTL / CRC / cache apps (separate batches, separate specs).

## 5. Pack schema extension: `timingNs` (numeric timing block)

The explorer's elapsed-time legality and countdowns need numbers; packs don't have them.
Additive, optional field:

```js
timingNs: {
  // one entry per parameter the explorer enforces; ns values, chosen speed bin recorded
  tCK:   { v: 0.625 },           // controller clock period for countdown display, ns
  tRCD:  { v: 15.0 },
  tRP:   { v: 15.0 },
  tRAS:  { v: 32.0 },
  tRC:   { v: 47.0 },            // sanity: >= tRAS + tRP
  tRTP:  { v: 7.5 },             // RD -> PRE spacing
  tWR:   { v: 15.0 },            // WR -> PRE spacing (write recovery)
  tWTR:  { v: 7.5 },             // WR -> RD turnaround, same bank
  tRTW:  { v: 3.0 },             // RD -> WR turnaround, same bank
  tRFC1: { v: 350.0 },           // refresh (explorer v1: display only; REF not an engine cmd)
  bin: 'DDR4-3200 (representative speed bin, 0.625 ns tCK)',
  source: '<JEDEC doc + table pointer for the chosen bin>; transcribed from MemorySpecs docs/ddr4/ch06_electrical_timing_package/01_core_timing.md'
}
```

Rules:
- Field is OPTIONAL. `validatePack` (`js/registry.js`) gains validation for it when present:
  every `v` positive finite number; `tRC >= tRAS + tRP`; `bin` and `source` strings present.
- Units are ns (not nCK) — the MemorySpecs tables give both; ns chosen so the calculators
  and explorer share values without a rate conversion. Values that are spec'd only in nCK
  are converted at the recorded `tCK`.
- Speed bins: the app's drill model is cycle-structural, so each pack records ONE
  representative bin (the pack's `note`/`name` already carry the bin identity). The exact
  bin and its citation go in `bin`/`source`.
- Pack-authoring checklist (`bin/apps/ddr_drills/README.md`, `notes/pack-authoring.md`)
  gains a step 7: timingNs.
- All 11 packs authored this batch, transcribed from the MemorySpecs tree.

## 6. Tab 1 — Bank Explorer

**Files:** `js/legal.js` (pure model), `js/explorer.js` (UI mode), `test/test_legal.js`.

### 6.1 FSM model (in legal.js)

Per bank: `IDLE --ACT(row)--> ACTIVE(row) --PRE--> PRECHARGING --tRP--> IDLE`, with
`RDA/WRA` from ACTIVE going to PRECHARGING (auto-precharge). RD/WR require ACTIVE with
matching `openRow` (row hit); mismatch = row conflict (needs PRE first). One command issue
per cycle across all banks (shared bus). This is the structural layer — always on.

### 6.2 Replay API

`DDRD.legal.replay(schedule, topology, timingNs?)` → replay object:

- `stateAt(bankIdx, timeNs)` → FSM state + openRow + per-relevant-counter elapsed/remaining
  ns (tRCD, tRAS, tRP, tWR, tRTP, turnarounds) — counters computed from the schedule's
  command events replayed up to `timeNs`.
- `legal(bankIdx, cmd, timeNs)` → `{ ok, violations: [{ symbol, needNs, haveNs }] }` —
  structural rules +, when `timingNs` is present, elapsed-time rules. Violations cite the
  parameter by symbol (quiz feedback: "tRCD: ACT→RD needs 15.0 ns; 9.4 ns elapsed").
- Without `timingNs`: `violations` only carries structural reasons and counters read
  "timing not available for this pack".

### 6.3 UX flow

1. Scenario picker (reuses `scenarios.js` generators + tier filters, same as Bank-State
   Drill) and policy picker (open / close / FR-FCFS).
2. Engine runs once → schedule (structural, as today).
3. Step controls: **command step** (issue next scheduled command) and **time step**
   (advance one `tCK`). The quiz operates at the current time, before the next command.
4. Bank tile grid (geometry from `pack.topology`, grouped when `hasBankGroups`): tile
   color = FSM state, label = open row; a per-bank expandable counter panel.
5. Legality quiz pane: "Bank B — which commands are legal right now?" exact-set
   multi-select over ACT/RD/WR/PRE(/RDA/WRA per pack command set), RD/WR annotated with
   their target row from the pending request; exact-set scoring with per-violation
   explanations. A RD/WR that misses the open row is illegal at quiz time with a
   row-conflict violation ("row 5 open, request targets row 2 — PRE required first");
   the corrected sequence is the lesson the drill teaches.
6. Annotated timeline of issued commands with engine reasons (same renderer style as
   Sandbox).

### 6.4 Seeded randomness

Scenario pick uses `DDRD.mulberry32(seed)`; quiz selection is deterministic per mount;
node tests pin seeds (house rule).

## 7. Tab 2 — Refresh Calc

**Files:** `js/refreshcalc_model.js` (pure), `js/refreshcalc.js` (UI),
`test/test_refreshcalc.js`.

- Model API: `compute({ tREFI_ns, tRFC_ns, derate /* 1|2|4 */, granularity /* 'all'|'per' */,
  tRP_ns /* optional adder */, banksPerGroup? })` → `{ refreshesPerSec, overheadPct,
  stallNs, stallPctOfWindow }`.
- Derating: `tREFI/d`, `tRFC_d` from the standard 1x/2x/4x pairing (packs' prose already
  documents these pairings; the model takes the pair as explicit inputs, derate selects
  the pair).
- `granularity: 'per'` (per-bank / bank-group rolling, HBM+LPDDR style) models tRFC hidden
  behind other banks: reported stall = tRFC / banks (approximation, labeled as such in the
  UI note).
- Inputs: manual numeric fields + **pack pre-fill button** reading `timingNs.tREFI1/tRFC1`
  when present + three built-in presets (DDR4-3200 8Gb, LPDDR4X, HBM3) with "typical
  values" labeling.
- Tests pin known answers: DDR4-3200 1x ≈ 4.3 % (0.35 µs RFC / 7.8 µs REFI), 4x ≈ 15.9 %,
  per-bank rolling on 4 banks cuts stall ~4×.

## 8. Tab 3 — Bandwidth Calc

**Files:** `js/bwcalc_model.js` (pure), `js/bwcalc.js` (UI), `test/test_bwcalc.js`.

- Model API: `compute({ widthBits, ratePerPin /* MT/s or GT/s */, lanes, encoding
  /* 'none'|'8b10b'|'128b130b'|'64b66b' */, efficiencyPct, ddr /* double-data-rate toggle */ })`
  → `{ rawGbps, effectiveGbps, encodingOverheadPct, perEncoding: [{encoding, gbps}] }`.
- Encoding efficiencies: 8b10b = 0.8, 128b130b ≈ 0.9846, 64b66b ≈ 0.9697, none = 1.
- `ddr` toggle doubles beats per clock for DDR-style MT/s vs PCIe GT/s — the UI copy
  explains the difference (the lesson the tab exists to teach).
- Preset cards, computed through the same model: DDR5-6400 x64, GDDR6-18 x32, HBM3
  1024-bit, PCIe 5.0 x16, PCIe 6.0 x16 (FLIT). Side-by-side table; user edits any preset
  to explore.
- Tests pin known answers: PCIe 5.0 x16 raw 63.0 GB/s → 8b10b would be 50.4 (teaching
  contrast: PCIe actually uses 128b130b → 62.0); HBM3 6.4 Gbit/pin × 1024 bit ≈ 819 GB/s raw.

## 9. Integration & verification checklist

- `index.html`: 3 nav buttons + 3 `<section id="mode-...">` + 3 `<script>` tags
  (after `js/scenarios.js`, before `js/app.js`, matching existing order).
- `js/app.js`: `MODE_IDS` += `'explorer'`, `'refreshcalc'`, `'bwcalc'`.
- `test/run_tests.js`: `require()` the 3 new model files + 3 new test suites.
- `selftest.html`: loads the same suites (verify no per-suite registry edits needed; if it
  enumerates, just add files).
- All 11 packs: add `timingNs` (transcription source: MemorySpecs tree; citations JEDEC).
- `node bin/apps/ddr_drills/test/run_tests.js` green; `selftest.html` green; manual
  browser pass on 2 packs (one with, one historically without, to exercise fallback —
  after this batch all have it, so temporarily test fallback via a fixture pack in tests).
- App `README.md`: modes list + pack-authoring checklist updated.

## 10. Risks

- **Speed-bin ambiguity**: every pack records one representative bin; the UI labels it.
  Wrong-bin arguments are a content bug, fixable per pack without code changes.
- **nCK-only parameters**: converted at recorded `tCK`; conversion noted in `source`.
- **Tab bar crowding (6→9)**: mobile-first CSS wraps; acceptable, revisit if reported.
- **Fallback path rot**: all 11 packs get `timingNs`, so structural-only fallback is only
  exercised by unit-test fixture — keep the fixture.
