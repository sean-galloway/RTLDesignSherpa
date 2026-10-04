# RTL Drills Apps Program — Design Spec (7 standalone apps)

- **Date:** 2026-10-03
- **Status:** approved direction (user: "work on the other apps now"); README advertising deferred until apps ship
- **Pattern precedent:** `docs/superpowers/specs/2026-10-03-fifo-depth-app-design.md` (fifo_depth app)
- **Recommendation source:** user's 10-item list; batch 1 (ddr_drills tabs) specced separately in
  `2026-10-03-ddr-drills-explorer-calculators-design.md`

## House conventions (all seven)

- Location `bin/apps/<dir>/`, deployed URL `/<dir>/` on the GitHub Pages project site.
- Vanilla HTML5 / CSS / ES5-ish JS. No ES modules, no CDN, no npm, no build step, works from `file://`.
- Every `js/*.js` opens with the dual-environment header
  (`var NS = (typeof window !== 'undefined' ? window : globalThis).NS || (...NS = {});`) and closes
  with `if (typeof module !== 'undefined' && module.exports) { module.exports = NS; }` so node
  `require()` and the browser execute the same bytes.
- Pure model in `js/model.js` (node-testable, no DOM); DOM glue in `js/app.js`.
- `test/run_tests.js`: zero-dependency TAP-ish runner; `node bin/apps/<dir>/test/run_tests.js` exits 0.
- ASCII only, no emojis. Seeded RNG (`mulberry32`) wherever randomness exists; tests pin seeds.
- `README.md` per app: what it teaches, how to open, how to run tests.
- NOT in app scope: launcher tile, Pages workflow staging, `STAGED` map — wired separately after.

## 1. `mtbf_calc` — Metastability MTBF calculator

Lesson: why 2 flops isn't enough at 1 GHz. Model: classic synchronizer MTBF
`MTBF = exp(C2 * tMET) / (C1 * f_clk * f_data)`; N stages contribute (N-1) full resolution periods
plus the aperture term — the model states its exact convention and cites Cummings SNUG papers.
Inputs: f_data (async transitions/s), f_clk, stages N (1-4), per-stage resolution time r
(derived from period - tCO - tSU, editable), technology preset (C1/C2 pairs for e.g. 180/28/7 nm,
labeled typical). Outputs: MTBF per stage count (seconds → years), pass/fail vs a mission-time
input, table MTBF vs N, the "1 GHz, 2 stages" headline case as a preset button. Tests pin known
answers (formula inversions, monotonicity in N and r).

## 2. `fifo_flags` — Async FIFO flag/threshold generator

Companion to `fifo_depth`. Inputs: FIFO depth, write/read clock frequencies (ratio derived),
synchronizer stages, bubble tolerance (% of depth the user can afford to lose at each end).
Outputs: almost-full and almost-empty thresholds with the occupancy-uncertainty margin shown
explicitly (sync latency in the producer/consumer's items, same math style as fifo_depth's
sync margin), a sanity check the thresholds can't collide at the chosen depth, and the
Gray-vs-Johnson depth note where relevant. Tests: symmetric case, worst-case ratio case,
threshold-collision rejection.

## 3. `slack_explorer` — Setup/hold slack & pipelining explorer

Inputs: clock period, tCO, logic/delay line estimate, insertion/route delay, clock skew
(+/-), tSU, tHD; a second corner for min-delay (hold). Outputs: setup slack and hold slack with
pass/fail and which knob fixes a violation; sliders make slack flip sign visibly. Pipelining
panel: split the same logic into 1-4 stages → per-stage budget, new max frequency, latency in
cycles, throughput table (the latency-vs-throughput tradeoff made numeric). Tests: textbook
slack numbers, hold-fix by adding delay, pipelined freq scaling.

## 4. `qformat_explorer` — Fixed-point Q-format explorer

Inputs: Qm.n (m+n = 8/16/32 presets + custom), signed/unsigned, overflow mode (wrap/saturate).
Interactive: bit pattern ⇄ real value (click bits or type either side), quantization step and
max representable error, demo arithmetic (add/mul with shift-and-truncate) showing exact vs
quantized results, overflow behavior demo (wrap vs saturate on a ramp). Tests: round-trips,
step sizes, known wrap/saturate cases, mul shift math.

## 5. `cdc_drill` — Clock-domain crossing drill (gamified, ddr_drills-style)

Two drill modes over a bank of parameterized scenarios (seeded):
- Spot-the-violation: a described or waveform-rendered crossing; pick every illegal element
  (multi-bit bus straight through, pulse into 2-flop, reset misuse, combo logic before
  synchronizer...).
- Pick-the-synchronizer: given data characteristics (single-bit level/pulse, multi-bit bus,
  req/ack semantics, throughput/latency budget, loss tolerance) choose the right structure
  (2-flop, pulse-toggle, handshake, async FIFO) — with the "why" explained per answer.
Pattern mirrors ddr_drills: correct-answer-first banks shuffled by UI, explanations, chapter
filters, exact-set scoring where multi-select. Content floor: ≥ 16 spot + ≥ 12 picker scenarios.
Tests: every scenario validates (≥2 distinct answers, explanation present, correct first),
generator determinism at pinned seeds.

## 6. `crc_calc` — CRC calculator with shift-register visualization

Presets: CRC-8 (0x07), CRC-16/CCITT-FALSE (0x1021), CRC-16/ARC (0x8005, refin/refout),
CRC-32 (0x04C11DB7) — matching the parameter shapes the repo's `dataint_crc` uses
(init/refin/refout/xorout), plus custom poly. Input: hex or ASCII message. Outputs: checksum,
and a step-through table of the shift register per byte (the "watch it shift" view) with
bit-order explanation; the hardware-serial vs software-table agreement note (LSB-first vs
MSB-first conventions) as a first-class panel. Tests: known check values for all four
presets ("123456789" standard check strings), custom-poly round trip, refin/refout handling.

## 7. `cache_sim` — Cache associativity simulator

Inputs: address trace (textarea, one hex addr per line) OR built-in generators
(sequential / strided / random with seed); cache geometry: sets (1 = fully assoc), ways
(1 = direct), block size (words), policy LRU/FIFO/RANDOM. Outputs: hits/misses, hit rate,
miss-classification (compulsory/capacity/conflict) where classifiable, per-access result list,
per-set occupancy view. Tests: hand-computed small cases (direct-mapped vs 2-way on the same
trace shows conflict-miss removal; capacity cliff when sets shrink).

## Shared wiring (done once, after the seven land)

- `bin/apps/launcher/js/apps.js`: 7 `LAUNCHER_APPS` tiles.
- `bin/apps/launcher/test/run_tests.js`: `STAGED` map entries.
- `.github/workflows/pages-ddr-drills.yml`: 7 staging copies + 7 node-suite test steps.
- Root README advertising: deferred per user.

## Verification

Each app: `node bin/apps/<dir>/test/run_tests.js` exits 0. Global: all pre-existing suites
(ddr_drills 13,733 assertions, fifo_depth, launcher integrity) stay green; link checker clean.
