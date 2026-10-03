# DDR Drills

A zero-build, zero-dependency web app for training memory-controller
intuition: knowledge quizzes, timing-parameter drills, bank-state
scheduling drills, and a live scheduling sandbox. One tech-agnostic
scheduling engine drives every mode; each memory technology plugs in as a
content pack.

This file is MECHANICS ONLY. The decision record (why script tags, why
annotations are commands, the exact engine semantics) lives in
`notes/design.md`.

## Open the app

Open `index.html` in any browser. It works from `file://` -- no server,
no build step, no network access. Any static file server works too:

```bash
cd bin/apps/ddr_drills && python3 -m http.server 8000
# then http://localhost:8000/
```

## Run the tests

```bash
node bin/apps/ddr_drills/test/run_tests.js
```

Exit code 0 means every suite passed. The runner `require()`s the shipped
`js/*.js` files unmodified (the same bytes the browser loads), then the
`test/test_*.js` files, which register suites on
`globalThis.DDRD_TEST_SUITES`. Output is TAP-ish: one `ok`/`not ok` line
per assertion, a summary line, and `# PASS` / `# FAIL` at the end.

Tests are deterministic: all randomness in scenario generation and
wrong-answer mutation flows through a seeded mulberry32 RNG
(`DDRD.mulberry32(seed)`), threaded as an explicit `rng` parameter.

## Layout

```
index.html        app shell; loads js files in dependency order
selftest.html     in-browser test runner (same suites as the node harness)
style.css         all styling
js/registry.js    DDRD namespace, pack registry, pack schema validation
js/rng.js         mulberry32 seeded PRNG + helpers
js/model.js       Req/Cmd factories, bank state, canonical text formats
js/engine.js      open-page / close-page / FR-FCFS schedulers
js/mutate.js      7 mutators + fallbacks -> exactly 3 wrong answers
js/scenarios.js   19 parameterized scenario generators + build API
js/timing.js      timing-drill matcher (pure) + mode 2 UI
js/quiz.js        mode 1 UI (knowledge quiz)
js/scenariodrill.js  mode 3 UI (bank-state drill)
js/sandbox.js     mode 4 UI (live scheduling sandbox)
js/app.js         shell: hash router, pack picker, tab switching
packs/            one content pack per technology (hbm4, ddr2, lpddr2)
test/             zero-dependency node harness and suites
notes/            design.md decision record, pack-authoring.md content
                  contract, timing-tables.md per-pack spec cross-check
```

## Self-test in a browser

Open `selftest.html`. It loads the same shipped js files and the same
suite files as the node harness and runs them with a DOM-writing
assertion kit - a green PASS banner means the engine works in that
browser (useful on a phone, where there is no node).

## Deployment

`.github/workflows/pages-ddr-drills.yml` runs the node suite on every
push that touches this directory and, when green, deploys this directory
to GitHub Pages (artifact upload, no gh-pages branch). One-time manual
step: repo Settings -> Pages -> Source = "GitHub Actions".

## How a pack registers (5 steps)

Three packs ship today (`packs/hbm4.js`, `packs/ddr2.js`,
`packs/lpddr2.js`); the content contract for writing a new one is
`notes/pack-authoring.md`. Mechanics:

1. Create `packs/<tech>.js` as an IIFE that ends in
   `DDRD.registerPack({...})`.
2. Fill in `id`, `name`, `jedec: {doc, note}`, and `topology`
   (`{hasBankGroups, groups, banksPerGroup, banks, rows, cols, sids}`).
   When `hasBankGroups` is true, `banks` must equal
   `groups * banksPerGroup`.
3. Add `questionBank` entries `{q, answers, chapter, hard, explanation,
   source}` -- the correct answer is always `answers[0]`; shuffling is the
   UI's job. Every question needs at least 2 answers and an explanation.
4. Add `timingParams` entries `{symbol, name, definition, chapter,
   appliesTo}` with at least one `appliesTo` rule per parameter.
5. Add a `<script src="packs/<tech>.js">` tag in `index.html` AFTER
   `js/scenarios.js`, and a matching `require()` in `test/run_tests.js`.

Everything is ASCII. `registerPack` throws on schema violations or a
duplicate id, so a malformed pack fails loudly at load time.

## The one rule for contributors

No ES modules, no CDN, no build step, no dependencies, no emojis, ASCII
only. Every `js/` file opens with the dual-environment header:

```js
var DDRD = (typeof window !== 'undefined' ? window : globalThis).DDRD ||
           ((typeof window !== 'undefined' ? window : globalThis).DDRD = {});
```

so the browser (plain `<script>` tags) and node (`require()`) execute the
same bytes. The script order in `index.html` and `JS_ORDER` in
`test/run_tests.js` must stay in sync.
