# DDR Drills - Design Record

Why the app is built the way it is. Mechanics (how to open it, run tests,
add a pack) live in `../README.md`; this file records decisions and the
reasoning behind them, newest context first per topic.

## 1. Script tags, not ES modules

The app must work from `file://` (double-click `index.html`, phone, a
static host with no configuration). ES-module fetches are blocked by CORS
on `file://`, so everything is a plain `<script>` tag writing to one
global namespace, `DDRD`.

Consequence: load order is manual and load-bearing. `index.html` and
`JS_ORDER` in `test/run_tests.js` list the same files in the same order
(registry, rng, model, engine, mutate, scenarios, then packs, then UI).
Changing one without the other breaks either the browser or the tests.

## 2. One file, two environments

Every `js/` file opens with:

```js
var DDRD = (typeof window !== 'undefined' ? window : globalThis).DDRD ||
           ((typeof window !== 'undefined' ? window : globalThis).DDRD = {});
```

so the browser (window) and node (globalThis, via `require()`) execute
the SAME bytes. The node test harness therefore tests the shipped files,
not a copy or a bundle - there is no build step that could drift.

## 3. Seeded RNG everywhere

All randomness (scenario generation, mutator fallbacks, future UI
shuffles) flows through `DDRD.mulberry32(seed)`, passed as an explicit
`rng` parameter. Tests pin seeds and are fully deterministic; a failure
is reproducible by re-running the same seed. A side benefit kept open:
shareable drill URLs can later encode seed + filters without touching
the engine.

## 4. Annotations are commands

Turnaround bubbles ("--- (tWTR bubble) ---") are first-class Cmd objects
with `annotation: true`, not side-channel strings. Rationale: schedules
format uniformly, and `format_schedule` (the wrong-answer dedup key)
captures them for free. The cost is one rule every consumer must honor:
mutators, the timing matcher and any real-command logic skip annotation
Cmds. The mutator invariant is stronger: the real-command subsequence of
a wrong answer must differ from the correct schedule's.

## 5. Turnaround rule: global, sticky, op-type only

After each column command, if its data-bus op (RDA counts as read, WRA
as write) differs from the previous COLUMN command's op, a turnaround
annotation is inserted immediately before it: tWTR on WR->RD, tRTW on
RD->WR. The latch is global across banks and is NOT reset by intervening
PRE/ACT commands - bus direction is a shared-resource property, not a
per-bank one. Labels are per-pack overridable
(`scenarioTweaks.turnaround`) because the books' symbol conventions
differ (tRTW is a book-symbol for DDR2/LPDDR2; see the study-note
books' Chapter 6).

## 6. ACT pipelining: three preconditions, all required

Open-page pipelines ACTs (phase 1 = all ACTs, phase 2 = all column
commands) only when ALL of: every request is the same op; every request
targets a distinct bank; there are zero page misses. Each precondition
kills a real hazard: mixed ops would interleave turnarounds into the
"parallel" phase, same-bank ACTs are illegal back-to-back, and a miss
injects PRE/ACT pairs that destroy the two-phase shape. Tests falsify
each precondition individually.

## 7. FR-FCFS: one-level reorder

The spec reading implemented: scan arrival order; the oldest page-hit
may jump ahead of the oldest miss (one jump per scan pass), then the
reordered list runs through the open-page scheduler. The scheduler
returns the reordered request list so the UI can show served-vs-arrival
order. A full multi-level reorder was considered and rejected: it
teaches the same lesson with far more visual noise.

## 8. Pack schema and validation

Packs are data plus one `DDRD.registerPack({...})` call. `validatePack`
enforces the contract at load time (unique id, topology sanity -
`banks == groups * banksPerGroup` when bank groups exist - every
question has >= 2 answers and an explanation, every timingParam has >=
1 appliesTo rule, ASCII-only strings). A malformed pack throws at load,
never mid-drill. Correct answers are always `answers[0]`; shuffling is
the UI's job, which keeps the data diff-friendly.

## 9. Scenario generators degrade, they don't lie

Each of the 19 generators declares `requires: {bankGroups?, sids?}`.
On a topology that can't honor them (flat-bank DDR2/LPDDR2), BG/SID-only
generators are excluded outright - a "cross-group" drill on a tech with
no bank groups teaches something false. Two generators
(act_pipelining, full_mix_hard) degrade instead: same mechanics, with
explanation text keyed on `hasBankGroups` so the prose never claims
group parallelism that doesn't exist.

## 10. Zero-dependency testing

`test/run_tests.js` requires the shipped js files, then the test files
(each registers suites on `globalThis.DDRD_TEST_SUITES`), runs them, and
exits non-zero on any failure. TAP-ish output. Chosen over jsdom/jest
because the app has no npm anything; the moment a real DOM test is
wanted this decision should be revisited, and UI modules are kept thin
for exactly that reason.

## Deferred (later commits, per the approved plan)

- Content packs (`packs/hbm4.js`, `ddr2.js`, `lpddr2.js`) transcribed
  from the study-note books in cold_storage/MemorySpecs/docs.
- UI modes: quiz, timing drill (+ reference panel), bank-state drill,
  sandbox. The timing matcher's scope-subsumption rule (diff_bank
  satisfied by same_group/diff_group on BG techs) is decided there.
- GitHub Pages deploy workflow (test job gates deploy; Settings ->
  Pages -> Source = "GitHub Actions" is the one manual step).
