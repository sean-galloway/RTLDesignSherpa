# Authoring a Content Pack

How to add a memory technology to ddr_drills. Mechanics (the 5-step
checklist) are in `../README.md`; this file is the CONTENT contract -
what makes a pack correct, complete and consistent with the others.

## The schema

A pack is one `packs/<tech>.js` IIFE ending in `DDRD.registerPack({...})`
with:

| Field | Shape | Consumed by |
| --- | --- | --- |
| `id` | unique lowercase string | registry, router |
| `name` | display name | pack picker |
| `jedec` | `{doc, note}` - spec number + one-line character | footer citation |
| `topology` | `{hasBankGroups, groups, banksPerGroup, banks, rows, cols, sids}` | engine, scenarios, matcher |
| `commands` | `['ACT','PRE','RD','WR','RDA','WRA']` | validation |
| `timingParams` | `[{symbol, name, definition, chapter, appliesTo}]` | timing drill |
| `questionBank` | `[{q, answers, chapter, hard, explanation, source}]` | quiz |
| `scenarioTweaks` | `{excludeGenerators, extraTags, defaultPolicy, turnaround:{wtr,rtw}}` | scenario drill, engine labels |

`DDRD.validatePack` enforces the shape at load time; `test/test_packs.js`
enforces the content floors (see below) in CI.

## Hard rules

1. **Correct answer first.** `answers[0]` is always the right one. Every
   UI shuffles; the model layer never does. All answers in one question
   must be distinct and plausible - wrong answers are the teaching.
2. **Every question cites a source.** `source` is a JEDEC document +
   section/table pointer (`'JESD79-2F sec 3.6.3'`). The question text and
   explanation are PARAPHRASED from the spec - never copied prose, never
   a reproduced figure. Functional facts (truth-table entries, MR field
   layouts, timing values) are fine to state directly.
3. **tRTW exists in every pack.** Where the spec names the read-to-write
   parameter, use its name. Where it does not (DDR2, LPDDR2), define tRTW
   anyway with the spec's relation and a "book symbol" note in the
   definition. `test_packs.js` rejects a pack without tRTW and without a
   tWTR-family parameter.
4. **Drill-model topology.** `banks: 8, rows: 8, cols: 8` always. Real
   geometry goes in a comment and in `name`/`note` prose. `sids: 0` unless
   the technology has Stack IDs (HBM4: `sids: 2` in the drill model).
5. **ASCII only.** The pre-commit hooks and `validatePack` both care.

## timingParams authoring

- `appliesTo` rules are `{from, to, scope}`. `from`/`to` are command
  patterns with `|` alternation and `*` wildcard (`'RD|RDA'`, `'*'`).
- Scopes: `same_bank`, `same_group`, `diff_group` (BG techs only),
  `diff_bank` (flat techs), `diff_sid` (SID techs only), `any`.
  A `diff_bank` rule also fires on `diff_group`/`diff_sid` pairs (one-way
  subsumption: different groups/stacks are different banks). `same_bank`
  does NOT subsume into `same_group` - list both scopes explicitly when a
  parameter covers both (see tCCDL/tWTRL in packs/hbm4.js).
- **Reference-panel-only parameters** (refresh, power-down, anything the
  drill engine never emits) use a `from` the engine cannot produce:
  `'REF'`, `'PREA'`, `'SRX'`. They render in the timing reference panel
  with a truthful "applies between" and never match a question. Document
  them as panel-only in the definition.
- **Direction-change params.** Decide per book whether the column-spacing
  parameter (tCCD family) covers direction changes or only same-direction
  pairs, and say so in the definition. HBM4 covers all four column types
  on both sides; DDR2/LPDDR2 model tCCD as same-direction only, matching
  their books' gap sheets. Whatever the choice, turnaround params
  (tWTR/tRTW) must cover WR->RD and RD->WR.
- Record every symbol, its scope pattern, value basis and spec reference
  in `notes/timing-tables.md` - that worksheet is the cross-check against
  the spec, per pack.

## questionBank authoring

- Floors enforced by `test_packs.js`: >= 8 questions, >= 3 distinct
  chapters, >= 2 answers each, >= 10 timingParams overall. Aim for 12-15
  questions spanning organization / init / commands / timing / datapath /
  refresh.
- `chapter` tags are the quiz's filter checkboxes - keep the vocabulary
  small and consistent within the pack.
- `hard: true` on questions whose wrong answers are seductive (formula
  mix-ups, direction swaps, S4-vs-S2 confusions). Roughly a third of the
  bank is a good mix.
- Explanations teach the distractors down: say WHY each plausible wrong
  answer is wrong, not just why the right one is right.

## Topology-dependent scenarios

The 19 scenario generators degrade automatically: generators whose
`requires` (`bg`, `sids`) the topology cannot meet are excluded by
`DDRD.availableGenerators(topo)`; ACT-pipelining and full-mix generators
run with topology-keyed explanation variants. A pack normally needs
NOTHING in `excludeGenerators` - use it only to drop a generator that is
legal but actively misleading for the technology, and say why in a
comment.

`defaultPolicy` is `'open'` unless the technology's teaching default is
close-page. `turnaround` overrides the engine's annotation labels
(`'(tWTR bubble)'`, `'(tRTW bubble)'`) when the technology names those
bubbles differently.

## Verify

```bash
node bin/apps/ddr_drills/test/run_tests.js   # all suites incl. test_packs
```

Then open `index.html`, switch to the new pack, and play one round of each
mode. The footer under the app shows the pack's JEDEC citation - check it
reads the way the other packs read.
