# core_drills: merlin stage viewer + hazard quiz + peregrine predictor drill -- Design Spec

- **Date:** 2026-11-27
- **Status:** accepted 2026-11-28, all eight decisions as recommended (sec. 14);
  riscv-ip/common-rv32i TASK-003 step 1
- **App:** `bin/apps/core_drills/` (deployed at `/core_drills/` on the GitHub Pages project site)
- **Suite spec:** `docs/superpowers/specs/2026-10-06-riscv-falcon-suite-design.md`
  ("Suite-wide packaging", build order milestone 3)
- **Precedents:** `2026-10-03-ddr-drills-explorer-calculators-design.md`,
  `2026-10-03-fifo-depth-app-design.md`, `2026-10-03-rtl-drills-apps-program-design.md`

## 1. Intent

One drill app for the core ladder, as the suite spec plans it. This doc covers the
three modes that have cores behind them today:

1. **Stage Viewer** (`stage`, merlin). Step a program through IF/ID/EX/MEM/WB one
   cycle at a time and watch the forwarding arrows, the stalls and the flushes.
2. **Hazard Quiz** (`hazard`, merlin). Generated snippets with questions whose
   answers the merlin model computes: how many bubbles, which path feeds this
   operand, which instructions get flushed.
3. **Predictor Drill** (`bpred`, peregrine). Step a branch stream through the BTB
   and BHT, predict the predictor, and see each update land.

Audience: readers of *Simplified RV32I* (kestrel; its ch07 merlin teaser is the
bridge), the planned *Simplified RV32I: merlin -- pipelining* (not written yet; until
it exists the citations point at the merlin PRD and RTL), and *Simplified RV32IM*
(peregrine, ch02 "Speculation"). Each mode teaches the core **as built**: where a
book and the RTL disagree, the model follows the RTL and the drill says so (sec. 2).

## 2. Verified facts this design rests on

App architecture (`bin/apps/ddr_drills`, `bin/apps/launcher`, `.github/workflows/pages-ddr-drills.yml`):

- Mode contract `DDRD.<name>Mode = { mount(el, pack), unmount() }`; registration = nav
  button + `<section id="mode-<name>">` + `MODE_IDS` in `js/app.js` + `<script>` tag.
  Hash routing `#/mode/pack`; a section mounts once per pack and survives tab switches
  (`test/test_shell.js`).
- Dual window/globalThis header on every `js/`/`packs/` file, so `test/run_tests.js`
  `require()`s the shipped bytes in `JS_ORDER`/`PACK_ORDER`, kept in step with
  `index.html` by hand; zero-dependency TAP runner; `selftest.html` runs the suites in
  a browser.
- **Cache busting is a hand-bumped query string**, `?v=YYYYMMDD[letter]` on each
  script/stylesheet tag in `index.html` and `selftest.html`, because Pages caches about
  10 minutes (`vault/handbook/tools/apps/ddr-drills.md`). Nothing checks it, or the html
  order: ddr_drills' `selftest.html` today loads 3 of 11 packs and 5 of 7 suites.
- Deploy: the one `site pages` workflow runs every app's node suite, then copies each
  app dir to `_site/<dir>/`. Launcher = `LAUNCHER_APPS` in `launcher/js/apps.js`,
  checked by `launcher/test/run_tests.js` (`APP_INDEXES`, `STAGED` href->dir map).
- No README beside the app (2026-11-07 rule; the 2026-10-03 program spec's "README per
  app" is superseded). Mechanics, including fixture regeneration, go in
  `vault/handbook/tools/apps/core-drills.md`, indexed in `vault/handbook/tools/INDEX.md`.
- Precedent for crossing languages: `cache-ip/common-ip/dv/golden/cache_sim_harness.py`
  runs `bin/apps/cache_sim/js/model.js` from Python. Here the direction reverses
  (sec. 10): the Pages CI has node, not Python, spike or the toolchain.

merlin as built (`merlin-rv32i/rtl/top/merlin_core.sv`, `rtl/fub/merlin_hazard.sv`,
PRD sec. 4.2 and M1-M4). The MAS ch04 behavior chapters are still placeholders, so
the RTL and `dv/tests/test_merlin_hazards.py` are the documentation:

- Forwarding goes EX/MEM->EX and MEM/WB->EX on both operands, and EX/MEM wins. The
  select is computed in ID against the instructions then in ID/EX and EX/MEM, then
  registered, so the result equals an EX-stage compare. x0 never forwards. A
  producer exactly three ahead (DV distance 2) reaches the consumer through the
  **WB-to-ID regfile bypass**, not a forwarding mux; four or more ahead reads the regfile.
- **Load-use:** a load in EX whose rd matches an ID source stalls IF/ID and flushes
  ID/EX: 1 bubble (DV: the distance-0 consumer retires at load + 2).
- **Load-to-branch (TASK-004, 2026-11-21):** the branch/JALR operands never take load
  data from WB. A branch (rs1 or rs2) or JALR (rs1) whose producer is a load waits.
  A load directly ahead costs 2 bubbles and a load one between costs 1 (DV: retire
  gap 3 in both cases).
- **Control:** branches, JAL and JALR all resolve in EX. Predict-not-taken; a taken
  transfer flushes IF/ID and ID/EX (2 bubbles). A flush beats a stall.
- **The ID compares use the raw instruction fields** `insn[19:15]`/`insn[24:20]`,
  whether or not the instruction reads them. So `lw x5,..` followed by
  `addi x6,x7,5` stalls (imm[4:0] = 5). The model reproduces that, and the drill
  teaches it as a lesson.
- `ecall`/`ebreak`/illegal/misaligned halt with a cause in WB. The halting
  instruction retires and everything younger is flushed.
- Book disagreements: the kestrel book's merlin teaser (ch07.2) and merlin HAS ch05
  give load-use = 1 and taken = 2 but leave out the load-to-branch interlock, which
  came later, and no document mentions the raw-field stall. The app follows the RTL.
  peregrine is no longer "merlin plus additions" for load-use: since P14/TASK-006 it
  does not forward a load WB->EX, so its load-use costs 2. That is one reason modes
  1-2 are merlin-only (decision D6).

peregrine predictor as built (`peregrine-rv32im/rtl/fub/peregrine_bpred.sv`, PRD
sec. 4.2 and P5, book ch02.1-02.2, `dv/tbclasses/peregrine/bpred_model.py`). RTL,
PRD, book and model agree:

- Direct-mapped BTB, 32 entries: index `pc[6:2]`, tag `pc[31:7]`, word target, an
  uncond bit, and a valid bit that resets. 256 2-bit BHT counters at `pc[9:2]`, with
  no reset. Predict taken = BTB hit and (uncond or counter[1]). No RAS.
- Update once per instruction leaving EX. Conditional taken without a conditional
  hit installs the counter at **`01`**; conditional taken with a hit steps up and
  rewrites the entry; conditional not-taken steps down and leaves the BTB alone;
  JAL/JALR installs an unconditional entry; a non-control instruction predicted
  taken clears its entry. Mispredict = direction wrong, or taken with the wrong
  target. Cost 2 bubbles; `BP_EN=0` is merlin's fetch.
- The stress streams are `dv/tbclasses/peregrine/predictor_streams.py`: 12 self-checking
  RV32IM programs (loop_trip1-4, btb_alias, bht_alias, jalr_targets, interlock,
  stale_entry, trap_shadow, stale_target, jalr_odd). They use M, Zicsr traps and
  self-modifying code with `fence.i`. `test_peregrine_predictor.py` holds the RTL's
  retired predictions to `check_trace`, which accepts any state the IF-lookup lag allows.

## 3. Goals / success criteria

- Three tabs that work from `file://` and on the deployed site, mobile-first, ASCII
  only, no dependencies, no ES modules, seeded RNG wherever randomness appears.
- `node bin/apps/core_drills/test/run_tests.js` green. That includes the merlin RTL
  fixture check (sec. 9) and the bpred_model fixture check (sec. 10).
  `selftest.html` green.
- TASK-003's second "done when": modes 1-3 pass the node suite, and mode 3's
  outcomes match `bpred_model.py` on the stress streams.

## 4. Non-goals

- Modes 4/5 (gyrfalcon ROB, garuda FP scheduler). Only the hooks in sec. 12 are built.
- A peregrine pipeline in modes 1-2 (D6), the M extension or traps in the app's
  interpreter (D2), `mem_wait` injection, and spike/riscv-formal-grade ISA coverage
  (the interpreter is checked against RTL retire data, sec. 9).
- No changes to ddr_drills. The house runtime (registry, rng, the run_tests kit) is
  **copied**, not shared, because each app dir deploys standalone.

## 5. File layout

```
bin/apps/core_drills/
  index.html  selftest.html  style.css
  js/registry.js     CORED namespace, pack registry, validatePack
  js/rng.js          mulberry32 (copy of ddr_drills)
  js/isa.js          RV32I encode/decode tables, disassembler          (pure)
  js/asm.js          assembler: text -> {words, listing, labels, errors} (pure)
  js/interp.js       RV32I interpreter -> dynamic trace                 (pure)
  js/pipe_merlin.js  merlin cycle model                                 (pure)
  js/pipe_mutants.js misconception variants of pipe_merlin (quiz)       (pure)
  js/quizgen.js      seeded snippet + question generators               (pure)
  js/bpred.js        peregrine predictor model                          (pure)
  js/stageview.js  js/hazardquiz.js  js/bpreddrill.js   mode UIs (DOM)
  js/app.js          shell: hash router #/mode/pack[/item], pack picker
  packs/merlin.js  packs/peregrine.js
  test/run_tests.js  test/test_*.js  test/export_programs.js
  test/fixtures/merlin_pipe.js  test/fixtures/bpred_streams.js   (GENERATED)
```

Fixtures are `.js`, not `.json`. They assign to `CORED_FIXTURES` under the dual header,
because `selftest.html` cannot fetch JSON from `file://`.

## 6. Model layer

All pure. They return new objects and never mutate their inputs.

**`isa.js` / `asm.js`.** RV32I base plus the GNU pseudo-ops the packs need (`li`, `la`,
`mv`, `nop`, `j`, `jr`, `ret`, `call`, `beqz`/`bnez`/`bgt`/`ble`...), labels, `.word`,
`.balign`, `.skip`. `li`/`la` expand exactly as `riscv-none-elf-as` does (lui+addi with
the carry adjust), so the words match the golden assembler bit for bit. Errors carry
the line number. The decode table is keyed by extension (`I` now) so M/A/F can
register later without touching the core.

**`interp.js`.** `run(image, {resetPc, maxSteps})` -> `{trace, halt}`. Each trace entry
is the app's common currency, which every mode reads:
`{seq, pc, insn, op, rs1, rs2, rd, rs1v, rs2v, rdv, memAddr, isLoad, isStore,
ctrl: 'br'|'jal'|'jalr'|null, taken, target, nextPc}`. Memory is unified (kestrel/merlin
TB arrangement), so a store into text changes what is fetched later. Halt follows
merlin's contract (ecall/ebreak/illegal/misaligned).

**`pipe_merlin.js`.** `simulate(image, {resetPc, maxCycles})` ->
`{cycles: [...], insts: [...], cpi}`. It is a **structural, cycle-stepped** mirror of
`merlin_core`, not a trace-driven dependency count. Each cycle it evaluates the RTL's
own equations: `pc_d` priority (halt > flush > stall > +4); `merlin_hazard`'s select
and `stall_lu` on raw fields; `stall_ldbr`; `id_ex_flush_eff = flush | stall`; the
WB-to-ID bypass. Then it advances the four pipeline registers. Wrong-path fetches come
from the image, so flushed instructions show up struck out. Per cycle it emits
`{stage: {IF,ID,EX,MEM,WB: seq|null|'bubble'}, fwdA, fwdB, bypass, stallLu, stallLdbr,
exFlush, why: [...]}`, using the RTL signal names so the viewer can say what the GTKW
save file shows. Per instruction it emits `{seq, pc, stageCycles, retireCycle,
bubblesBefore, opSrc: {a, b}}`, where a source is `regfile|wb_bypass|exmem|memwb`.
EX computes values through the forwarded operands, so a forwarding bug also shows as
a value mismatch against `interp.js`. Structural rather than a dependency count,
because a count would miss the raw-field stall and flush-over-stall.

**`pipe_mutants.js`.** Named variants of `pipe_merlin` with one rule changed. Each one
is a misconception: `textbook_branch` (no load-to-branch interlock),
`id_resolve` (branches resolve in ID: 1 bubble), `memwb_priority` (wrong priority),
`no_bypass` (no WB-to-ID bypass, so distance 2 reads a stale value), `decoded_sources` (no raw-field
stall). The quiz builds its wrong answers by running these, so every distractor is what
a named misconception predicts, and the explanation names it. This is ddr_drills'
mutate.js, applied at the level of the model.

**`quizgen.js`.** `generate(rng, pack, tier)` -> `{snippet, question, answers[0]=correct,
explanation, cite}`. Templates combine a producer (ALU, load, LUI, JAL link) with a
consumer (ALU rs1/rs2, store data, store address, branch rs1/rs2, JALR) at a distance
of 0-3 (merlin DV convention: 0 = the next instruction), plus taken and not-taken
control. Question kinds: bubbles before X; source of X's operand A/B; which
instructions flush; retire cycle of X / total cycles; why X stalled (load-use,
load-to-branch, raw-field). `pipe_merlin` computes the answer; mutants that agree with
it are skipped, and a question no mutant distinguishes is rejected. ddr_drills rule:
at least 2 distinct answers, correct first, the UI shuffles.

**`bpred.js`.** It mirrors `BpredModel` with exact counters:
`create({btbEntries, bhtEntries, installCtr})`; `predict(state, pc)` -> `{taken, target,
hit, btbIdx, bhtIdx, ctr}`; `update(state, ev, predTaken)` -> `{state, row}`, where `row`
names the update-table row that fired (the book's five-row table) so the UI can
highlight it; `replay(events, cfg)` -> per-event `{predTaken, predTarget, mispredict}`
plus final state and counts. `eventsFromTrace(trace, cfg)` turns an `interp.js` trace
into events: every control instruction, plus every non-control instruction whose
lookup predicts taken. Any other instruction cannot change state, so the filter
loses nothing (tested). The defaults are the as-built `32/256/01`. Other values are
UI what-ifs and are labeled "not the RTL".

Stated in the UI: replay is in **program order** (a lookup sees every older update),
the model `bpred_model.py` defines. The RTL's IF lag, where a lookup can miss the one
or two newest updates, is what `check_trace` tolerates; mode 3 does not show it (D5).

## 7. Modes: what the learner sees and does

**Stage Viewer.** A pipeline diagram (rows = dynamic instructions, columns = cycles;
`--` bubble, struck-out flushed slot) over a five-box datapath strip for the current
cycle: the instruction in each stage, forwarding arrows from EX/MEM or MEM/WB into EX
operand A/B, the WB-to-ID bypass arrow, and stall/flush badges with a reason line
("stall_lu: lw x5 in EX, ID's rs2 field is x5 (addi imm[4:0])"). A signal panel shows
`ex_fwd_a/b`, `stall_lu`, `stall_ldbr`, `ex_flush`, plus registers and running CPI.
Step, back, run-to-cycle; pick a pack program or edit it (reassembles live). Teaches
forwarding priority, the load-use bubble, the 2-bubble flush, the load-to-branch extra
bubble and the raw-field stall.

**Hazard Quiz.** One generated snippet (listed asm) and a question; single-select, or
exact-set multi-select for "which flush". Feedback opens the snippet in the Stage
Viewer at the cycle that matters, so the explanation is the pipeline diagram. Tiers
(`basic`, `loads`, `control`, `all`) filter templates; the pack's conceptual bank is
mixed in. Score is per session, nothing stored.

**Predictor Drill.** The dynamic stream on the left; a 32-row BTB (valid, tag, target,
U/C) and a 16x16 BHT grid on the right, indexed row and cell outlined. Before each
event the learner commits a guess (taken/not, target; mispredict?); the step reveals
the lookup, the outcome, the update-table row that fired and the counter's move on the
00-11 diagram. Tallies compare against `BP_EN=0` (every taken transfer mispredicts),
with a bubble estimate at 2 per mispredict labeled as an estimate, not the book's
measured table. What-ifs: table sizes and install `01`/`10` (book ch02.2's measured
lesson). Streams: the 12 stress streams (read-only, fixture) and the pack's RV32I
programs run live through `interp.js` and editable (move an aliasing branch with
`.balign`).

## 8. Packs

A pack is one core. It is an IIFE that calls `CORED.registerPack`, and `validatePack`
enforces the schema at load time.

```js
{ id, name, book: {title, chapters}, modes: ['stage','hazard'] | ['bpred'],
  cite: { prd, rtl: [...], dv: [...] },        // where each modeled rule is documented
  params: { btbEntries:32, bhtEntries:256, installCtr:1 },   // peregrine only
  programs: [{ id, title, asm, focus, look: [{cycle, note}], cite }],
  quizBank: [{ q, answers, explanation, cite, tier }],       // answers[0] correct
  quizTiers: {...}, streams: [{ fixture: 'loop_trip2' } | { program: 'nested_loop' }] }
```

How a program is authored: assembly text in the pack, ending in `ecall` (merlin
halt) and linked at 0. `focus` is a sentence on what to look at. `look` holds cycle
annotations, which are checked against the model's cycle count, so a timing change
that leaves a note stale fails the suite. Every program must assemble, halt within
its cycle cap, and appear in the merlin fixture (sec. 9).

Starter list for `merlin.js` (12). The first eight are asm versions of the DV's own
hex cases (`dv/tests/programs/hazard_*.hex`, `load_use_distances.hex`), so the
fixture covers what the RTL suite asserts: forward_matrix, load_use_distances
(d0/d1/d2), load_branch (cases A-D), branch_after_alu, branch_flush_backtoback,
jalr_forward, store_data_forward, flush_during_loaduse. Four are new:
raw_field_stall (lw then addi/lui/jal whose immediate bits alias rd),
wb_bypass_distance2 (producer 3 ahead, no mux arrow), x0_never_forwards, and
array_sum_loop (a realistic CPI). `peregrine.js`: the 12
fixture streams, plus RV32I programs nested_loop, if_else_alternating,
aliasing_pair_movable, jump_table_jalr and two_site_call_return (no RAS).

## 9. Node test suite

Suites, in TEST_ORDER: `test_isa` (encode/decode round trip over every RV32I format and
immediate edge), `test_asm` (labels, pseudo expansion, errors; **golden: the GNU-as
words in the merlin fixture**), `test_interp` (hand cases; **golden: the RTL's RVFI
`rd_wdata`/`pc_wdata` in the merlin fixture**), `test_pipe_merlin`, `test_mutants`,
`test_quizgen`, `test_bpred`, `test_packs`, `test_shell`.

`test_pipe_merlin` checks two things.
(a) **RTL fixture.** For every pack program, each instruction's retire cycle
(relative to the first retire) and the per-cycle `ex_fwd_a/ex_fwd_b/stall_lu/
stall_ldbr/ex_flush` must equal the RTL's.
(b) Hand-pinned rules copied from `test_merlin_hazards.py`: distance-0 load-use =
load+2, load-branch gap 3 at d0 and d1, branch_flush_backtoback retires exactly 4 beats, every
instruction retires once and in order, at most one per cycle.

The merlin fixture is `test/fixtures/merlin_pipe.js`. Its generator is a cocotb test in
the merlin suite, `merlin-rv32i/dv/tests/test_merlin_drill_fixture.py`, which works in
five steps:
1. Get every pack program's text and words from `node test/export_programs.js`.
2. Assemble the same text with `riscv-none-elf-as` and require identical words.
3. Run each program on `merlin_tb_top` through `MerlinTB`.
4. Record the RVFI beats, with cycle, plus the five probes, sampled from `u_merlin_core`.
   The signal names are pinned, so a rename fails loudly.
5. Compare against the committed fixture, or rewrite it when `CORE_DRILLS_REGEN=1`.

That test runs in the merlin regression, so an RTL or pack change that moves the
timing goes red until someone regenerates and commits the fixture.

`test_mutants` checks that every mutant differs from `pipe_merlin` on at least one
starter program. A mutant that agrees everywhere is dead and generates no
distractors. `test_quizgen` pins seeds and checks determinism, answer == model, distinct
answers, and that every question has an explanation. `test_packs` runs validatePack,
assembles every program, checks the halt cap and the `look` cycles, rejects non-ASCII,
and requires citations. `test_shell` is ddr_drills' mount-persistence test plus a new
**order-sync check**. It parses `index.html` and `selftest.html` and asserts that their
script lists match JS_ORDER, PACK_ORDER, the fixtures and TEST_ORDER, and that every
local tag carries `?v=`. That is the drift ddr_drills has today.

## 10. Mode 3 cross-check against bpred_model.py

The claim being tested: `bpred.js` replay == `BpredModel` replay, event for event, on
the stress streams. `BpredModel` == RTL is already held by `check_trace` in
`test_peregrine_predictor.py`, so the chain reaches the RTL.

- **Generator:** `peregrine-rv32im/dv/tbclasses/peregrine/bpred_fixture.py`, with a
  `__main__` that writes `bin/apps/core_drills/test/fixtures/bpred_streams.js`. For
  each `streams('gate')` program it does five things:
  1. Build the ELF the predictor test builds, with the same `program()`, as/ld flags and `LINK_BASE`.
  2. Check `check_alias`.
  3. Run spike (`run_spike`, `rv32im_zicsr_zifencei`) and `parse_spike_log`.
  4. Drop records before the entry and stop at the store to `tohost`, so the
     `1: j 1b` spin never lands in the fixture.
  5. Derive each beat's taken/target from the next commit's pc.

  It then replays `BpredModel(32, 256, unknown_counters=False)` in program order
  (`predict_one(pc)`, then `update(...)`) and writes the filtered events `[pc, kind,
  taken, target]`, the expected `[predTaken, predTarget, mispredict]`, the final
  BTB/BHT contents, counts, and the sha256 of `bpred_model.py` and
  `predictor_streams.py`. Spike is a faithful source because the predictor test
  locksteps the RTL to it, and it needs no simulator. The generator asserts the
  filtered and full-stream replays end in the same state.
- **Node side:** `test_bpred` replays every fixture stream with the as-built config and
  requires every prediction, mispredict flag, final table and count to match, naming
  the first divergent event (stream, index, pc). `eventsFromTrace` over the pack's
  RV32I programs is checked against hand-computed expectations.
- **Sync:** `test_peregrine_bpred_fixture.py`, a plain pytest in the peregrine gate
  level: a fast hash compare against the current sources, then a regenerate-to-temp
  and byte diff; either failure prints the regen command. A change to the Python model
  or streams goes red in the peregrine regression; a change to `bpred.js` goes red in
  the node suite and the Pages CI (no toolchain needed); the regenerated fixture is
  committed with the change that caused it.

## 11. Deploy and launcher

- `launcher/js/apps.js`: `{ id: 'core_drills', name: 'RISC-V Core Drills', href:
  'core_drills/', blurb: 'Pipeline stage viewer, hazard quiz and branch-predictor drill
  for the merlin and peregrine cores' }`. `launcher/test/run_tests.js`: `APP_INDEXES` +=
  `core_drills`, `STAGED['core_drills/'] = 'core_drills'`.
- Workflow: a test step `node bin/apps/core_drills/test/run_tests.js`, and
  `mkdir -p _site/core_drills` + `cp -r bin/apps/core_drills/* _site/core_drills/`. The
  existing `bin/apps/**` path filter already triggers it.
- Cache busting follows the house rule: hand-bumped `?v=YYYYMMDD[letter]` on every tag,
  fixtures included, now enforced by the presence check in `test_shell`.
- The header gets an "All apps" link to `../`. No absolute `/` URLs (launcher test).
- Deep links `#/stage/merlin/load_branch` and `#/bpred/peregrine/bht_alias` let a book
  cite a drill by URL.

## 12. Hooks for modes 4 and 5 (not built)

- Tab ids `rob` (gyrfalcon) and `fpsched` (garuda) are reserved; the shell enables a
  tab only when the pack lists the mode, so a new rung is a pack plus mode files.
- The interpreter trace (sec. 6) is the interface: a ROB viewer and an FP scheduler
  each consume it with their own timing model, as `pipe_merlin` does, without touching it.
- The ISA table is keyed by extension, so M (gyrfalcon), A (gyrfalcon-A) and F (garuda)
  register decode/assemble/execute entries; the trace record reserves `flags: null`
  for F's accrued `fcsr` bits.
- `bpred.js` is reused unchanged by a gyrfalcon pack (it speculates off peregrine's
  predictor). Each future mode brings its own DV-generated fixture, as sec. 9 and 10 do.

## 13. Risks

- **Fixture churn:** every merlin timing change needs a one-command regen. Intended.
- **Assembler fidelity:** a pseudo-op expanded unlike GNU fails the word compare; packs
  avoid ambiguous forms.
- **Program-order vs RTL lag:** a learner holding the book's waveform may see the RTL
  predict from an older state; the UI note and D5 cover it.

## 14. Decisions for the owner

Decided 2026-11-28: the owner took the recommended option on all eight ("all
recommended"). Each line below names the choice first.

- **D1 Program authoring.** In-app RV32I assembler with an editable sandbox, checked
  word for word against GNU as (recommended), or pre-assembled hex only (smaller, but
  the learner cannot edit anything).
- **D2 Interpreter scope.** Keep `interp.js` RV32I-only and take the 12 peregrine
  stress streams from the fixture as read-only event streams (recommended), or grow it
  to M + Zicsr traps + `fence.i` so they run live. That is a second trap model to keep
  in sync for one mode.
- **D3 Fixture level.** Stress streams at `gate` reps (8; recommended: small, and
  enough to saturate counters) or `func` (40).
- **D4 merlin fixture depth.** RVFI retire cycles plus the five internal probes
  (recommended; the arrows and stall reasons get checked, at the cost of pinning
  internal names), or retire cycles only (public interface, but the arrows go
  unchecked).
- **D5 RTL lag in mode 3.** Program-order replay with a stated note (recommended for
  v1), or an "as the pipeline sees it" view that replays the RTL's retired predictions
  from a sim trace. That would need an RTL fixture as well.
- **D6 peregrine in modes 1-2.** merlin only (recommended: the rung's lesson, and
  peregrine's load-use now differs), or a peregrine profile later as its own model
  file.
- **D7 What-if knobs.** Install value `01`/`10` and table sizes (recommended: book-backed),
  or add a 1-bit counter variant, a textbook contrast the RTL never built.
- **D8 Cache-bust mechanism.** Keep the hand-bumped date with the new presence and
  order check (recommended: house rule, zero build), or a stamping script that writes
  content hashes into the tags. That would be the first build step any app has.
