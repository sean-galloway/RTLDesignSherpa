<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# docs-review — Open (accepted, not started)

---

## DOCREV-011 — fix ALL broken links, whenever they were introduced
**Status:** open 2026-07-26 (Sean); mechanical classes swept 2026-07-27
**Priority:** P2

Not a rename cleanup. **Every** broken link in the repo, no matter which move,
split or deletion caused it. First measured 2026-07-26 at `d65be489`: **495
broken links across 160 files.**

### Where it stands

**374 remain, across 146 files** (re-measured 2026-07-27 at `057f75df`+). The
two mechanical classes were swept outside `projects/`, which is what closed the
121:

| n | class | how to fix |
|---|---|---|
| 308 | target does not exist anywhere | judgement call each: write the page, repoint, or delete the link |
| 64 | target moved (same filename exists elsewhere) | mechanical, but these are the ones the sweep deliberately skipped -- see below |
| 2 | repo-root-relative | mechanical |

**262 of the 374 are under `projects/`**, which is deferred. Outside projects the
remaining count is 112, and it is dominated by pages that reference documentation
that was never written:

| n | file |
|---|---|
| 24 | `bin/markdown_to_word_instructions.md` |
| 10 | `bin/TBClasses/wavedrom_user/GAXI_WAVEDROM_GUIDE.md` |
| 10 | `docs/markdown/TestTutorial/wavedrom_gaxi_example.md` |
| 7 | `bin/DOC_GENERATION.md` |
| 6 | `docs/markdown/overview.md` (was 76) |
| 5 | `docs/DOCUMENTATION_STANDARDS.md` |

`README.md` and `docs/markdown/rtl-cdc/cdc.md` are now at zero.

### What the sweep deliberately would not touch

Three exclusions, each because a "fix" there would be a corruption:

- **`docs/review/`** — archived reviewer output. It *quotes* what a page said at
  the time. Rewriting a quoted link falsifies the record.
- **Anything inside a ``` fence** — templates and examples. The link in
  `assets/*/DIAGRAM_PLAN.md` or in `doc-placement.md` is written relative to the
  *page being generated*, not to the file it appears in. An automated pass
  "fixed" both on the first attempt and had to be reverted.
- **`projects/`** — deferred by request until the rest of the tree is done.

That accounts for most of the 64 remaining "moved" links. Any future automated
pass must keep these three exclusions.

**The second class -- 126 `rtl/**/*.sv` `// Documentation:` headers pointing at
nonexistent files -- is CLOSED (2026-08-12).** All were in `rtl/math`: 113 at
`IEEE754_ARCHITECTURE.md`, 12 at `BF16_ARCHITECTURE.md`, 1 at
`docs/bf16-research.md`, plus 40 more still pointing at the pre-split
`rtl-common/index.md` and one at `index.md` -- every `rtl/math` header (167)
now points at `docs/markdown/rtl-math/overview.md`, the stale
`Subsystem: common` lines say `math`, and the `Regenerate:` lines name
`rtl/math`. Fixed at the SOURCE per [[generated-rtl-discipline]]: the two
`rtl_header.py` generators emit the new header, and regen-and-diff across
both generated families is ZERO. The two `rtl/cdc` headers that pointed at
`index.md` now point at their per-module pages.

### Regenerate the list

    python3 - <<'EOF'
    import os, re, subprocess
    files=[f for f in subprocess.check_output(['git','ls-files','*.md'],text=True).split()
           if os.path.isfile(f)]
    lr=re.compile(r'\[[^\]]*\]\(([^)\s]+?)(?:#[^)\s]*)?\)')
    for f in files:
        root=os.path.dirname(f) or '.'
        for m in lr.finditer(open(f,encoding='utf-8',errors='ignore').read()):
            t=m.group(1)
            if t.startswith(('http://','https://','mailto:','#')): continue
            if not os.path.exists(os.path.normpath(os.path.join(root,t))):
                print(f"{f} -> {t}")
    EOF

### Notes before starting

- **`docs/review/kimi/**` was removed in the 2026-07-28 corpus reset** — its
  4 broken links went with it (they were inside critique artifacts, which are
  evidence and were never to be hand-edited anyway, [[doc-placement]] rule 5).
- **Dangling `[[wikilinks]]` in `vault/` are not broken links.** The handbook
  convention is that a `[[name]]` with no note yet marks something worth
  writing. 36 distinct ones exist; leave them.
- Do the two mechanical classes (221 of 495) first and re-measure. That leaves
  the 274 judgement calls, which is where the real work is -- and some of those
  will be "the page should exist", which turns into writing, not linking.
- **Wire the checker into a gate afterwards, or this returns.** Nothing runs it
  today, which is exactly how 495 accumulated. Same gap as
  `filelist_registry.py --check` (see [[filelists]]).

---

## DOCREV-014 — emoji sweep: 4512 glyphs across 252 tracked .md files
**Status:** open 2026-07-31; scope and figures corrected the same day
**Priority:** P2

The no-emoji rule ([[humanization-voice]], CLAUDE.md, the style guide's
banlist) exists because emojis break the LaTeX path in PDF generation and read
as unprofessional in a formal spec.

**Measured 2026-07-31 over every git-tracked `.md`: 4512 glyphs in 252 of 1310
files.** Use the tool, not a grep -- `bin/review/check_emoji.py` is the single
definition of the class and the reason the first two figures were wrong:

    python3 bin/review/check_emoji.py --all --summary
    python3 bin/review/check_emoji.py docs/markdown/rtl-amba rtl/amba

| area | files | glyphs |
|---|---|---|
| `projects/` | 118 | 2621 |
| `docs/markdown/rtl-amba` | 71 | 613 |
| `vault/` | 12 | 397 |
| `rtl/` beside-code | 8 | 226 |
| repo root | 5 | 215 |
| `docs/markdown/rtl-math` | 10 | 111 |
| `docs/markdown/TestTutorial` | 6 | 83 |
| `bin/` | 5 | 57 |
| everything else | ~16 | ~180 |
| `docs/markdown/rtl-common` | 1 | 8 (quickstart, with the meta apply) |

Dominant glyphs: check mark 2724, cross mark 424, VARIATION SELECTOR-16 196,
warning sign 161, clipboard 153, open book 143, the traffic-light circles 191
combined.

**Progress in the completed areas, and the residue the sweep's own definition
left (measured 2026-08-11):**

| area | then | now | what is left |
|---|---|---|---|
| `docs/markdown/rtl-common` | 8 | **0** | — |
| `docs/markdown/rtl-amba/gaxi` | 81 | **0** | swept with the humanize apply |
| `docs/markdown/rtl-cdc` | — | 1 | `U+FE0F` in `gaxi_fifo_async.md` |
| `docs/markdown/rtl-math` | 111 | 6 | 5x `U+FE0F`, 1x `✓ U+2713` |
| `docs/markdown/rtl-amba` (rest) | 613 | 531 | untouched books |

The 7 stragglers in cdc/math are the "one definition of emoji" problem in
miniature: the `U+FE0F`s are **orphans** -- invisible modifiers left behind when
the visible glyph in front of them was deleted, so they survive both a visual
proofread and a grep for the glyph you remember removing -- and `✓ U+2713` is a
different codepoint from `✅ U+2705` and was never in the hand-kept set. Sweep
against what `check_emoji.py` reports, never against a remembered glyph list.

Also learned 2026-08-11: **the humanizer never removes emoji and readily adds
them.** The gaxi humanize round came back having introduced 20 glyphs (81 -> 101)
and `check_tag_survival.py` failed it with 3 FATAL. A voice pass can never be
the thing that closes this task; the rule now sits in the humanize brief and the
run_batch wrapper so future rounds stop making it worse.

**Two earlier figures in this task were wrong, and the way they were wrong is
the point.** It first said "110 files under `docs/markdown/`". Both the scope
and the character class were too narrow:

- **Scope.** Every count was globbed from `docs/markdown/`, so beside-code
  `CLAUDE.md`/`README.md` were never in the denominator -- `rtl/common/CLAUDE.md`
  alone holds 33. The voice rules bind those files too.
- **Class.** The sweep and the grep that verified it used the same
  `[\x{1F300}-\x{1FAFF}\x{2600}-\x{27BF}]`, which omits U+2B00-U+2BFF and
  U+FE0F. A verification sharing the sweep's blind spot agrees with itself: 47
  stars, 21 black stars and 196 variation selectors were invisible to both.

Three things make this more than tidying:

- **The humanizer INTRODUCES them.** The cdc humanize round put checkmarks into
  `apb5_slave_cdc.md` and `apb5_slave_cdc_cg.md`, which is how a rule that
  predates the round gets violated by the pass meant to polish the prose.
  `bin/review/check_tag_survival.py` now makes that FATAL before apply, so the
  inflow is stopped; this task is the backlog it leaves.
- **Arrows are NOT in scope, and neither is the rest of the technical
  typography.** The first version of the checker swept U+2190-U+21FF and
  flagged 15 pages of legitimate state-transition and navigation arrows.
  Measured across 54 rtl-common files, the non-ASCII that MUST survive: 713
  OVERLINE (waveform diagrams), 191 arrows, 178 box-drawing, 174 em dashes,
  160 middle dots (the doc header separator), plus math operators, Greek, and
  super/subscripts. `check_emoji.py` records these exclusions with the reason;
  do not widen the class without reading them.

Do it per area as that area is humanized, not as one repo-wide sed: a status
marker usually wants replacing with words ("verified", "not supported"), not
deleting, and that is a per-line judgement.

**rtl-common: DONE 2026-07-31** (except `quickstart.md`, swept with the
`_meta` unit). 65 glyphs across 9 pages. What the per-line judgement bought,
and why a blanket delete would have been wrong:

- `✅`/`❌` leading a bullet or a heading carried nothing the words did not
  already say ("Appropriate Use Cases", "Anti-Pattern 1") -- deleted.
- **`⚠️` in the same list did NOT.** `arbiter_round_robin_weighted.md` listed
  three `✅` fits and one `⚠️` caveat under one mode; deleting all four glyphs
  turns the caveat into a fourth reason to use it. Those became `Caveat: ...`.
- `✓`/`✗` in a capability table became `Yes`/`No`, which reads better than the
  glyphs did and survives the PDF path.
- Trailing `✓` on a worked-example result became `(correct)` or fell away with
  the sentence rewritten.

**The humanize pass is INCONSISTENT about them -- do not rely on it either
way.** Measured across the same round: the four module-page units kept all 56
glyphs (56 before, 56 after, same 10 files), while the `_meta` unit removed
most of its own (`quickstart.md` 8 -> 0, `rtl/common/CLAUDE.md` 33 -> 12). Same
model, same brief, same round. So the backlog cannot be closed by humanizing,
and a page cannot be assumed clean because it was humanized -- measure after
every apply. `check_tag_survival.py` only stops NEW ones arriving.

**Final for the area: 0 across all 55 files** (`docs/markdown/rtl-common` +
`rtl/common` recursively), verified with `check_emoji.py` rather than the grep
that produced the original undercount.

## DOCREV-010 — every docs/markdown book needs index.md + overview.md
**Status:** open 2026-07-25 (Sean)
**Priority:** P2

**The rule** (recorded in [[doc-placement]]): every directory under
`docs/markdown/` carries BOTH `index.md` (the catalogue) and `overview.md` (the
orientation), and the overview links to the index. `assets/` is exempt -- it is
shared header fragments and image dirs, not a book.

**Gaps as of 2026-07-25:**

| Book | index.md | overview.md |
|---|---|---|
| rtl-amba, rtl-common, projects | yes | yes |
| rtl-math | yes | **write it** |
| Scripts | yes | **write it** |
| TestTutorial | yes | **write it** |
| RTLcdc | **write it** | **write it** |

`docs/markdown/RTLcdc/` exists but is EMPTY, and its casing disagrees with the
`docs/markdown/rtl-cdc/` that AMBA-CDC-REORG specifies. Settle on one name when
that book is populated -- do not end up with both. That book is blocked on the
CDC reorg anyway, since its pages have to move out of rtl-common/rtl-amba first.

**Also: the link back from the RTL tree.** Each area's RTL should point at its
book's `overview.md`. It cannot be a `README.md` (banned under `rtl/`, commit
`f7ca848a`), so use the two allowed anchors:
- the `// Documentation:` module header line -- already in 225 of 232 modules
  under `rtl/{common,cdc,math}`. The cdc and math slices are DONE
  (2026-08-12): all 167 math headers point at `rtl-math/overview.md` (the
  IEEE754/BF16_ARCHITECTURE phantoms are gone, fixed in the header
  generators), and cdc's all point at per-module pages. `rtl/common`'s
  index.md-pointing headers remain;
- the area `CLAUDE.md` -- `rtl/amba`, `rtl/common`, `rtl/cdc` and (since
  2026-08-12) `rtl/math` have one; `rtl/integ_amba` still has none.

**Why it matters beyond tidiness:** `build_review_bundle.py` builds a unit per
`_book_*_index.md` and includes `overview.md` plus the pages that index links.
A book with no overview reviews less than it appears to, and `index.md` /
`quickstart.md` are outside the bundle entirely -- which is how rtl-common's meta
docs kept a wrong module count, six relocated modules and a phantom `sync_2ff`
through three review rounds. Pair this with the `<area>_meta` unit from
DOCREV-009.

---

## DOCREV-003 — Final MD-only humanize round
**Status:** open 2026-07-23 — blocked on DOCREV-002

Sequencing is deliberate: accuracy rounds first (DOCS + RTL, so the reviewer has
ground truth), humanize LAST. Rewriting prose over stale content only makes
wrong statements read more fluently — so this is also blocked on DOCREV-001.

Run with `bin/review/run_batch.py humanize`. The docs-only path DOCREV-002 asked
for already exists there; the bundler still emits `RTL.sv` per unit, which
humanize mode simply does not send.

## DOCREV-004 — Back up or retire the off-repo review collateral
**Status:** open 2026-07-23 — **updated 2026-07-28 for the corpus reset**

The pre-reset collateral now lives at
`~/rtl-doc-review/archive-pre-reset-2026-07-28/` (untracked, one disk): the
old results tree (proxy corpus inputs + k3 rounds 1-10) and the run logs.
That archive is the FP-rate baseline for DOCREV-012 and the only copy of the
old critiques outside git history. Decide: keep, prune, or delete once the
reset corpus has its own track record. The active pipeline's collateral
(`~/rtl-doc-review/books/`, fresh `results/`) is regenerable or current work
product; same rule — do not leave anything as the only copy on one disk.

## DOCREV-005 — Enable Kimi from the cloud (key + egress)
**Status:** open 2026-07-23 — prerequisite for running any new round off the workstation

The scripts are endpoint-agnostic ([[kimi-review-rounds]]), but two things
outside the repo have to be arranged before a cloud round can run:

- [ ] **Key as a sandbox secret.** `MOONSHOT_API_KEY` lives in
      `/mnt/data/github/seans-cli-ai-local/config/frontier-keys.env`, untracked
      on one disk. Set it in the cloud environment's secret store as
      `KIMI_API_KEY` — pasted into the secret settings, never into a file, never
      committed, never on removable media. Also set
      `KIMI_BASE_URL=https://api.moonshot.ai/v1` and `KIMI_MODEL=kimi-k3`
      (`kimi-k2` is the local proxy alias and 404s against Moonshot directly).
- [ ] **Egress.** Sandboxes filter outbound network; `api.moonshot.ai` may need
      allowlisting. If the first call hangs or 403s, that is the cause — nothing
      in the scripts can work around it.
- [ ] Confirm the model id is accepted. `kimi-k3` is what `litellm-config.yaml`
      routes to, but no live direct call has been made to verify Moonshot takes
      it unprefixed. `GET /v1/models` with the real key lists the valid ids.

**Not a blocker on the workstation.** Direct-mode rounds run fine here (the
reset cdc round is the proof case); this gates only rounds run from a cloud
sandbox.

---

## DOCREV-007 — README rollout: convert 105 beside-code READMEs to link stubs
**Status:** open 2026-07-24 — pattern established (rtl/common), 104 to go
**Priority:** P2
**Owner:** TBD

The tree has **105 `README.md` files**, and many are 500-1000 line standalone
guides beside the code — `projects/components/README.md` (1062),
`converters/README.md` (719), `rtl/integ_amba/examples/README.md` (698),
`rtl/amba/README.md` (635). Every one is a second copy that rots on the next
structural change, exactly as `rtl/common/README.md` did (claimed 86 modules
after the split left 55). See [[doc-placement]].

**The pattern, already worked once (rtl/common, commit ec6bd81a):**
- [ ] For each big README: move the genuine standalone-guide prose into
      `docs/markdown/<Book>/` (a `quickstart.md` or folded into `index.md`),
      correcting staleness during the move (derive counts, drop content that
      moved elsewhere).
- [ ] Replace the beside-code `README.md` with a link stub, written in voice
      from the template in [[doc-placement]].
- [ ] Repoint referrers (the `# Documentation:` code headers, cross-links).
- [ ] Link-check the moved tree.

**Humanization (Sean, 2026-07-24): every README gets humanized eventually.**
Two phases:
- [ ] **Write in voice now.** Each stub is authored from the [[doc-placement]]
      template in voice, so it starts human. This is the floor.
- [ ] **Bulk humanization pass over ALL READMEs, later.** The stubs included,
      not only the guide prose they shed. This is a real pass, still to be run.
      **Tooling gap:** `bin/review/run_batch.py humanize` only globs
      `books/**/DOCS.md`, so it cannot see scattered `README.md` files today.
      Running the bulk pass means either bundling the READMEs as units or
      teaching the humanizer to target `README.md` directly — decide which as
      part of this task.

Guide content that moves into `docs/markdown/` becomes a bundle-able `DOCS.md`
unit and gets the normal humanize pass with every other page as a side effect.
Contract recorded in [[humanization-voice]] and [[doc-placement]].

**Do not blanket-convert.** Some READMEs legitimately stay: `known_issues/README.md`
is a bug-record index, `boards/README.md` and report-dir READMEs may be local
manifests the tooling or a human genuinely reads in place. Apply the
[[doc-placement]] test (method/second-copy vs local-instruction) per file, not a
mass `sed`.

**Sequence with the doc reviews.** Converting a README that a pending Kimi unit
cites would move the target mid-review; do the area's DOCREV-001 findings first,
then its README, the same order used for the rtl-math move.

---

## DOCREV-009 — Final per-section correctness + humanization pass (whole repo)
**Status:** open 2026-07-24 — the closing gate for the doc effort.
**Subsumed 2026-07-28 by AUDIT-001** (`vault/Tasks/site-audit/`): parts 2-3 of
the site-wide audit are this task, widened with RTL correctness (part 1) and
verification coverage (part 4). When AUDIT-001 goes active, cut this block
there; until then this remains the detailed statement of the docs half.
**Priority:** P2
**Owner:** TBD

Supersedes and absorbs the earlier "final Kimi round" (DOCREV-008). After every
area's findings are integrated and the reorg has settled, do ONE comprehensive
closing pass, **section by section**, across the entire repo — `rtl/*`,
`docs/markdown/RTL*`, **and** `projects/*` when we get there.

**Per section, send EVERYTHING — not just module pages:**
- [ ] Every `.md` in the section: `index.md`, `README.md`, `overview.md`,
      `quickstart.md`, the per-module pages — plus the section's RTL. The
      earlier rounds bundled module-page + RTL only; the meta-docs (index/
      readme/overview) were never reviewed and are exactly where count/structure
      drift hides (see the rtl/common 86-vs-55 case, [[doc-placement]] rule 3).
- [ ] **Correctness check** (`qc`): bundle from the CURRENT tree so paths are
      post-split (rtl-math, moved READMEs), serial, large max_tokens
      ([[kimi-review-rounds]] rules 1-4). Measure results against the tree;
      anything CONFIRMED becomes new DOCREV work. A near-empty round is the goal
      — that is the evidence the backlog is actually closed.
- [ ] **Humanization** (`humanize`) of ALL md files in the section — index,
      readme, overview, module pages — not only the prose docs. This is the
      bulk README humanization from DOCREV-007 folded in: every md, every
      section. Tooling gap to close first: `run_batch.py humanize` only globs
      `books/**/DOCS.md`, so index/readme/overview and scattered READMEs need
      bundling or a humanizer that targets them directly.

**Order:** correctness first, humanization second — never humanize an
un-corrected doc (the voice pass is prose-only and must not be handed known-wrong
content to "improve"). Run it section by section so a bad section is contained,
not smeared across one giant round.

**Gate:** do not start until the DOCREV-013 per-area rounds (cdc, common,
math, amba, projects/components) are done, AND the README rollout
(DOCREV-007) is done so the md set is stable. Needs Kimi enablement
(DOCREV-005) off-workstation. (Pre-2026-07-28 this gate listed the old
backlog areas; the corpus reset replaced backlog integration with the
DOCREV-013 fresh rounds.)
## DOCREV-013 — Fresh per-area qc rounds under the adjudication pipeline
**Status:** open 2026-07-28
**Priority:** P1
**Owner:** TBD

The corpus reset (2026-07-28) cleared every prior round; this task is the
replacement for backlog integration (DOCREV-001, dropped). Each area gets a
fresh qc round under the tightened REVIEWER_BRIEF, adjudicated by
`verify_findings.py` (validated 2026-07-28 on cdc round_1, DOCREV-012).

**Area order (Sean, 2026-07-28; math moved ahead of common 2026-07-29 --
"easiest first"):** cdc DONE, then **math**, common, amba (broken down
further when we get there), projects/components (also broken down when we
get there). After those, assess whether the fpga-specific areas need it.

**Per-area startup checklist** (Sean, 2026-07-28 — the Makefile step is part
of starting each area, not optional prep):

1. **Four-line Makefiles.** The RTL area gets the four-line Makefile
   delegating to `rtl/make/area.mk` (lint/etc. over
   `filelists/$(AREA)_all.f`); the val area gets the four-line Makefile
   delegating to `make/tests.mk` (clean-all + glob-discovered test running,
   TOOL-008). Already in place for cdc/common/math/amba/integ_*; CHECK when
   each new area starts — projects/components areas will need them added.
2. Rebuild the WHOLE bundle from the current tree (rule 1), then regenerate
   the area's `_meta` unit immediately — the bundler deletes it. Then run
   `bin/review/augment_golden_deps.py` on the area's PART units (never the
   `_meta` unit — its RTL.sv is an inventory): doc-referenced but
   non-instantiated modules (reset_sync class) join the bundle as GOLDEN
   ground truth — evidence for claims docs make about them, never finding
   targets (Sean, 2026-07-28; the reset_sync REFUTED-a-real-finding case).
3. qc round for the area, serial, large max_tokens (rules 2-4).
4. Adjudicate the round's findings with `bin/review/verify_findings.py`,
   then human-triage what the verifier does not REFUTE.
5. Integrate; re-round until near-empty — the near-empty round is the
   evidence. Humanize only after correctness is clean.

**Stopping rule (Sean, 2026-07-28): impact, not emptiness.** "Near-empty or
nothing-but-FPs" stays the aspiration, but an area STOPS when the current
round produces nothing trap-class (a claim a user could trust into a design
bug); remaining nit-class stragglers are the AUDIT-001 closing pass's job.
Rationale: three reset-corpus cdc rounds produced 12 real findings with 0
FP and rising subtlety, and amba is ~10x cdc's size — a strict near-empty
rule per area does not terminate. cdc round_4 is its final round under this
policy: triage and fix what it finds, then cdc is DONE.

**After correctness, per area (Sean, 2026-07-28):** (a) humanize the area's
docs ([[humanization-voice]]; correctness first, always); (b) audit the
area's TESTS in a similar fashion — details to be scoped when cdc gets
there (folds into AUDIT-001 part 4).

One area at a time, to completion — the multitasking failure (nothing gets
fixed while a second area runs) is documented in [[kimi-review-rounds]].

### Progress log — DOCREV-013

**cdc (rounds 1-2, 2026-07-28).** round_1: 3 findings, 0 FP, all doc-only
(SYNC_STAGES->N_FLOP_CROSS, 1.25x->1.2x, duplicate `r_q_array` declaration) —
fixed, and DOCREV-012 validated the adjudication pass on them. Confirmation
round_2: 5 findings; triage + verifier: **4 real, 1 FP** (overview.md
"omission" was a non-exhaustive sentence, correct REFUTED). The 4: cdc.md
reset table 4-phase cell (prose said "repeated or dropped"), skid_buffer doc
missing the `DW = DATA_WIDTH` alias line, `reset_sync #(.STAGES(3))` +
`.async_rst_n` example against a module whose params are `N`/`rst_n` (the
verifier REFUTED this one on absent-file grounds — VERIFIER_BRIEF rule 4 now
makes absent-cited-file an automatic UNCERTAIN), johnson2bin "emptying from
the left" vs its own "from the right" (RTL confirms right). All fixed. No RTL
changes in either round.

**cdc (round_3, 2026-07-28) — first golden-deps round.** 5 findings, ALL 5
real (0 FP; verifier: 2 UPHELD, 2 UNCERTAIN, 1 REFUTED — human triage upheld
all five):

- cdc.md read-side-reset "benign, reads empty" — the crossed write-pointer
  copy is a LIVE synchronizer; after any traffic it re-samples gray(K) and the
  K consumed entries are REPLAYED. Rewrote the paragraph + summary-table row
  (the same claim the old backlog fixed on the apb5 pages; cdc.md still had
  it).
- cdc.md mistake #4: "the first transfer is silently lost" — inverted; the
  `src_valid && !src_busy` guard drops the NEW pulse, the first completes.
- fifo_async.md "Multi-stage sync: Reduces MTBF exponentially" — inverted
  (raises MTBF); same claim fixed in TestTutorial/gaxi_multi_field_integration.
- apb4_slave_cdc_cg.md `*_cg_idle` scenario unreachable: APB holds PSEL until
  PREADY, and PREADY waits for the response, so a stalled backend keeps
  pclk_user_valid high — idle never asserts mid-stall. Note rewritten.
- apb5_slave_cdc_cg.md "twice (APB, APB5, AXI5-Stream)" — wrong for APB:
  apb4_slave_cdc_cg has no wrapper r_wakeup (single stage); apb5 does (two).

The REFUTED one (last above) was the absent-evidence failure again:
apb4_slave_cdc_cg.sv was golden in part_01 but the finding was in part_02.
`augment_golden_deps.py` now unions refs across ALL units given (and is
idempotent — re-runs replace the golden section instead of appending).

**cdc (round_4, 2026-07-28) — FINAL under the impact-stop policy.** 5
findings, all real, 0 FP (verifier: 2 UPHELD, 3 UNCERTAIN, 0 REFUTED — rule
4 is routing borderline cases to UNCERTAIN as designed; all three UNCERTAIN
were real on triage):

- cdc.md open-loop "minimum spacing SYNC_STAGES + 1 destination clocks" —
  TRAP-class: at defaults (STRETCH_CYCLES=8, SYNC_STAGES=2) a 3-clock
  spacing is silently swallowed by the capture guard; the real rule is
  STRETCH_CYCLES source clocks. Both occurrences fixed (round_3's
  first-vs-new fix had preserved the bad spacing claim).
- counter_johnson.md shift direction backwards ("lower bits" — the slice
  lands in next_state[WIDTH-1:1]).
- gaxi_fifo_async.md Key Features "2-3 flop" vs its own "4 /
  Ultra-critical" row and "3 or 4" advice (RTL range is 2-5).
- cdc.md two stale line citations into cdc_2_phase_handshake.sv (:182 -> :261
  for w_req_event; :250-251 -> :252-253 for the resets).
- clock_pulse.md example testbench off-by-one vs its own NBA analysis:
  pulses are visible at edges WIDTH+1, 2W+1, 3W+1, so WIDTH*3 edges catch
  only 2 and the example $errors as written. Loop now runs WIDTH*3+1 edges
  with a comment pointing at the NBA trace.

**cdc is DONE (Sean, 2026-07-28):** round_4 was declared the final round up
front; everything it found is fixed above. Honest footnote: it DID produce
one trap-class finding, so a strict reading of the impact rule would argue
for round_5 — the residual risk is accepted and falls to the AUDIT-001
closing pass. Four reset-corpus rounds: 3+4+5+5 = 17 real findings, 1 FP,
0 RTL changes. Next per the plan: humanize cdc, then the test audit
([[test-review]]).

**cdc humanized (2026-07-28, humanize round_3).** All 17 pages of the cdc
review area (12 rtl-cdc pages + glitch_free_n_dff_arn + clock_pulse + the
four apb/apb5 cdc wrappers) rewritten in voice with the unify-structure
prompt; applied after tag-survival passed (0 links/anchors/captions lost in
all 3 units; length ratios 0.97-1.08; 0 broken links after apply).
**Process lesson, now in the handbook:** the round ran from the round_4 qc
bundle, built BEFORE round_4's fixes -- the apply reverted all five. They
were re-applied by hand (the humanizer incidentally fixed the johnson shift
direction itself). The humanize bundle is now ALWAYS rebuilt after the last
correctness integration.

**cdc TEST audit (round_1, 2026-07-29).** 51 findings over 8 units; verdicts
14 UPHELD / 8 REFUTED / 29 UNCERTAIN after three evidence fixes (see
[[test-review]] lessons). Integrated so far: SEED env honored in 179
wrappers (commit 86c91bfc). Remaining batches: (3) REG_LEVEL grids missing
on ~7 cdc tests + 2 docstring/grid mismatches; (4) silent-pass findings
(scoreboard-never-fails, log-only errors, fitted golden, driver
self-filter, reset-read-never-compared) -- the highest-value class, each
needs per-test care; (5) smalls: filelist includes discarded by 3 tests,
Clock stacked per subtest. REFUTED set: 1 wrong (2_phase REG_LEVEL, blob
conflation -- real), 1 defensible (bingray wavedrom HAS TEST_LEVEL), rest
correct.

**math (round_1, 2026-07-29).** 20 findings (7+7+6 across 3 parts; meta had
3), ALL real, 0 FP; verdicts 8 UPHELD / 12 UNCERTAIN / 0 REFUTED with human
triage upholding every UNCERTAIN. Notable: carry_save multi-operand examples
systematically violated the page's own carry-weight rule (fixed and
SIM-VERIFIED against the RTL: 1+1+1+1→4, 7x255→1785, 3x200→600); addsub
ALU_INC computed A not A+1; bf16 latency off by one both ends (RTL banner
comment fixed too -- the only RTL touch, comment-only); BK diagram's black
root is gray in the RTL; bf16 rounding is NOT 'RNE except at ties' (37.5%
of inexact patterns round wrong -- owner decision filed as MATH-001 in the
new vault/Tasks/math area). math needs round_2 under the impact rule.

**math (round_2, 2026-07-29).** 12 findings, integrated at `3a9564a9`. **Two
were my own round_1 defects** -- the dsp `product_pipe` declared in the wrong
example, and bf16 latency's two single-stage rows left at 2 cycles after the
quoted row was fixed to 1. Both are rule-6 sweep-for-the-claim failures, in a
round whose whole job was to confirm round_1. The rest: Kogge-Stone left in
the overview's methodology framing (round_1 under-sweep), HC 16-bit figure
stage-3/4 positions vs the RTL generate conditions, the dadda snippet naming a
non-existent instance, bf16 examples implying a NaN input asserts
`ow_invalid` (it asserts only on 0*inf / inf-inf), and an overview page count
of 29 against 27 module pages.

**math (round_3, 2026-07-29) -- FINAL under the impact rule.** 6 findings,
integrated at `c78bb824`. Two were again mine from earlier rounds (the BK
reverse-fill set missing position 11 -- my transcription of round_2's
enumeration; `math_subtractor` "shares NO port names" overstated -- it shares
`i_a`/`i_b`). One real class the earlier rounds missed: the han_carlson widths
table was **aspirational** -- HC-032 and HC-044 have no users at all, since the
ieee754 adders do exponents and accumulation behaviorally. The table now
carries a measured-usage column. `math_bf16_adder`'s FTZ promise vs the RTL's
wrap-bit overflow priority is filed as **MATH-002** (possible RTL defect).

**math is DONE (2026-07-29):** three rounds, 20 -> 12 -> 6, 38 findings, all
real, 0 FP, one RTL banner comment, two owner decisions (MATH-001/-002).
Still owed per the per-area rule: humanize the math docs, then the math test
audit. Next area per the plan: **common**.

**common (round_1, 2026-07-30).** 5 units (4 parts + `common_meta`), sent as
round_8 of the reset corpus. **18 findings; 17 real, 1 FP.** Verifier after the
evidence fix below: 6 UPHELD / 4 REFUTED / 8 UNCERTAIN — and **2 of the 4
REFUTED were wrong** (`shifter_barrel` modulo, `shifter_universal` WIDTH>=2,
both confirmed against the RTL), so the rule-10 validation rule fired again.
The single FP: `sync_pulse.md`'s Xilinx constraints target `r_sync_reg[0]`,
which is Vivado's name for a registered vector, not a phantom register — the
Intel SDC block correctly uses `r_sync[0]`. Tool-convention class, worth adding
to the brief's known-FP list.

**The `_meta` unit earned its place**: 6 of the 18 came from it, all in pages no
part unit can see. **Two trap-class findings**, both in files a reader acts on:

- `arbiter_round_robin_weighted.md`'s dynamic-weight example writes `4'd15`
  into `r_qos_weights[7:0]`, zero-extending bits `[7:4]`, which sets client 1's
  weight to 0 — and `w_valid_clients[j] = (client_weight[j] > 0)` makes that
  client permanently ineligible. **The identical snippet was in the RTL header
  comment** (`arbiter_round_robin_weighted.sv:228`), which is where the doc had
  copied it from; fixed in both, per rule 6.
- `rtl/common/CLAUDE.md` claimed "all modules use `i_rst_n` or `aresetn`".
  Measured: **28 modules expose `rst_n`, 1 exposes `aresetn`, none expose
  `i_rst_n`.** Its own five examples wrote `.i_rst_n(...)`, which cannot
  elaborate.

Pulling that thread found much more than the round did: **CLAUDE.md's whole
"Common Integration Patterns" section documented modules that do not exist as
described.** `counter_bin` is a FIFO-pointer counter (`clk`/`rst_n`/`enable`/
`counter_bin_curr`/`counter_bin_next`, param `MAX`) with no overflow output,
documented as `.i_clk`/`.o_count`/`.o_overflow` with `MAX_VALUE`;
`counter_freq_invariant` is a microsecond tick generator (`freq_sel`/`tick`),
documented as a timeout timer with `CLK_FREQ_MHZ`/`TIMEOUT_MS`;
`arbiter_round_robin` used `.N`/`.REG_OUTPUT` for `CLIENTS`/`WAIT_GNT_ACK`; and
`dataint_crc` treated `POLY`/`POLY_INIT`/`XOROUT` as parameters when they are
input ports. All four rewritten against the RTL, plus 9 more stale occurrences
swept from the same file. **The `_meta` unit could not have caught these — its
`RTL.sv` is an inventory with no port information.** Closed at `b398f8ae`:
`make_meta_unit.py` now appends the parameter/port header of every module the
meta-docs instantiate (15 interfaces for common), so the confirmation round can
check the corrected examples instead of taking them on trust.

Two process fixes went in with the startup checklist and both are the same
defect class the round hunts:
- The REVIEWER_BRIEF's own book table was stale -- it told the reviewer
  `common` had 57 docs / 56 modules when the tree has 50 / 49 (the math and
  cdc splits). Regenerated from the bundle for every book, with a note that a
  multi-part book means the reviewer is holding a SUBSET, so a count gap is
  not a missing module.
- The `_meta` unit is now built by **`bin/review/make_meta_unit.py`**, not by
  the inline snippet in [[kimi-review-rounds]] that got re-derived per area.
  It picks up index/overview/quickstart/`_book_*_index`/`CLAUDE.md`, and
  `--also-list` records where moved modules went (common's inventory is 49
  plus the 183 now in `rtl/cdc` and `rtl/math`), so "the doc says X lives
  here" stays separable from "X does not exist".

**common (round_2, 2026-07-31).** 23 findings, all `finish=stop` (part_01
escalated once and succeeded). Verifier: **11 UPHELD / 3 REFUTED / 9
UNCERTAIN** — a far healthier spread than round_1's pre-fix 1/4/13, which is
the evidence-packer fix working. **One REFUTED was wrong again** (credits
initialize to the weight — the RTL resets `r_credit_counter[i] <= MTW'(1)`),
making it three wrong REFUTEDs across two rounds. Treat the verifier as a
filter, never an authority.

**Three of the 23 were my own round_1 work**, which is rule 6's confirmation-
round lesson landing on this area:
- the Fibonacci "walks to zero and freezes" sentence I wrote is seed-dependent
  (3 of 15 seeds reach zero; 12 enter a short cycle);
- my "one module exposes `aresetn` (`icg`)" named the wrong module — `icg` has
  no reset port at all, `clock_gate_ctrl` is the one;
- the weighted-arbiter `request` vs `w_req_post` finding was UPHELD in round_1
  and I did not fix it.

The `_meta` interface change paid immediately: `quickstart.md` and `index.md`
carried the same broken integration examples `CLAUDE.md` did, and round_1 could
not see them. That class is now checked mechanically by
**`bin/review/check_doc_instantiations.py`** (`5a9ab654`) — for every
```systemverilog block, resolve the instantiated module and report parameter or
port names it does not declare. Measured after integration:

| area | undeclared names |
|---|---|
| rtl-common, rtl-cdc, rtl-integ-amba, projects, TestTutorial | 0 |
| rtl-math | 4 |
| **rtl-amba** | **161** |

Run it at the START of each area's round — the amba number is the argument.
Two parser traps are recorded in the tool's docstring; both were found by
disbelieving its own output, and both would have made it cry wolf on correct
docs (a direction keyword carrying across commas, and a paramless module's
opening paren swallowing the port list).

Also fixed: three malformed links (`](../index.md]`). The reviewer found one;
the other two were invisible to the link checker, which needs a closing paren
to match at all. Repo-wide sweep now 0.

**Where common stands.** Two rounds, 41 findings, 2 FP. Round_2 produced no
trap-class finding — the two in round_1 (the arbiter weight slice and the
`i_rst_n` claim) have no round_2 counterpart — so under the impact rule common
is a candidate to STOP. Against that: 3 of 23 were my own integration defects,
and a third of round_2 was a class round_1 structurally could not see. A
round_3 would mostly audit this integration.

**common round_2 leftovers, swept 2026-07-31** (second pass over the same
critiques; the integration above covered the doc pages it opened, these were in
files it did not):

- **The Galois zero-seed lockout was the wrongly-REFUTED finding, and it
  shipped.** `shifter_lfsr_galois.sv` has no `|r_lfsr` guard, so a loaded
  `seed_data = 0` parks the register at zero permanently AND parks `lfsr_done`
  high forever (it is the equality `lfsr_out == seed_data`). The verifier's own
  reason said the module's source was not in its evidence — which its brief
  rule 4 makes an automatic UNCERTAIN, not a REFUTED. Documented now. This is
  exactly the cost rule 10 predicts: a wrongly-REFUTED finding is only found by
  the next round, unless someone re-reads the critique.
- `debounce.md` never gave `PRESSED_STATE`'s default (1 = normally open).
- **Five RTL header comments** the reviewer filed under POSSIBLE RTL BUGS, all
  rule-6 sources the doc pages were copied from: `arbiter_round_robin`'s mask
  formula (`~((1 << N) - 1)` where the code computes `~((1 << (i+1)) - 1)`),
  `clock_divider` claiming `counter_bin` is "used internally" when it
  instantiates nothing, `cam_tag`'s `ENABLE = 0` described as "always empty"
  when it gates insertion only, `arbiter_round_robin_weighted`'s
  `.max_thresh({4'd3, 4'd5})` under `MAX_LEVELS(8)` (3-bit fields, so it
  truncates to weights [5, 6] rather than the commented [5, 3]) and its
  "credit counter initialized to its weight value", and `dataint_crc`'s
  "Reset: Asynchronous (immediate to POLY_INIT)" when the `crc` output register
  resets to 0. Swept repo-wide: these were the only occurrences, and every
  other "used internally" claim checked out.
- Two RTL corners filed rather than fixed: **COMMON-014** (`fifo_control`
  defaults `ADDR_WIDTH=3`/`DEPTH=16` violate its own `DEPTH == 2^ADDR_WIDTH`
  constraint; latent, both parents override) and **COMMON-015**
  (`shifter_beat_pack` truncates an over-wide runtime `cfg_beat_bytes_m1` to 0
  in `COUNT_BITS'(w_beat_bits)`, giving silent corruption instead of a stall).

Verified: `make -C rtl/common lint` passes all 49 files,
`check_doc_instantiations.py` is 0 across rtl-common's 53 files.

**common HUMANIZED — 2026-07-31, humanize round_4.** All 55 pages (4 part units
+ `common_meta`), bundle rebuilt after the last correctness commit so the cdc
revert-on-apply trap could not recur. `check_tag_survival.py` gated it and
earned its place on the first real use: `dataint_checksum.md` came back with
`](../index.md]`, the malformed-link class swept to zero that morning,
reintroduced by the voice pass and **invisible to a link checker** (which needs
a closing paren to match at all). It registered only as a link target missing
from the parsed set. 0 pages dropped across both applies.

Three things measured during the apply that change how the next area is run:

- **The humanizer is inconsistent about emoji.** Same round, same brief: the
  four module-page units kept all 56 glyphs, the `_meta` unit removed most of
  its own (`quickstart` 8 -> 0, `CLAUDE.md` 33 -> 12). Never assume either way.
- **A prose-only defect class exists that no checker catches.**
  `check_doc_instantiations.py` reads ```systemverilog blocks, so round_2's
  `REG_OUTPUT` phantom survived in two prose bullets ("Enable pipelining
  (REG_OUTPUT=1) for timing") after the instantiation examples were fixed. No
  arbiter declares it and `arbiter_round_robin`'s grants are already registered
  -- fiction twice. Sweep the CLAIM in prose, not just the code fences.
- **Correctness content must be verified BEFORE apply, not after.** Done here
  by grepping the round output for each fix; the reset tally, counter_bin's real
  ports and the galois zero-seed paragraph all survived, and `debounce`'s
  PRESSED_STATE default came back improved (bullet list -> parameter table with
  a real Default column).

**common emoji: 0 across all 55 files.** See DOCREV-014 for the two scoping
gaps this exposed (beside-code docs were never in any denominator; a
`rtl/common/*.md` glob misses `known_issues/` entirely) and for the corrected
repo-wide figure.

**common TEST AUDIT — bundle built 2026-07-31, NEVER DISPATCHED. Corrected
2026-08-05.** The line here used to read "round_1 dispatched"; it was not. The
evidence: `testqc-kimi-k3/round_1` holds cdc only (8 units) and `round_2` holds
math — there is no `common_*.md` in either, and no `_bundle_snapshot` entry for
common, which is written at dispatch time. There is a `testqc_cdc_r1.log` and a
`testqc_math_r1.log` and never was a common one. What actually happened is what
the rest of this block describes: 48 tests -> 13 units were BUILT at
`~/rtl-test-review/common` and the mechanical baseline was measured. The send
never followed.

Everything the 2026-08-01..05 work fixed in the common test collateral — the
three-level grids, the TB/runner separation, the seeds, the arbiter and
clock_gate defects — therefore came from that mechanical baseline plus local
auditing, **not** from an external reviewer. Common's test collateral had never
been externally reviewed at all.

Dispatched for real 2026-08-05 as `testqc-kimi-k3/round_3` (round numbering in
that results tree is global across areas: cdc=1, math=2), against a bundle
rebuilt the same day — necessary, since 93 of the 98 files in the corpus had
changed since the July build, 37 of them newly created. Bundle rebuilt after the
seed fixes so the reviewer sees the current TBs. Mechanical baseline measured
BEFORE sending, so triage can tell new findings from known state:

| class | val/common |
|---|---|
| no REG_LEVEL grid | 6 of 48 |
| no TEST_LEVEL gating | 16 of 48 |
| randomize with nothing seeding | 0 (was 2, fixed) |
| hand-listed sources, no filelist | 6 of 48 (4 are wavedrom) |

REG_LEVEL and TEST_LEVEL match the 2026-07-28 snapshot exactly (42/48, 32/48),
so nothing has drifted there since.

**Process hazard, recorded because it nearly cost a round:** the doc bundle root
`~/rtl-doc-review/books` is SHARED and `build_review_bundle.py` is `rm -rf` by
design. A second agent rebuilt it mid-round, which deleted the hand-built
`common_meta` and killed unit 5 of the humanize round. No damage -- the four
part snapshots proved byte-identical to the rebuild, so what was sent matched
what the gate compared against, and the regenerated `common_meta` was identical
to its snapshot before resuming. Two agents cannot share one bundle root; give
each its own, or serialise.

**Pipeline review — 2026-07-31.** Reading the whole process end to end before
starting amba produced four changes, all recorded in [[kimi-review-rounds]]:

- **The adjudication pass is demoted to advisory.** Measured over the reset
  corpus, the reviewer's FP rate is 2 in 72 findings, while **4 of the ~7
  REFUTED verdicts the verifier has issued were wrong** (cdc r2 reset_sync, cdc
  r3 apb5 wrapper, common r1 shifter_barrel and shifter_universal). It is not a
  filter and must not be run as one: a REFUTED never drops a finding by itself.
  Its real value is settling mechanical classes, ranking the triage queue, and
  naming missing evidence — three evidence-pack bugs were found that way. The
  verdicts file now says so in its own header.
- **The extractor measurement is tooled.** `verify_findings.py` locates quotes
  before sending and prints the share, so `--dry-run` is the rule-10 pre-flight
  and costs nothing; each verdict block records the evidence it was decided on,
  so a BLIND verdict stays identifiable. Measured post-hoc on round_7 (math
  round_3): 5/6 located, 1 blind.
- **The brief's book table is generated and gated.**
  `bin/review/update_brief_table.py` rewrites it from the built bundle;
  `run_batch.py qc` refuses to dispatch against a stale one. Run it AFTER
  golden augmentation — that is what the reviewer receives (common's parts:
  ~247k -> ~356k tokens).
- **Tool-convention false positives** (the `sync_pulse` Vivado `r_sync_reg[0]`
  case) are now a named class in `REVIEWER_BRIEF.md`.

Process debt noted while measuring: **math round_3 was integrated on human
triage alone — step 4 was skipped**, no `verdicts-*.md` exists for round_7. The
findings were all real so nothing was lost, but the step is unconditional.

### DV-TODO (P3, low): test_fifo_async_wavedrom hand-drives the read side

`val/cdc/test_fifo_async_wavedrom.py` drives `dut.read` directly in all three
scenarios instead of going through the FIFOSlave BFM (test-audit round_1,
clause 5). Parked 2026-07-31 (Sean: low priority): it is a wavedrom
doc-asset generator, so the hand-driving IS the scenario content, and a BFM
rewrite buys little. Revisit only if the FIFO's read protocol changes.

**common TEST AUDIT round_3 — dispatched and integrated 2026-08-06.** The area's
FIRST external test review (see the correction above: the July round was built
and never sent). 13 units, `testqc-kimi-k3/round_3`, against a bundle rebuilt
that day — necessary, since 93 of the 98 files in the corpus had changed since
July, 37 of them newly created.

**35 findings: 30 CONFIRMED, 5 SUSPECTED. Adjudication: 25 UPHELD, 9 UNCERTAIN,
1 REFUTED.** Extractor located 33/35 quotes (94%), one BLIND. Every finding
triaged; none dropped on a verdict alone.

**The round's headline was a tool that lied.** `check_test_levels.py` decided
the depth half with `'TEST_LEVEL' in <test text + TB text>` — a substring
search satisfied by the name in a comment — and reported common **48 of 48
compliant**. The true figure was **32 of 48**: seven wrappers never exported
TEST_LEVEL, eight pinned `test_levels = ['full']` in all three REG_LEVEL
branches, and one exported a varying value to a TB that never read it. The
reviewer found them one file at a time; the tool had certified every one, and
its green line had been quoted for four days. Rewritten to check EXPORTED,
VARYING and CONSUMED on the AST — its 16 then matched the reviewer's list
exactly, arrived at independently.

Defect classes found, all fixed:

| class | n | note |
|---|---|---|
| dead depth mechanism | 16 | incl. cam_tag's LEVEL_MULT, written days earlier against a variable nothing exported |
| silent pass / cannot fail | 6 | weighted 80% pass-rate over DIRECTED scenarios; two assertions on cumulative counters; a wavedrom generator emitting zero JSON while logging "COMPLETE" |
| duplicate method definitions | 5 | CamTB and CRCTB each defined the async contract pair twice, shadowed by sync versions defined later |
| hand-listed sources | 6 | converted to filelists |
| naming / crash / seed | 4 | VENDOR=XILINX crashed the wrapper outright |

**Two lessons worth carrying to the next area.**

*Wiring a dead mechanism surfaces real failures.* Exporting TEST_LEVEL for the
first time broke all four wavedrom wrappers with `NameError` — their
`reg_level` lives in a module-level helper, not the test function. Checking
that the definition preceded the use by LINE NUMBER said it was fine; they are
different scopes.

*A parser and a reviewer catch different things, and both are needed.* An AST
scan for duplicate method definitions found `CamTB.main_loop` defined twice,
which the reviewer missed; the reviewer found every semantic gap the parser
could not express. Where they overlapped they agreed exactly.

**The single REFUTED verdict was wrong** — the fourth on record. It refuted
"weighted FULL is GATE re-labelled"; `LEVEL_MULT` genuinely had one call site
and the seven weight scenarios genuinely ran at a fixed `target_grants=1000`
at every level. Rule 10 (a REFUTED never drops a finding by itself) paid for
itself again.

Left open: COMMON-020 (wavedrom constraints, P3, no consumer broken today).
Verification after integration: gate 75/75, func 208/208, full 925/925.

**common TEST AUDIT round_4 — 2026-08-06/07.** Re-round after integrating
round_3, scoped with the new `build_test_review_bundle.py --tests` filter to
the 22 tests whose runner OR TB chain changed: 9 units instead of 13. The list
must be computed from the TB chain, not from changed test files — `cam_testing`
and `crc_testing` were the two most heavily rewritten files and sit under
wrappers that barely moved.

**7 findings, against round_3's 35** — the shape a re-round should have.

| disposition | n |
|---|---|
| known and tracked (COMMON-019 x2, COMMON-020) | 3 |
| already fixed while the round was in flight | 1 |
| genuinely new | 3 |

**Two of the three new ones were defects I introduced integrating round_3**,
which is the entire argument for re-rounding:

- The ACK-mode grant target I scaled to 2500 for FULL is counted by filtering
  `monitor.transactions` — a `deque(maxlen=1000)`. The count SATURATES, so the
  target was unreachable and every ACK scenario exited on its 25,000-cycle
  safety cap instead. Weighted full 252s -> 132s once it stopped burning
  cycles against a cap it could never clear.
- `shifter_lfsr_galois_sequence`'s depth mechanism was still dead after I
  "fixed" it: I exported TEST_LEVEL to satisfy check_test_levels.py, the TB
  read it, and nothing used the result — `LEVEL_MULT` computed and never
  referenced, and the level-dependent default on COUNT unreachable because the
  wrapper always passes TEST_COUNT.

That second one is the same lesson a THIRD time. The check has gone *is the
string present* -> *is the name read* -> *is it exported, varying and read*,
and a mechanism still passed all three while driving no work. **Exported and
read is not DRIVES WORK.** The next refinement worth making is a dead-store
check: a name derived from TEST_LEVEL that is never subsequently referenced.

Third new finding: the weighted walking test logged "✓ successful" for every
client unconditionally, because `ArbiterMaster.manual_request` returns normally
when no grant arrives. Now asserts the client's grant count moved;
mutation-checked.

**Blocked mid-round by a shared-infrastructure break from another agent.** An
uncommitted edit to `bin/TBClasses/shared/tbbase.py` inserted a new method
directly beneath `convert_to_int`'s `@staticmethod`, giving the new method a
doubled decorator and stripping `convert_to_int`'s. 118 TB files call
`self.convert_to_int`; every test in the repo raised
`TypeError: takes 1 positional argument but 2 were given`. Repaired in place
(their function untouched, decorator restored) and left UNCOMMITTED, since the
file carries their in-flight work. **Two agents editing one shared file is the
same hazard as the shared bundle root, and it cost longer here because the
failure looked at first like my own change.**

Verification: gate 75/75, func 208/208, full 925/925, no skips or reruns.


**math TEST audit (round_1, 2026-08-06).** 173 findings over 34 units;
triaged by class and integrated: SEED two-line variant swept repo-wide (124
files); filelist class closed as MATH-003 (all 119 tests build from
filelists now); levels class closed as MATH-004 (level normalizer +
grid fixes); semantic class fixed with mutation checks (RNE checker,
clamp bit-exact, Goldschmidt zero-window + flag checks, carry_save i_c
stimulus, vacuous main_loop, sigmoid prose, create_view_cmd FST name,
johnson2bin/4-phase/open_loop/gaxi cdc items from the earlier cdc round).
carry_save PARAM_N was a false alarm (fixed module is 1-bit by design).
Remaining: MATH-001 (bf16 multiplier RNE, RTL fix directed by Sean).

**common TEST AUDIT round_5 — 2026-08-08. FINAL for this area.** Scoped with
`--tests` to the six common tests whose logic changed since round_4, plus
`test_sync_pulse` from val/cdc -- a test I wrote from scratch and common's own
until that morning. 4 units. The 48 wrappers whose only change was the
identical 3-line coverage insertion were deliberately excluded, as was
`bf16_testing.py` (the math agent's file).

**5 findings. One of them is wrong, and finding that out cost a live break.**

`sync_pulse` came back **CLEAN** -- the unit I most wanted checked, being the
only module test I authored outright. The reviewer verified both level
mechanisms move real work (8/24/80 pulses), the seed chain is intact and
actually consumed, the assertions can fail ("a DUT that drops, duplicates,
stretches, or invents pulses fails"), the monitor samples clear of the clock
edge, and the timeout is ~100x the worst-case runtime. It also noted the one
EXCLUDED scenario -- back-to-back toggling, which a toggle synchroniser cannot
sustain by construction -- is disclaimed in the docstring rather than silently
omitted. A documented scope decision reads differently from a hidden hole, and
that distinction is the whole point of this exercise.

**The walking-requests finding was real and the carve-out was hiding a genuine
defect.** The ACK branch warned instead of asserting, on the recorded grounds
that the per-client counter was "a measurement artifact, not starvation". It
was not. Disabling every client while one still owed an ACK stranded
`grant_valid` for the rest of the run -- the same root cause fixed in the
weighted TB's saturation phase -- so the arbiter genuinely never granted.
Measured: `[27,27,25,32] -> [27,27,27,32]`, one client of four served, while
the compliance model reported ZERO errors throughout because the arbiter was
behaving correctly with nothing to arbitrate. With a drain in place:
`[27,32,31,31] -> [30,34,33,33]`, all four served, 6/6 clean, and a mutation
that skips one client's window fails with `client(s) [1]`.

**The stacked-clock finding is FALSE, and acting on it broke every suite.** It
reported that six `@cocotb.test` functions each start a Clock on one dut.clk
and leave six unsynchronised drivers. cocotb CANCELS every coroutine a test
started when that test ends -- the clocks do not stack, and the per-test start
is the mechanism, not a bug. A class-level guard in `TBBase.start_clock` left
tests 2..N with no clock: counter_bin_load went from 1.4s to spinning at 100%
CPU on an edge that never came. Reverted, with the reasoning recorded on the
method. **Third plausible-but-wrong claim of the week to survive reading and
die on execution**, after the shifter_universal X-select test that passed while
exercising select=00 and ACK mode's "0 errors" that meant "not checking".

Remaining three were mine and small: shifter_universal's FUNC row mapped to
TEST_LEVEL='full' (orphaning every 'func' branch in its TB), counter_freq_
invariant's docstring still described the pre-strategy grid, and an
unrecognised REG_LEVEL built the FULL parameter set at gate depth.

**Process hazard, recorded because it reached main:** the broken guard was
UNCOMMITTED in the working tree when the math agent committed MATH-004. Their
`git add` swept it into da911640 and pushed it -- a broken change of mine, in
the history under someone else's commit message, live for about twenty
minutes. Two agents sharing one working tree means an uncommitted experiment
is not private.


---

## State of the areas -- cdc and math (logged 2026-08-09, Sean's request)

### cdc -- DONE

| Phase | State | Evidence |
|---|---|---|
| Critique (qc rounds) | 4 rounds, 17 real findings, 1 FP, 0 RTL logic changes | rounds 1-4 of the reset corpus |
| Doc correctness | all integrated | commits d121f123 and predecessors |
| Humanize | 17 pages applied; tag-survival clean (0 links/anchors/captions lost), 0 broken links, prose emoji stripped | humanize round_3; 43abf412, 18d0f7a6 |
| Tests (testqc round_1) | 51 findings triaged, all batches integrated; regression green gate/func/full | SEED sweeps (86c91bfc, 29900e1b), grids+vocabulary (dfe2e457, d6c72890), silent-pass class (4af3708b, 5d6d9b23, f0e68e06, 69cf2a7a, 0eeb0a8f, 97b86eed, c44c94f1), smalls (f798b801, 4c9bb752) |
| Open items | one P3 deferred (test_fifo_async_wavedrom hand-drives the read side -- wavedrom generator, Sean parked it) | docs-review open.md DV-TODO |

### math -- RE-SCRUBBED AND RE-HUMANIZED 2026-08-19..21 (post-update cycle)

The 2026-08-10..13 RTL wave (MATH-001/008/009, generator back-ports, header
sweep) invalidated the July certification, so the full loop re-ran:

| Phase | State | Evidence |
|---|---|---|
| Critique | rounds 5/6/7 of the corpus: 11 -> 10 -> 6 findings, STOP per the impact rule (nothing trap-class; part_03 clean twice) | commits 16e4c18b, 43b26620, c6e2ffc5 |
| RTL found | shifter_barrel no-wrap shifts wrong at/beyond WIDTH -- carried a PASSING formal proof whose model restated the RTL's mod arithmetic ("matching RTL"); fixed with IEEE saturation, un-tautologized formal + directed TB, mutation-proven both ways. En route: the mixed-signedness ternary trap (>>> silently degrades) caught by the new independent model | shifter_barrel fix commit |
| New page | mod_3_compress.md was OUTSIDE the book index, the PDF build and every prior review round; round_6 added it, round_7 gave it its first critique | c6e2ffc5 |
| Humanize | 32 pages applied incl. CLAUDE.md; fix-survival verified per unit BEFORE apply and re-confirmed on the tree; tag-survival caught the humanizer's recurring '](../index.md]' malformed-link class (1 FATAL, repaired, re-gated); post-apply checks all zero | e0ff79ee |
| Ops notes | large humanize units need KIMI_TIMEOUT=7200 (die thinking on the 1h default); run_batch --resume fills gaps only | |

### common + cdc -- POST-JULY-28 UPDATE CYCLE DONE 2026-08-22 (Sean: "run the common/cdc files updated since July 28 throught the critique/humanize flows")

| Phase | State | Evidence |
|---|---|---|
| common critique | rounds 8/9: 12 -> 6, converged (round_9 all doc nits) | 2f3ae653, 45c7fcc3 |
| common RTL found | shifter_barrel npo2 rotate fold was plain $clog2-truncation (modulo 2^k, NOT modulo WIDTH); fixed with truncate + one conditional subtract (exact since trunc < 2*WIDTH), permanent WIDTH=11 FULL-grid row, pre-fix directed test FAILED 10/10 | 2f3ae653 |
| common notable | LFSR seed-behavior claims ENUMERATED not patched: WIDTH=4 [4,3] Fibonacci = 3 freeze (1..3) / 3 revisit so lfsr_done asserts (6,11,13) / 9 cycle; the galois page's copy described the FIBONACCI module, and Galois itself measures MAXIMAL (all 15 seeds full period) | 45c7fcc3 |
| common humanize | 31 pages; fix-survival grep-verified pre-apply; tag-survival caught the recurring `](../index.md]` class again (1 FATAL, repaired) | 465ab9f3 |
| cdc critique | rounds 10/11 (first full review of the standalone cdc book incl. sync_pulse.md): 8 -> 4, meta unit clean, zero RTL logic | 516d43d0, 2763905a |
| cdc notable | apb4_slave_cdc.md's DEPTH-elaboration analysis predated the gaxi_skid_buffer {2,4,6,8} guard (raw DEPTH bypasses the FIFO floor and hits the skids; legal set {2,4,6,8}, Johnson only buys 6); round_11 then caught round_10's own kept shorthand -- pointer widths follow the FLOORED max(DEPTH,4), so default DEPTH=2 pays 4-vs-3 bits, not 2-vs-2. Same fixes mirrored into 5 wrapper .sv header comments (comment-only, diff-verified) | 516d43d0, 2763905a |
| cdc humanize | 19 pages + brief table (unit scope pulls in 4 APB slave-CDC pages + rtl-common clock_pulse); fix-survival verified; tag-survival caught `](../index.md])` -- THIRD consecutive humanize round with this defect class, gate catches it every time | 42630ad3 |
| Ops notes | run_batch refuses a qc dispatch on a stale brief table (rebuild bundle -> make_meta_unit -> update_brief_table -> dispatch, in that order); one engine_overloaded transport failure resent via --resume per the client's remedy text | |

### math -- DONE; all MATH-001..009 closed (open.md/active.md empty; stale rows below corrected 2026-08-22)

| Phase | State | Evidence |
|---|---|---|
| Critique (qc rounds) | 3 rounds, 38 findings, all real, 0 FP; converged 20->12->6 | rounds 5-7 of the reset corpus |
| Doc correctness | all integrated (carry_save rewrite sim-verified against RTL; addsub INC; bf16 latency both ends; BK diagrams; Kogge-Stone sweep; HC usage table) | 3b0513db, 6725c6dc, d5880a05, b2deeb75, 16d3959b, 9b1604ba, aef82d2d |
| Humanize | 29 pages applied; tag-survival clean; 0 broken links; prose emoji stripped | humanize round_5; 11f32089 |
| Tests (testqc round_1) | 173 findings triaged by class and integrated | SEED two-line variant (29900e1b), MATH-003 filelists CLOSED (134 generated + 24 repaired; all 119 tests converted; gate 119/119 func 134/134; 276de494), MATH-004 levels CLOSED (normalize_test_level sweep of 22 sites + grid fixes; b3c0aa23), semantic class (RNE checker shift-aware + directed cases; clamp bit-exact; Goldschmidt zero-window + flags; carry_save i_c stimulus; vacuous main_loop; sigmoid prose; create_view_cmd FST name) |
| MATH-002 | CLOSED -- bf16 adder underflow reported +inf (wrap bit shared by both flags); RTL fixed, directed FTZ regression added, mutation-checked | 650fe622 |
| MATH-001 | CLOSED -- bf16 multiplier textbook RNE (guard + true sticky export, G & (R\|S\|LSB)); sweep-verified 0/5000 vs exact reference; fp32 pair fixed identically; docs updated | vault/Tasks/math/closed.md |
| MATH-005 | CLOSED -- math_mod_3_compress final formal checks done | vault/Tasks/math/closed.md |
| MATH-006 | CLOSED -- (this row misdescribed it: the fp16/fp8 RNE sweep was MATH-007, closed false-alarm with exhaustive evidence). MATH-006 = full math formal suite re-run after the .sby path repair: 157 PASS 2026-08-11 | vault/Tasks/math/closed.md |
| False alarms | carry_save PARAM_N (fixed module is 1-bit by design) | triage note in round_2 record |

### Cross-area process state

- Pipeline proven: tightened reviewer brief + golden deps + second-model
  adjudication (verify_findings.py with per-finding blocks, normalized quote
  location, identifier grep, test skeleton) -- 0 FP across the last five doc
  rounds, verifier REFUTED-set errors all traced to evidence gaps now fixed.
- Stopping rule: impact-based, near-empty aspiration (Sean 2026-07-28).
- Hard requirements recorded 2026-08-03: TB separate from runner; every test
  has gate/func/full (both REG_LEVEL grid and honest TEST_LEVEL depth).
- math test style: directed patterns for full functional coverage, not
  exhaustive sweeps; non-exhaustive stimulus is never a finding.
- Next area per the order: common (with the other agent), then amba
  (decomposed), then projects/components, then assess fpga areas.

---

## State of the areas -- gaxi and shared (logged 2026-08-11, Sean's request)

amba is being taken one book at a time rather than as one unit; `gaxi` and
`shared` were split out of the old combined book (58967753) so they round-trip
independently.

### gaxi -- DONE (RTL, tests, docs, humanize)

| Phase | State | Evidence |
|---|---|---|
| Critique (qc rounds) | 2 rounds, 13 then 7 findings. round_2 was worth running: 5 of its 7 were residue of round_1's own claims (the phrase was spread wider than the findings enumerated) and one was a regression I introduced while fixing an overgeneralization | rounds 1-2, `~/rtl-doc-review-amba` |
| RTL | mux-mode addressing bug fixed: `r_rd_addr` took the NEXT pointer, so `rd_ready` re-pointed memory past the entry being accepted -- written A B C D read back C D 00. Every RTL instantiation uses REGISTERED(0), so the broken mode was the only one shipping. Mutation-checked | 37cc9cce |
| Doc correctness | both rounds integrated: zero-latency-bypass claim (5 files, gone since the 2026-04-23 refactor), phantom almost_full/empty ports, false min(N,count) clamp, wrong defaults/widths, undocumented MEM_STYLE, per-module power-of-2 rule | 5725969b, a0694c20 |
| Book structure | own `_book_gaxi_index.md`; all 6 modules linked from BOTH entry points (regslice was an orphan, index.md listed 2 of 6) | 58967753, a7373cc0 |
| Tests | the TB returned its own shadow model as the DUT's answer, so `assert data == expected` compared the stimulus list to itself -- that is what hid the RTL bug through 5 tests x 2 modes x 3 levels. Fixed to read the pin; streaming-drain and fill/random-drop tests added; 8/8 wrappers REG_LEVEL/TEST_LEVEL compliant (area is 40/119) | 37cc9cce, 5725969b, ec15a931, d4ecb410 |
| Coverage | 100% on all five modules at REG_LEVEL=FULL. Earned by stimulus where reachable (slow_consumer profile + random drop took drop_fifo 91.3 -> 100), waived only where illegal-by-construction, each waiver carrying a DEFENSIVE comment | 27b9d981, 17b8abe8, 233a3393 |
| Humanize | round_1 applied: 8 pages, 84 links resolving, 0 emoji | bf63573c |
| Open items | none for gaxi itself |

### axi4 + axi5 -- ARC COMPLETE 2026-08-26 (first-ever reviews + double humanize)

qc rounds 20-23: 74 -> 44 -> 24 -> class-closed (zero RTL findings after
round_20; round_23's assessment: 'nothing that would send an integrator
down a wrong design path'). The plateau at 24 taught the closure lesson:
fix by CLASS exhaustively, not by citation -- per-citation fixes leave
twins and create fresh inconsistencies. RTL fixed: 8 dead clock-gates
(peer-READY activity terms, family-wide, mon_cg siblings' rule), undriven
stub AR counts (both families, widened to [3:0]), WSTRB forwarding, stale
4-bit timeout comment blocks deleted from all 8 mon wrappers (the doc
corruption source), filtered.sv err_select routing myth, buckets identity
comment. Headline doc classes: phantom CG interface (8 pages), phantom
safety capabilities (poison/MTE/ATOP/WLAST/WSTRB/burst checks), inverted+
mismapped filter masks, 4-bit->16-bit-us timeouts, stays-awake/flushed
gating guarantees -> freeze/drop warnings, idle-count power-of-2 tables
(16x sizing error), event_data payload truth (32-bit address only).
Humanize round_8: 44 pages, gates clean (twelve bracket-links repaired --
fifth consecutive round with the class). TASK-070 = remaining RTL
follow-up. Incidents: two more staged-set sweeps by concurrent sessions
(69d220e3 + one earlier), provenance commits pushed both times.

### apb4 -- ARC COMPLETE 2026-08-25 (first-ever review + humanize); apb5 spillover integrated

Rounds 17/18/19: 13 -> 10 -> 5, converged ('well above average in accuracy
and candor'; round_19 independently re-derived every round_18 correction).
Headline doc fixes: both stub pages' paddr/pwdata packing order (guaranteed
integration failure), the slave's latency mis-model (>=4 wait states /
6-cycle minimum through both registered skid rd_valids, not 2/4), README
one-sided-reset claim, monitor page brought forward a generation. RTL fixed:
STRB_WIDTH = 32/8 -> DATA_WIDTH/8 (slave + cg). RTL FILED with traces:
TASK-066 (monitor slot leaks, +disabled-config trigger), TASK-067 (stub
framing FIFO overflow), TASK-068 (P1 CONFIRMED master
response-backpressure bus deadlock -- holds PENABLE forever), TASK-069
(monitor protocol-check false positives on pipelined traffic + live-command
event pairing + active_count drift). Humanize round_7: 10 pages, emoji
38 -> 0, fourth consecutive round emitting the bracket-for-paren footer
link (gate caught it). apb5 spillover (4 findings) integrated ca941b2b.
Skid contract correction (2..8 inclusive, Sean) swept 24 pages + 3 guards
mid-arc, 21c51b36.

### gaxi -- RE-SCRUB COMPLETE 2026-08-24 (post-drift confirmation)

First review since the 08-10 humanize (the signal-prefix sweep and skid
DEPTH guard landed after it). Round_15 -> round_16: substantive -> 3 nits.

| Item | Outcome |
|---|---|
| RTL: dbldrn rd_valid corner | double drain from EXACTLY 2 held rd_valid on empty; streaming consumer's accept underflowed count 0->15, wedged until reset. Fixed (count==2 term excludes dbl-drain-without-write), RED 4/4 -> GREEN 4/4 via new double-drain-to-empty scenario (8b760a10) |
| RTL: dbldrn DEPTH guard | added, mirroring base module; verified firing at -GDEPTH=16 (was comment-only with the same 4-bit wrap) |
| RTL: drop FIFO bounds check | the header PROMISED 'checked in simulation'; no check existed. Now a real capture-edge $error; header + doc disclosure synced (5f240490) |
| Docs | 9 findings across the two rounds: self-contradicting ALMOST-margins guidance, dbldrn storage-style claim, regslice latency-differentiation contradiction, README drop-FIFO latency row (flop=2), phantom 'transaction logging' feature, DEPTH=1 'any depth' overstatement (verified failing), + 3 example/format nits |
| Humanize | NOT re-run -- the 08-10 voice pass stands; integration edits are localized and voice-matched |
| Suites | dbldrn/skid/drop/regslice 18/18 clean builds |

### shared -- ARC COMPLETE 2026-08-24 (correctness + tests + humanize)

Resumed post-observer-unblock as rounds 12/13/14 (qc rounds 5-7 of the arc):
14 -> 8 -> 8. Round_12 = docs lagging 537c7af8 (14 findings) + the splitters'
two-process sticky-overflow write (fixed, single dedicated process,
c3b84d0c). Round_13 = residue/nits (5a5d82c8). Round_14 caught the REAL one:
the rd splitter's owed-beat RLAST counter is single-transaction state and a
second admission mid-flight reloaded it -- fixed with the r_rbeats_active
acceptance fence mirroring the wr side, mutation-proven via a new
back-to-back TB scenario (landed inside the converters session's 426e2fb8 --
see incident 5 in the worktree note; provenance commit 1de8ad18). Humanize:
28 pages, all survival gates clean first pass (da44a07c). Arc totals:
correctness rounds 2/3/4 + 12/13/14, SEVEN mutation-proven RTL fixes, all 21
modules tested (TASK-062), TASK-060/061/063/064 closed.

(Previous save-state record follows for history:)

### shared -- CORRECTNESS NEARLY DONE (updated 2026-08-13, Sean's "save state")

Fresh rounds re-run from this machine's tree (the round_1 collateral lived
only on the other machine; per Sean, if the mods can't be found, nothing was
done -- so the cycle restarted clean). Convergence: **29 -> 14 -> 10**.

| Phase | State | Evidence |
|---|---|---|
| Critique | rounds 2/3/4 dispatched, adjudicated (r2: 19 UPHELD/0 REFUTED/12 UNCERTAIN, extractor 100%), triaged, integrated | `~/rtl-doc-review/results/qc-kimi-k2/round_{2,3,4}` |
| RTL defects fixed | SIX, each mutation-proven RED->GREEN on clean rebuilds: (1) master CRC accumulate strobe tied off -- constant 0x00000000, integrity compare vacuous; (2) writer CRC captured 2 cycles early; (3) LFSR tap defaults not maximal, 8-bit ID set parks at zero from seed 0x01 -- library-table primitive sets now, family-wide incl. dma_slaves/AXIS pair; (4) convert dropped WSTRB (blocking-order guard) -- partial writes clobbered whole APB words; (5) sdpram_core WRAP mask shrank mid-burst (len = remainder, now latched); (6) rd_crc_check stray-beat drain detected pin-side, parked the stray in the skid, poisoned the next run | 494fe520, 058b3ae0 + suite evidence in messages |
| RTL defects filed | TASK-060 (observer, left alone per Sean), TASK-061+063 (splitter cluster: block_ready duplication, final-split BRESP lost, per-split RLAST, silent FIFO drop, unfenced consolidation, leading-W), TASK-064 (read-path PSLVERR loss; peakrdl held-req contract) | vault/Tasks/amba/open.md |
| Tests | ALL 21 shared modules covered (Sean: "all of the shared modules need tests"): 8 new suites over the 7 uncovered (TASK-062 CLOSED -- board-deployed sdpram axil_axil now simulated); software mirrors, REG/TEST_LEVEL grids, SEED, mutation evidence per suite; area sweep **246/246** clean build | ed1319a6 |
| Doc integration | rounds 2/3/4 fully integrated with read-back verification; README 996-line second copy -> pointer map; STATUS tracking un-rotted; shims Location fixed (all four pages pointed at a directory with no RTL) | e8ba4962, 27ce2732, 058b3ae0 |
| Guard rails added | gaxi_skid_buffer DEPTH elaboration guard ({2,4,6,8} is the PERMANENT contract -- Sean: "skid buffer will never be more than 8 deep"); shim partial-strobe regression; stray-beat scenario | 058b3ae0 |
| Humanize | NOT STARTED (correctness first, and round_5 is deliberately held) | -- |

**UNBLOCKED 2026-08-21: the observer rework LANDED as a deletion.**
axi4_dma_observer (module + doc page) is gone, replaced by
axi4_intf_master/slave_observer in projects/components/misc; TASK-060 closed
obsolete. The dedicated-observer-unit plan below is MOOT for shared -- the
successors belong to the misc book and get reviewed there. Shared's round_5
re-critique can proceed with the current 24-page book. (Original held plan,
for context:) Plan agreed: (a) wait for the update to land; (b) re-sync
axi4_dma_observer.md; (c) build a DEDICATED observer unit carrying its FULL
monitor cone -- part_01's closure did NOT include axi_monitor_base/filtered or
axi_perf_latency_hist (documented in another part), which is exactly why the
observer's own o_cmd_block defect was invisible to its reviewer; golden-deps
auto-skips shared (47 > 25 scale guard), so hand-scope the unit like a _meta;
(d) spin that unit alone (--only, rebuild-all-send-subset) until clean --
likely a couple of rounds; (e) round_5 over the rest of shared; (f) humanize
from a bundle rebuilt AFTER the last correctness commit. Close TASK-060
against the measured tree only (elaboration passes, the 249th GATE test
green), not the incoming commit message.

**Monitor-restore incident (context, not mine):** 1e6b1d9d (stream agent,
2026-08-12) stripped the ID-range filter feature from axi_monitor_base
(6e95cbab's feature -- per-instance ID slices are the only way parallel
monitor snooping closes timing). Restoration was in-flight, uncommitted, in
the shared tree as of 2026-08-13; my footprint has zero overlap. See
[[multi-agent-worktree]] for the discipline this week bought.

### Process changes made while doing this

- **The no-emoji rule was never in the humanize prompt.** It lived in the
  handbook, a commit message, and the reviewer's head. The gaxi round came back
  having ADDED 20 glyphs and failed the gate with 3 FATAL. Both rules -- no
  emoji, and a NAMED canonical `##` section list -- now sit in
  `kimi_humanization_style_guide.md` and the `run_batch.py` wrapper. "Unify the
  headings" without naming the target set had let each round invent its own
  self-consistent scheme, which is why the finished areas are internally tidy
  and mutually inconsistent.
- **`bin/review/check_doc_structure.py`** added: reports per-area heading drift
  so "does this area need re-humanizing?" has a number. Its answer for
  common/cdc/math/gaxi is **no** -- the deltas are mechanical renames
  (`Implementation Details` -> `Functional Description` x30 in common) plus one
  real content gap (DOCREV-016), and a scripted rename is cheaper and safer than
  a voice pass that rewrites everything to fix section names.
- **Framework upgraded 0.6.1 -> 0.6.3** on this box; `val/amba` could not
  collect before it (`create_apb4_wavejson_generator` missing).

### What comes next on amba

shared: integrate the 23 CONFIRMED, decide the 6 SUSPECTED, then humanize with
a bundle rebuilt after the last correctness commit. The remaining books
(monitor, axi4, axi5, axil4, apb, apb5, axis4/5) have not had a round at all --
174 of the 182 amba pages, and 531 of the emoji in DOCREV-014's amba row.

---

## DOCREV-016 — `Testing` section missing from most common and math module pages
**Status:** open 2026-08-11
**Priority:** P2

`bin/review/check_doc_structure.py` (added 2026-08-11) reports a required
section absent at scale:

| area | pages missing `Testing` |
|---|---|
| rtl-math | ~~29 of 29~~ **0** (closed 2026-08-12: real suites named per page, docstring-extracted scenarios; no-dedicated-test blocks say so honestly and point at the structural/formal coverage; catalog and overview pages carry pointer sections) |
| rtl-common | 33 of 49 |
| rtl-cdc | ~~5 of 12~~ **0** (same pass) |

The same pass applied the checker's mechanical renames across both books
(32 pages: Functionality/Theory of operation -> Functional Description,
Design Considerations -> Design Notes, Verification -> Testing, case fixes)
with a guard against creating duplicate headings. Remaining structure drift
in math/cdc is a PAGE-TYPE question, not missing content: family/catalog
pages (math_fp8_modules, cdc.md) can never carry a per-module Parameters
table, and index.md TOCs should join _book pages in the checker's exempt
set. Decide page types in the checker before chasing 0/29-conformant.

`module-doc-template.md`'s completion checklist requires a test file reference —
location plus the command to run it. **No humanize round can fix this**: the
voice pass rewrites prose it is given and cannot invent a test path it was never
told. It needs the real `val/<area>/test_<module>.py` path per page, which is
mechanical (the file either exists or the module has no test, which is itself
worth knowing).

Distinct from the heading-name drift the same tool reports — those are renames
(`Implementation Details` -> `Functional Description` x30 in common,
`Design Considerations` -> `Design Notes` x22 in math) and can be scripted
without touching prose. This one is missing content, not a wrong name.

**Work:**
- [ ] Add `## Testing` to each page with the test path + run command.
- [ ] Where no test exists, say so explicitly rather than omitting the section —
      an absent section reads as an oversight, a stated gap reads as a fact.

---

## DOCREV-017 — The five HAS/MAS books: qc rounds, then humanize
**Status:** open 2026-08-20 (Sean)
**Priority:** P2

The component books queued for correctness first, voice second. This is the
`projects/components` slice of [[DOCREV-013]], decomposed to the five books
that actually exist as HAS/MAS today.

| Book | Words | qc round | humanized |
|---|---|---|---|
| Bridge MAS | — | **none recorded** | 2026-08-11 (`93eed6f1`) |
| Bridge HAS | — | **none recorded** | 2026-08-11 (`93eed6f1`) |
| Converters MAS | — | **none recorded** | 2026-08-11 (`93eed6f1`), 19 files |
| APB Crossbar MAS | 7,154 (5 md) | none | **never** |
| APB Crossbar HAS | 8,179 (20 md) | none | **never** |

### Two problems, not one

**Three books were voice-passed without a correctness round.** Searching the
docs-review area for a bridge or converters qc round returns nothing; the
2026-08-11 humanization ran anyway. That is the failure shape
[kimi-review-rounds](../../handbook/authoring/kimi-review-rounds.md#the-order-correctness-until-clean-then-voice)
names outright: a voice pass rewrites every page, so voice-passing a page that
is still wrong "produces a well-written falsehood, and the rewrite makes the
error harder to spot later because it no longer reads like something copied
from stale RTL." Their qc round is therefore owed retroactively, and it is
reading prose that has already been smoothed once.

**The two APB Crossbar books have had neither pass.** Not an oversight in
judgement — a timing miss. The `apbx-xbar` doc tree was created 2026-08-12
(`95f7006f`), one day after the humanization pass ran, and nothing has swept
it since.

### Content added after both passes

Written 2026-08-19/20 (`cf3aa7da`), so it postdates every prior round:

- apbx MAS ch1 — APB5 parity section; the generated-vs-thin parameter split
- apbx MAS ch3 — generator arguments the CLI does not expose
- Converters MAS §3.4 — `axi4_to_apb4_shim` parameter table

The converters case is the one to watch: an un-humanized table now sits inside
an otherwise-humanized file, which is where a voice mismatch will show first.

That same commit corrected parameter tables that had documented
`NUM_MASTERS`/`NUM_SLAVES` — parameters no module has — and defaults that were
simply wrong (`AXI_ADDR_WIDTH` 64 vs the actual 32). Both were found by reading
the RTL, not the docs. Treat that as evidence about the qc round's likely yield
on books nobody has checked against source: aim it at parameter tables,
defaults, and module names first.

**Work:**
- [ ] qc round per book, re-run until a round returns nothing actionable or
      only false positives. One round is not a clean bill of health.
- [ ] Integrate findings, verifying each against RTL before acting — a
      mis-packaged bundle produces confident-but-wrong findings.
- [ ] Only then humanize, using
      `docs/kimi_humanization_style_guide_has_mas.md` (the guide the
      2026-08-11 HAS/MAS pass used), gated on `verify_structure.py`.
- [ ] Re-verify the qc fixes survived the voice pass.
- [ ] Rebuild all five books; confirm LoF/LoT/LoW still populate — caption
      encoding (`: caption`, `Figure N:`) drives them, and a rewrite that
      drops it silently breaks book generation.

**Note:** the apbx books are small enough to send un-split. Sizes above are
markdown word counts, not the built page counts.
