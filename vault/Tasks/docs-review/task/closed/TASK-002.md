# TASK-002: emoji sweep: 309 glyphs in 13 tracked .md (843 in 72 files counting code)

> Migrated 2026-09-27 from `vault/Tasks/docs-review/open.md` as **DOCREV-014** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** CLOSED 2026-09-27 -- the owner confirmed the docs-review work is done. No measurement was taken in this session to support that; the basis is Sean's statement, recorded as such rather than presented as verification.
**Status (as filed):** open 2026-07-31; scope and figures corrected the same day.
*History, all superseded by the 2026-09-24 figure below -- the headline is
current, these are not:* 4512 in 252 of 1310 when opened (2026-07-31), then
2979 in 133 of 1397 (2026-09-16). Roughly a third of the glyphs and half the
files cleared between those two, by owners fixing pages for other reasons. The
rule never changed; only the backlog did.

**RE-MEASURED 2026-09-24 with the tool: 309 glyphs in 13 of 1557 files, and
every one of the 13 is `dmas/stream`, `dmas/rapids` or `Genesys2/stream`.**
Outside those areas the `.md` half of this task is DONE -- zero glyphs in
anything not owned by another session.

**The class had a third blind spot, now fixed.** U+2300-U+23FF was absent from
`RANGES`, so hourglass, pause, stopwatch and next-track read as clean; 48 of
them sat in tracked `.md` and this checker reported nothing. Adding the emoji
sub-ranges only (U+231A-231B, U+23E9-23FA) moved the count 263 -> 309 and
exposed 3 files that had always reported clean (`rapids/PRD.md`,
`rapids/TASKS.md`, `stream/regs/README.md`). U+2308-230B stay OUT: ceiling and
floor brackets are live math here. `check_tag_survival.py` imports `is_emoji`
from this module, so the humanize gate tightened with it.

That is the same defect the docstring already described twice -- a definition
that omits a block, and a verification that shares the omission. It is now
recorded there a third time.

**The code file classes were swept the same day, and this checker does not see
them** (`--all` globs `*.md`). Four commits:

| commit | what |
|---|---|
| `6bd5b1912` | 1674 glyphs out of 235 `.py`/`.sh` |
| `167ae7e89` | repaired 42 string literals that sweep had emptied (`"<glyph>"` -> `""`), restored 91 lost in-string indentations, swept 18 glyphs its class had missed |
| `5f2ca09e9` | 518 glyphs from the 13 files held back because their glyphs carried meaning (PASS/WARN/FAIL, accessible/missing, YES/NO), plus 56 from the two pumice docs |
| `4da579e07` | 110 glyphs -- 80 in Makefiles, testplan YAML, `.toml`, `.txt` and two `.sv` comment blocks; 30 in 6 `.md` |

Measured from the four commits: **2279 glyphs out of code files and 86 out of
`.md`**, 2365 in all. `167ae7e89` nets to only 7 because it deliberately put 11
glyphs BACK -- the `EMOJI_MAP` keys, which are data -- while removing the 18 its
class had leaked.

The lesson from the emptied literals is [[silent-fallbacks]] rule 14; the
`EMOJI_MAP` casualty (nine dict entries collapsed to two, emoji stripping dead
for all 30 `generate_*_pdf.sh` callers) is in [[doc-pipeline]].

**Residual, needs a decision.** Nothing gates emoji in `.py`/`.sh`/`Makefile`/
`.sv`. This note already records that the humanizer readily ADDS them and that
`check_tag_survival.py` only guards the `.md` humanize path, so the 2279 glyphs
just removed from code files have no ratchet behind them. A staged-file check over
those classes would close it; not built, because it is new tooling rather than
backlog.

**Generated .docx are out of scope, and that is a decision not an oversight.**
42 tracked `.docx` carry embedded emoji (Bridge_MAS_v1.0 141, UART_16550_MAS_v1.0
101, Bridge_MAS_v1.7 36). None were built during the 85 minutes `EMOJI_MAP` was
broken, and every source book behind them is now clean (Bridge_MAS 23 `.md` -> 0,
UART_16550_MAS 26 -> 0, APB_Crossbar_MAS 5 -> 0), so the glyphs are frozen
history. They are versioned RELEASE archives -- `generate_*_pdf.sh` takes
`--rev`, and eight Bridge HAS/MAS versions coexist from v1.0 (May 14) to v1.7
(Sep 13) -- so regenerating one rewrites what that release was, the same reason
`docs/review/` is off-limits. `Bridge_MAS_v1.7.docx` is in any case already 8
days stale against its sources (built 09-13, newest source commit 09-21); the
next `--rev` picks up clean sources on its own. Do not sweep them.

Measurement caveat for whoever re-counts: read the XML inside the zip, not the
container's bytes. A raw scan reports 168 for Bridge_MAS_v1.0 (141 real) and 107
for APB_Crossbar_MAS_v1.0 (**0** real).

**One deliberate exception, not a miss:** the check mark in
`projects/components/fabric-gen-ip/apbx-xbar/docs/apbx_xbar_mas/assets/graphviz/address_decode_flow.gv`.
That `.gv` is the source for a committed SVG and PNG, and regeneration is not
byte-stable on this box (graphviz rewrites 182 lines including its version
banner), so fixing one decorative glyph would either bundle a whole-asset
rewrite from version drift or leave the shipped diagram inconsistent with its
source.

The shape makes this far more tractable than the raw count suggests: **1700 of
the 2979 are a single glyph**, U+2705 WHITE HEAVY CHECK MARK, with U+274C CROSS
MARK at 248 and U+2713 CHECK MARK at 151. Three characters are ~70% of the
sweep, and all three are status markers in tables and checklists that a
scripted pass can replace with text. The long tail (open book 124, warning 116,
the traffic-light circles, clipboard 84) is what needs judgement.
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
| `docs/markdown/rtl-math` | 111 | 6 | 5x `U+FE0F`, 1x `U+2713` |
| `docs/markdown/rtl-amba` (rest) | 613 | 531 | untouched books |

The 7 stragglers in cdc/math are the "one definition of emoji" problem in
miniature: the `U+FE0F`s are **orphans** -- invisible modifiers left behind when
the visible glyph in front of them was deleted, so they survive both a visual
proofread and a grep for the glyph you remember removing -- and `U+2713` is a
different codepoint from `U+2705` and was never in the hand-kept set. Sweep
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

- ``/`` leading a bullet or a heading carried nothing the words did not
  already say ("Appropriate Use Cases", "Anti-Pattern 1") -- deleted.
- **`` in the same list did NOT.** `arbiter_round_robin_weighted.md` listed
  three `` fits and one `` caveat under one mode; deleting all four glyphs
  turns the caveat into a fourth reason to use it. Those became `Caveat: ...`.
- ``/`` in a capability table became `Yes`/`No`, which reads better than the
  glyphs did and survives the PDF path.
- Trailing `` on a worked-example result became `(correct)` or fell away with
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
