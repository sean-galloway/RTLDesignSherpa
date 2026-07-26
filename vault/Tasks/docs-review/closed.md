<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# docs-review — Closed (done)

_None._

---

## DOCREV-006 — Give math its own docs directory
**Status:** ✅ closed 2026-07-23 — moved, generator repointed, links verified

The RTL split had happened and the docs had not followed:

| | Before | After |
|---|---|---|
| RTL | `rtl/math/` (171) | unchanged |
| Tests | `val/math/` (119) | unchanged |
| Docs | `docs/markdown/rtl-common/math_*.md` (27) | **`docs/markdown/rtl-math/`** |

Math already built as its own PDF book (`RTL_Math_Library`) from its own index;
what it lacked was a directory matching where the RTL lives.

**Done:**
- 28 files moved with `git mv` (27 docs + `_book_math_index.md`) so history
  follows.
- New `rtl-math/index.md`, built from the "Arithmetic and Math Operations"
  section lifted out of `rtl-common/index.md`. Creating it also fixed all 27
  math docs' `](index.md)` sibling links for free — they resolve to the new
  index without edits.
- `rtl-common/index.md` now points at `../rtl-math/index.md` instead of carrying
  52 math links.
- `generate_rtl_pdfs.sh:99-101` repointed. It globs (`ls rtl-math/math_*.md`),
  so there is no file list to maintain.

**Deliberately NOT touched: `docs/review/kimi/`.** A first pass swept the Kimi
round files with the same rename and that was wrong — those are raw reviewer
evidence, and `FINDINGS.md` says in its own header "do not hand-edit the
tables; re-run it instead". Rewriting a critique to match a later
reorganisation destroys the record of what was actually reported. Reverted.

**So the math findings still cite `docs/markdown/rtl-common/math_*.md`.** That is
correct and should stay. The mapping is a 1:1 rename — `rtl-common/math_X.md` is
now `rtl-math/math_X.md` — so citations remain trivially resolvable. Regenerate
`FINDINGS.md` via `bin/review/index_findings.py` if its paths need refreshing;
do not sed it.
