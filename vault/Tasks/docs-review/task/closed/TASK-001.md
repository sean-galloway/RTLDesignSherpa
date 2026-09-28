# TASK-001: fix ALL broken links, whenever they were introduced

> Migrated 2026-09-27 from `vault/Tasks/docs-review/open.md` as **DOCREV-011** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** CLOSED 2026-09-27 -- the owner confirmed the docs-review work is done. No measurement was taken in this session to support that; the basis is Sean's statement, recorded as such rather than presented as verification.
**Status (as filed):** open 2026-07-26 (Sean); mechanical classes swept 2026-07-27;
gate landed 2026-09-21 (ec5bd1602) -- the backlog is now ratcheted, so it
can shrink but cannot regrow
**Priority:** P2

Not a rename cleanup. **Every** broken link in the repo, no matter which move,
split or deletion caused it. First measured 2026-07-26 at `d65be489`: **495
broken links across 160 files.**

### Where it stands

**RE-MEASURED 2026-09-21 with the checker: 117 broken in 56 files** (was 374
in 146). 114 of the 117 are under `projects/`, still deferred; only 3 are
outside it. Two caveats on comparing the figures: the old counts came from
the snippet below, which counts links inside ``` fences and inline `code`
examples, and the checker excludes both -- 68 fenced and 8 inline-code today.
So part of the drop is a truer measurement, not repair.

The 2026-07-27 figures, for history: **374 remain, across 146 files** (at
`057f75df`+). The
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
| 24 | `bin/markdown_to_word_instructions.md` -- RETIRED 2026-09-23, see below |
| 10 | `bin/TBClasses/wavedrom_user/GAXI_WAVEDROM_GUIDE.md` |
| 10 | `docs/markdown/TestTutorial/wavedrom_gaxi_example.md` |
| 7 | `bin/DOC_GENERATION.md` |
| 6 | `docs/markdown/overview.md` (was 76) |
| 5 | `docs/DOCUMENTATION_STANDARDS.md` |

`README.md` and `docs/markdown/rtl-cdc/cdc.md` are now at zero.

**The top row is gone as of 2026-09-23 (TOOL-002).**
`bin/markdown_to_word_instructions.md` documented `markdown_to_word.py`, a
tool that has never existed in this repo -- not on disk, not tracked, not in
history, and referenced by no code. Its 24 broken links were links into a
toolchain that was never here, which is why they were never fixable by
repointing. The file is retired; the checker went 1399 -> 1398 tracked .md
with the broken count unchanged at 3, and 22 fenced + 1 inline-code example
left the denominator with it.

The figures ABOVE are deliberately left as measured. They are the 2026-07-27
snapshot at `057f75df` and are superseded by the 2026-09-21 re-measurement at
the top of this entry; editing a historical count to match today would
falsify the record, for the same reason `docs/review/` is excluded from the
sweep.

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
- **DONE 2026-09-21 -- the checker is a gate.** `bin/check_broken_links.py`,
  ratcheted against `bin/broken_links_baseline.json`, wired into BOTH
  `bin/hooks/pre-commit` and `.github/workflows/filelist-checks.yml` (one
  without the other is how the filelist checks silently stopped running for
  five days). It reports coverage beside the count and fails if it matches no
  links at all, because two checkers here have reported success off an empty
  set. It excludes fenced blocks, inline `code` examples, `docs/review/` and
  wikilinks -- "fixing" any of those corrupts the page.

---
