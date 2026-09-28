# TASK-010: `Testing` section missing from most common and math module pages

> Migrated 2026-09-27 from `vault/Tasks/docs-review/open.md` as **DOCREV-016** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** CLOSED 2026-09-27 -- the owner confirmed the docs-review work is done. No measurement was taken in this session to support that; the basis is Sean's statement, recorded as such rather than presented as verification.
**Status (as filed):** open 2026-08-11
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
