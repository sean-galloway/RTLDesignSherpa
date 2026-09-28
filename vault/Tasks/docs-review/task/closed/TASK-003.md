# TASK-003: every docs/markdown book needs index.md + overview.md

> Migrated 2026-09-27 from `vault/Tasks/docs-review/open.md` as **DOCREV-010** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** CLOSED 2026-09-27 -- the owner confirmed the docs-review work is done. No measurement was taken in this session to support that; the basis is Sean's statement, recorded as such rather than presented as verification.
**Status (as filed):** open 2026-07-25 (Sean)
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
