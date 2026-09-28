# apbx-xbar — task rollup

**Next ID: APBX-008** — never recycle a number, even when its task closed.

## Lanes

This area tracks three kinds of work, each a directory with its own INDEX and
its own ID sequence. **Every item is its own file**, `<ID>.md`, filed under
the directory for its state (`open/`, `active/`, `closed/`, `dropped/`).
Pick the lane before filing:

| Lane | open | active | closed | dropped | deferred |
|---|---|---|---|---|---|
| [task/](task/INDEX.md) | 1 | 0 | 4 | 0 | 0 |
| [bug/](bug/INDEX.md) | 1 | 0 | 2 | 1 | 0 |
| [issue/](issue/INDEX.md) | 1 | 0 | 0 | 0 | 0 |

**The pages at this level are the LEGACY task lane.** They are frozen: close
them out where they stand, and do not add to them. New work of any kind goes in
a lane above. See [the convention](../../../INDEX.md) for the full definitions.


APB crossbar family (`projects/components/apbx-xbar/`): the generated
fixed-configuration variants `1to1`, `2to1`, `1to4`, `2to4` and
`2to2_mixed`. Every port independently speaks APB4 or APB5.

| Lane | open | active | closed | dropped | deferred |
|---|---|---|---|---|---|
| [task/](task/INDEX.md) | 1 | 0 | 3 | 0 | 0 |
| [bug/](bug/INDEX.md) | 0 | 0 | 2 | 1 | 0 |
| [issue/](issue/INDEX.md) | 0 | 0 | 0 | 0 | 0 |

## Open shortlist

*(`apbx_xbar_thin` RETIRED and DELETED 2026-08-27, along with its test,
its two formal harnesses, its testplan and its doc page. APBX-006 — its
zero-cycle downstream setup phase — dropped as moot. The generated
variants are unaffected. The one real cost — the thin harnesses carried
the ONLY formal proof of APB4/APB5 version gating — was repaid on
2026-08-29 by `formal/apbx_xbar/apbx_xbar_2to2_mixed/`, which proves the
mixed configuration directly.)*

*(APBX-004/005 closed 2026-08-27: raw-address decode rotated the slave map
for non-span-aligned BASE_ADDR; out-of-range accesses wedged the master
instead of returning PSLVERR. Both found by qc round_7 — the first
correctness round on the APB crossbar books — RED-tested and fixed.)*

Nothing open. APBX-001 (generalize to APB4/APB5/mixed), APBX-002 (formal
proof of the version gating) and APBX-003 (parity) are all closed.

## Reading order

closed.md APBX-001 is the whole story of the APB4→APBX
generalization and records why mixing needs no converters; APBX-002 proved
the version gating formally (on the thin core, since deleted); APBX-003
added parity and records why a check-and-regenerate fabric protects a
narrower span than end-to-end pass-through did.

Docs: [docs/markdown/rtl-amba/apbx/](../../../../../docs/markdown/rtl-amba/apbx/README.md)
