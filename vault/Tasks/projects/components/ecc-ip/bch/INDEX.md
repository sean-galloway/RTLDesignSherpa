# bch — task rollup

**Next ID: TASK-004** — never recycle a number, even when its task closed.

## Lanes

This area tracks three kinds of work, each a directory with its own INDEX and
its own ID sequence. **Every item is its own file**, `<ID>.md`, filed under
the directory for its state (`open/`, `active/`, `closed/`, `dropped/`).
Pick the lane before filing:

| Lane | open | active | closed | dropped | deferred |
|---|---|---|---|---|---|
| [task/](task/INDEX.md) | 3 | 0 | 0 | 0 | 0 |
| [bug/](bug/INDEX.md) | 0 | 0 | 0 | 0 | 0 |
| [issue/](issue/INDEX.md) | 0 | 0 | 0 | 0 | 0 |

See [the convention](../../../../INDEX.md) for the full definitions.

## Open shortlist

- **TASK-001** (open) — the stand-up umbrella, run the way reed-solomon
  TASK-001 ran: references and draft PRD landed 2026-10-03; HAS, RTL + DV
  and (eventually) a board harness follow; it closes when the component
  exists and passes end to end.
- **TASK-002** (open) — author the BCH HAS v0.1; closes when the `docs/bch_has/`
  PDF builds and every open item is tied to a PRD decision ID.
- **TASK-003** (open) — author the BCH MAS v0.1 and signal-contract kmaps;
  closes when the `docs/bch_mas/` tree, generator, and workbook are landed
  and every block page carries signal-level intent with FSM policy.
