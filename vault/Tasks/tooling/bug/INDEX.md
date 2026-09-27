<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# tooling — bugs

**Next ID: BUG-003** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what correct looks like. If you cannot state the expected behaviour, it is an ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 2 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 1 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |

## Open

- **BUG-000** — reserved template; copy the file, do not file against it.
- **BUG-002** — `--blindspots` enumerates filelists from the index but resolves them from disk; a partial-pathspec rename commit reports phantom unregistered filelists

## Closed

- **BUG-001** — checker attribution: multi-module declarations + 46 pages silently unchecked (fixed; threshold was NOT the defect)
