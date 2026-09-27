<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# tooling — bugs

**Next ID: BUG-004** — never recycle a number, even when its item closed.

A DEFECT with a reproduction: something behaves wrongly and we can say what correct looks like. If you cannot state the expected behaviour, it is an ISSUE, not a bug.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 3 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |

## Open

- **BUG-000** — reserved template; copy the file, do not file against it.

## Closed

- **BUG-003** — `RegisterMap.walk()` crashes on an ERROR response, so the MON-window guard silently disabled the board register walk on every `USE_AXI_MONITORS=0` build since 2026-09-24 (walker fixed; host-side skip still open)
- **BUG-001** — checker attribution: multi-module declarations + 46 pages silently unchecked (fixed; threshold was NOT the defect)
- **BUG-002** — `--blindspots` read the index and disk in one subtraction, so a tracked+registered filelist absent from the worktree was reported unregistered (fixed; the rename-commit block it was filed for was CORRECT)
