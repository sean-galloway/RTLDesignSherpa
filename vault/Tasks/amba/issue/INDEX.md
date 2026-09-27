<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# amba — issues

**Next ID: ISSUE-003** — never recycle a number, even when its item closed.

An observed problem that is not yet a diagnosed defect or a decided piece of work: an anomaly, a risk, an open question. It RESOLVES INTO a bug, a task, or a recorded no-action.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 3 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 0 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |

## Open

- **ISSUE-000** — reserved template; copy the file, do not file against it.
- **ISSUE-001** — monbus_axil4_axil4_group misses 10 ns on Artix-7 through the s1_beats_to_limit CARRY4 chain (found synthesizing the amba/monitor-lite TASK-001 lite fixture)
- **ISSUE-002** — cam_clear inside the reporter's emission window strands the completion packet under aggressive clock gating (`_mon_cg` slave wrappers, idle-count 0; the `_monlite_cg` wrappers are unaffected)
