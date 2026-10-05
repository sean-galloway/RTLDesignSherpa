<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# tooling — issues

**Next ID: ISSUE-004** — never recycle a number, even when its item closed.

An observed problem that is not yet a diagnosed defect or a decided piece of work: an anomaly, a risk, an open question. It RESOLVES INTO a bug, a task, or a recorded no-action.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 2 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **ISSUE-003** — cocotb-framework 1.0.0: external dependency major rev; IRQ BFM promoted into
  the package, breaking `TBClasses.irq` imports outside this repo. Advisory/tracking; closes as a
  recorded no-action once local venvs sync past 1.0.0.

- **ISSUE-002** — task areas are named two ways for sibling IPs: `vault/Tasks/pumice-ddr2-lpddr2/`
  (top level, codename) vs `vault/Tasks/scoria-ddr3-lpddr3/` (nested,
  protocol name), so a new component area has no way to tell which is intended.
  Cheapest to settle now, while scoria and andesite hold two items between them.

## Closed

- **ISSUE-002** — CLOSED: the compound `<codename>-<protocols>` form is the
  directory name at every level (component dir, task area, knowledge mirror). All
  three memory-controller areas renamed and promoted to top level; the rule is
  stated in the memory-controllers README. Prose citations keep the bare codename,
  on purpose.

- **ISSUE-001** — Triage the 18 Dependabot vulnerabilities on the default branch
