<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# vault/tracking/projects/components/cache-ip/onyx-ace-ccu — issues

**Next ID: ISSUE-003** — never recycle a number, even when its item closed.

An anomaly, risk, or open question not yet diagnosed: it resolves INTO a bug, a task, or a recorded no-action.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 1 | in progress right now |
| [closed/](closed/) | 1 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

(none)

## Active

- **ISSUE-002** ([page](active/ISSUE-002.md)) — a snarfed write-back victim still drains after passing the line dirty; wider than filed: a coherence bug between any two writers, reproduced with two caches as jet-prime BUG-002. Resolved 2026-11-24 on both sides (the cache ends a passed-on entry; onyx and the pair fabric order same-line write-backs by presentation); closes on the proofs (filed 2026-11-23)

## Closed

- **ISSUE-001** ([page](closed/ISSUE-001.md)) — onyx's observer put per-transaction classes on the low-bandwidth MonBus with no class knob; closed 2026-11-22 into TASK-001 step 6c: the ocelus mask layers on `onyx_monlite`, reset to the rare class (filed 2026-11-22)
