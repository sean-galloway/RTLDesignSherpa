<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# projects/components/cache-ip/jet-mesi-l1 — issues

**Next ID: ISSUE-003** — never recycle a number, even when its item closed.

An observed problem that is not yet a diagnosed defect or a decided piece of
work: an anomaly, a risk, an open question. It RESOLVES INTO a bug, a task,
or a recorded no-action.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.

| State | Count | What |
|---|---|---|
| [open/](open/) | 2 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 0 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **ISSUE-001** ([page](open/ISSUE-001.md)) — cpu_req→snoop-accept
  combinational chain (31 levels) fails 90 MHz timing on Kintex-7; jet rig
  reclocks to 60 MHz; pipelining the snoop-accept path is jet v2 work.
- **ISSUE-002** ([page](open/ISSUE-002.md)) — jet_monlite commits only 2
  events/cycle and drops the rest under thrash (up to ~1.5% of J7 events on
  64 KB configs); drops are counted (profile bin 17) but MSHR bins undercount.

## Active

(none)

## Closed

(none)
