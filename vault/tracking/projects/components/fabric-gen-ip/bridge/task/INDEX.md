<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# bridge — tasks

**Next ID: TASK-022** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 2 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 15 | done (kept for history) |
| [dropped/](dropped/) | 4 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-020** — make the read-return-atomic tracker depth (8, fixed today) a per-slave TOML key, and report it
- **TASK-021** — head-of-line blocking under uniform traffic past saturation: 2-deep request slots, a master's one in-order request stream (found by TASK-014's patterns, 2026-10-24)

## Dropped

- **TASK-009** — WB4 in the bridge is best effort -- the two known gaps stay open by decision
- **TASK-010** — Legacy TASK-012 — AXI burst optimization
- **TASK-011** — Legacy TASK-014 — APB3 to APB4 bridge
- **TASK-001** — trim method from `bridge/CLAUDE.md`; dropped, the file was already compliant and every row of its removal table was falsified by reading the text.

## Closed
- **TASK-016** — buffer sizing rule: every unset max_outstanding / rate_buffer derived from 1 + latency_cycles + modelled round trip (bridge_pkg/sizing.py), skid stages 2, `<bridge>_sizing.json`; the step measured at the boundary (2026-10-24, grouped with TASK-014)
- **TASK-014** — perf methodology: uniform / permutation / hot-spot open-loop sweeps vs offered load on 2x2, 2x2 pipe and 4x4 (test_bridge_perf_patterns.py, HAS 5.1); found the uniform-overload head-of-line case, filed as TASK-021 (2026-10-24)
- **TASK-015** — matrix arbiter vs round-robin: `arbitration = "matrix"` shipped, measured on ASAP7 (4x4 worst path -11 percent, +2 percent cells; 2x2 a wash), fairness bound equal; `rr` stays default (2026-10-24)
- **TASK-019** — Genesys 2 bridge stress model on every protocol the bridge builds: AXI4 / AXI3 / AXI5 (sideband, poison, IDUNQ, atomics, MTE), third-party IP on LiteDRAM, and the single-beat AXI-Lite / APB / WB4 shells in `build-mixb` (2026-10-24; 30/30 and a soak on every build; found and fixed bridge BUG-018..024, converters BUG-010..015)
- **TASK-018** — Transaction-ID remap: fabric ID = {master index, slot} (2026-10-19)
- **TASK-017** — bridge HAS/MAS v2.0: full 8-protocol summaries + explicit ACE-out-of-scope + version alignment (2026-10-12)

- **TASK-013** — bin/GENERATOR_ARCHITECTURE.md: reconcile the 2025-11 walkthroughs against the generator -- CLOSED 2026-09-29: GENERATOR_ARCHITECTURE.md rewritten from the code, 434 lines, every path/symbol checked; no 64-bit-internal or YAML claims, no line numbers
- **TASK-012** — bridge placement pass: 9 loose markdown files (generator design notes beside bin/, a bug write-up at the root) -- CLOSED 2026-09-29: 9 loose files placed: BUG-015 filed, GENERATOR_ARCHITECTURE to bin/ (rewritten where wrong), SIGNAL_NAMING collapsed, 5 stale pages deleted; TASK-013 filed for the rest
- **TASK-002** — AMBA5 bridge support (AXI5 ports alongside AXI4)
- **TASK-003** — scrub the tests for completeness (bridge)
- **TASK-004** — AXI5-Lite and APB5 as MASTER protocols
- **TASK-005** — Master-unique transaction IDs: prepend the master index
- **TASK-006** — Legacy backlog carried over from projects/components/fabric-gen-ip/bridge/TASKS.md
- **TASK-007** — A native-AXI5 fabric
- **TASK-008** — Wishbone B4 as a bridge protocol, both sides
