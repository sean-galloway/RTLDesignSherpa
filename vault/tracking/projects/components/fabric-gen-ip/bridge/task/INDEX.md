<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# bridge — tasks

**Next ID: TASK-024** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 19 | done (kept for history) |
| [dropped/](dropped/) | 4 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

Nothing open.

## Dropped

- **TASK-009** — WB4 in the bridge is best effort -- the two known gaps stay open by decision
- **TASK-010** — Legacy TASK-012 — AXI burst optimization
- **TASK-011** — Legacy TASK-014 — APB3 to APB4 bridge
- **TASK-001** — trim method from `bridge/CLAUDE.md`; dropped, the file was already compliant and every row of its removal table was falsified by reading the text.

## Closed
- **TASK-023** — the generator emits the write-only monbus group and it is the DEFAULT: `[bridge.mon_group] write_only` defaults true (monbus_<p>_group_1wr; the Genesys 2 _mon bridges' egress); `write_only = false` keeps the two-port group, pinned in the 20 legacy mon configs whose DV drains s_mon_axil_*; err-window RDL/DV plumbing landed; regen clean over 55 fixtures, generator tests 257/257 (2026-10-25)
- **TASK-022** — the 4x4's uniform-traffic loss past saturation, measured per cycle: the return path clean (0 percent stalled), the loss was request supply -- the driver's `k % 16` ID rotation on a 3-target cycle sprang the per-ID same-target gate (31-58 percent of AR cycles; the 2x2 immune, 16 mod 2 = 0); IDs partitioned per target took the 4x4 to 0.98 of capacity at 1.4x offered; the flat ceiling past 2x is the traffic itself (half the beats at the 7x-oversubscribed 32-bit periph port; Little's law on the shared outstanding table) -- documented, stays (2026-10-25)
- **TASK-021** — head-of-line blocking under uniform traffic past saturation: a shared slave's in-order R output stalls on a busy master while the next master idles (measured per cycle; not the request slots, not the adapter mux); fixed by `[bridge] r_queue_depth`, default 0 -- `bridge_2x2_rw_rq8` 0.67 to 1.00 of capacity at 2x offered, cost measured on ASAP7 and Kintex-7 (2026-10-25)
- **TASK-020** — `atomic_rr_depth`: the read-return atomic tracker depth as a per-slave key (default 8), in the package and the sizing report; stall measured at 2 and at 8 (2026-10-24)
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
