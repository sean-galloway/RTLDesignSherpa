<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# projects/components/cache-ip/jet-mesi-l1 — issues

**Next ID: ISSUE-004** — never recycle a number, even when its item closed.

An observed problem that is not yet a diagnosed defect or a decided piece of
work: an anomaly, a risk, an open question. It RESOLVES INTO a bug, a task,
or a recorded no-action.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 2 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **ISSUE-003** ([page](open/ISSUE-003.md)) — two jet cores sharing nothing lose every pipelining gain: board `disjoint64k_we64` dual is flat at ~480,000 cycles from depth 1 to 16 (single 349k -> 215k); 2.1-2.3x single-core where jet-prime / onyx are 1.4-1.7x. Suspected: the serial pair fabric. Filed 2026-11-27.

## Active

(none)

## Closed

- **ISSUE-002** ([page](closed/ISSUE-002.md)) — jet_monlite commits only 2
  events/cycle and drops the rest under thrash (up to ~1.5% of J7 events on
  64 KB configs); drops are counted (profile bin 17) but MSHR bins undercount.
  **Closed 2026-11-10:** owner decision, leave it; bin 17 is the error bar. Monitor-family FPGA cost question -> rtl/amba/monitors TASK-007.
- **ISSUE-001** ([page](closed/ISSUE-001.md)) — cpu_req→snoop-accept
  combinational chain (31 levels) fails 90 MHz timing on Kintex-7; jet rig
  reclocks to 60 MHz; pipelining the snoop-accept path is jet v2 work.
  Active 2026-11-03: cone mapped on the routed checkpoint (35 levels, the
  entire top-20 critical list), `coh_req` sideband registered at the
  jet_coh_core boundary.
  **Closed 2026-11-08:** superseded by jet v3 + the FPGA review; bin 10 closes 100 MHz at WNS +0.517, 21.7k LUT. Residual latency cost is TASK-003.
