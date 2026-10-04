<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# projects/components/dma-ip/rapids — tasks

**Next ID: TASK-024** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 23 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

## Active

## Closed

- **TASK-022** — CLOSED 2026-10-04: both byte macro port-level proofs done
  (snk depth 15, src depth 16), mutation batteries all-caught in-budget;
  suite-wide prove/cover re-run green, 13/13 flats CURRENT; the 64
  never-compiled in-RTL SVA blocks deleted (bf5db01b7)
- **TASK-023** — CLOSED 2026-10-03: both Genesys2 rapids harnesses rebuilt on
  the fixed sdpram (71d48b6f7), timing-closed, board-verified; byte std 117/117
  + aligned 28/28, beats suite 48/48 + 7 observer campaigns (139 configs) all
  pass; small-transfer bandwidth up to +400% (1-beat sink) with zero
  regressions, saturated headline points unchanged; docs repinned
- **TASK-020** — AXI response-error injection: harness CSR + injector on both shared slaves, proven on silicon 36/36 at full; the monbus half built a capture buffer that works and showed there is no error packet to check (rapids BUG-013) (closed 2026-10-01)

- **TASK-019** — the byte-granular RAPIDS: bytes, WSTRB/TSTRB partial beats, its own Genesys 2 harness and books, board-characterized (closed 2026-09-30; sign-off fub 1521/0, fub_beats 1281/0, macro 822/0, macro_beats 771/0, top 42/0, top_beats 36/0)
- **TASK-021** — beat-aligned utilization delta versus RAPIDS Beats: start-up terms isolated in sim and accepted as by design (closed 2026-09-30)
- **TASK-001** — adopt the shared instrumentation pair (axi4_intf_master_observer + axis4_intf_observer); measured through them 2026-09-27
- **TASK-002** — RAPIDS-beats has NO contracts workbook at all
- **TASK-004** — Register-map hygiene enforced in RAPIDS DV
- **TASK-005** — one RTL harness -- move the host path down so verify-sim can reach it
- **TASK-006** — re-measure the beat-count knee on rapids (July data is stale)
- **TASK-007** — MAS/HAS trees and index table redrawn to the STREAM-wrapper hierarchy (closed 2026-09-27)
- **TASK-008** — ch01_overview/02_port_list.md regenerated from the RTL: 300/300 ports, per half (closed 2026-09-27)
- **TASK-009** — 07_beats_latency_bridge.md re-authored against latency_bridge_beats.sv (closed 2026-09-27)
- **TASK-011** — 15 `// Module:` headers now match their filenames (closed 2026-09-27)
- **TASK-012** — harness AXI observer timestamp FIFO 8 -> 32; latency sweep re-measured with no sample loss (closed 2026-09-27)
- **TASK-003** — scrub the tests for completeness (rapids) (closed 2026-09-27; residue is TASK-013)
- **TASK-013** — replace the hand-rolled protocol responders in the rapids TBs with framework BFMs (closed 2026-09-27)
- **TASK-010** — 26 ASCII placeholder figures name dead signals; 2 figures have no test to capture from (closed 2026-09-27)
- **TASK-014** — control engines drain on channel reset instead of abandoning the AXI transaction (closed 2026-09-27)
- **TASK-015** — AXIS monitor-lite in each half (Option B), one arbiter entry per half (closed 2026-09-27)
- **TASK-016** — re-prove the rapids and stream formal suites after the engine fixes; prove the control engines (closed 2026-09-28)
- **TASK-017** — placement pass: 6 filelists into filelists/ dirs, 3 trackers into this lane, 10 stale pages deleted (closed 2026-09-28)
- **TASK-018** — interleaved-channel schedule for the harness AXIS generator; sink aggregate window measured, no knee to 512 cycles (closed 2026-09-28)
