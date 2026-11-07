# TASK-044: pre-beats RAPIDS work list, superseded by the beats rearchitecture

> Migrated 2026-11-07 from `projects/components/dma-ip/rapids/TASKS.md`, which held seven items (its TASK-002, -004, -005, -006, -007, -008, -009) written against the pre-beats RTL and test tree. Each is disposed below; none survives as planned work. The file's own 2026-07-22 banner already called them "superseded - pre-beats work history".

**Priority:** --
**Status:** DROPPED 2026-11-07 -- every item is moot, done another way, or decided against. One file records the seven decisions together because they share one cause.
**Owner:** sean galloway

## Dispositions

| Old ID | Title | Disposition | Where the need went |
|---|---|---|---|
| TASK-002 | AXI timeout detection in the sink data path | **By design, no action.** Timeouts are the monitor's job, not the datapath's (owner, 2026-09-25); the real half, a discarded write-error flag, was fixed | `known_issues/resolved/sink_data_path.md`; rapids TASK-002 item 1; `cfg_axi_timeout_mask` on `rapids_beats_top_base.sv` |
| TASK-004 | expand integration test coverage | Superseded: `dv/tests/integration_tests/` and its five named files were retired | `dv/tests/macro/`, `dv/tests/macro_beats/`; sign-off counts in rapids TASK-019; error injection rapids TASK-020 |
| TASK-005 | system-level tests | Superseded: `dv/tests/system_tests/` never existed in that form | `dv/tests/top/`, `top_beats/`, `top_g/`; board runs rapids TASK-020, TASK-023 |
| TASK-006 | README.md for RAPIDS | Decided against: a beside-code README is a link, never a guide (`vault/handbook/authoring/doc-placement.md`); CLAUDE.md and PRD.md serve the role | -- |
| TASK-007 | update the validation status report | Moot: `RAPIDS_Validation_Status_Report.md` is itself stamped a superseded pre-beats snapshot | sign-off counts in rapids TASK-019 and TASK-034 |
| TASK-008 | SRAM control for concurrent reads | Moot: the module was retired (`known_issues/resolved/sink_sram_control.md`); RAPIDS now wraps STREAM's `sram_controller` (bdf4e0dff), single drain port by design, sink egress at line rate | -- |
| TASK-009 | performance monitoring infrastructure (`rapids_perf_monitor.sv`) | Superseded: never built | `axi_bus_meter` instances (`scheduler_group_array_beats.sv`), the shared observers (rapids TASK-001), AXIS monitor-lite (rapids TASK-015) |

The other four items in that file landed: TASK-001 -> [BUG-018](../../bug/closed/BUG-018.md),
TASK-003 -> [TASK-042](../closed/TASK-042.md), TASK-011 -> [TASK-040](../closed/TASK-040.md),
TASK-012 -> [TASK-041](../closed/TASK-041.md). There was no TASK-010.

## Pre-beats -> beats path map

Kept here because parts of it (tests, TB classes, docs) are recorded nowhere
else. Old paths appear in commit messages and the pre-beats books.

- `rtl/rapids_fub/scheduler.sv` -> `rtl/fub_beats/scheduler_beats.sv` (no credit management)
- `rtl/rapids_fub/descriptor_engine.sv` -> `rtl/fub_beats/descriptor_engine_beats.sv`
- `rtl/rapids_fub/program_engine.sv`, `sink_axi_write_engine.sv`, `sink_sram_control.sv`, `rapids_perf_monitor.sv` -> retired (nearest beats equivalents: `axi_write_engine_beats.sv`, `snk_sram_controller_beats.sv`; no beats program engine or perf monitor)
- `rtl/rapids_macro/scheduler_group.sv` -> `rtl/macro_beats/scheduler_group_beats.sv`
- `rtl/rapids_macro/sink_data_path.sv` -> `rtl/macro_beats/snk_data_path_beats.sv`
- `rtl/rapids_macro/rapids_top.sv` -> `rtl/top_beats/rapids_beats_top.sv`
- `dv/tests/fub_tests/` -> `dv/tests/fub_beats/` (e.g. `test_scheduler.py` -> `test_scheduler_beats.py`)
- `dv/tests/integration_tests/`, `system_tests/`, `performance_tests/` -> `dv/tests/macro_beats/` and `dv/tests/top_beats/` (retired, not ported 1:1)
- `bin/TBClasses/rapids/` -> `projects/components/dma-ip/rapids/dv/tbclasses/`
- `docs/rapids_spec/` -> `docs/rapids_beats_has/` + `docs/rapids_beats_mas/`
- `known_issues/scheduler.md`, `known_issues/sink_*.md` -> `known_issues/README.md` + `known_issues/active/`
