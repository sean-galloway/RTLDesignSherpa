# TASK-028: the testplan gate only sees singular `rtl_file:`/`test_file:` keys — plural-list plans are unchecked, and duplicate scalar keys are lossy in the coverage runner

**Status:** CLOSED 2026-10-04 (commit a5424e05a). Gate parses plural
`rtl_files:`/`test_files:` lists under the same resolve-or-fail rule;
ref-or-annotation convention documented in the parser (single token =
checked ref, prose = intentional gap, mid-list prose skips without
truncating). Bridge 1x2-1x5 on plural lists; uart_axil_bridge's 3 refs
fixed for the uart_to_axil4/ move; fub_legacy_gaps' 4 legacy names
annotated as gaps. Runner joins plural test_files and guards string-
valued plural keys. Gate: 0 broken, baseline empty.
**Priority:** P3
**Filed from:** closing tooling TASK-027 (broken testplan refs).

TASK-027 fixed the 42 ratcheted broken refs and emptied
`bin/testplan_refs_baseline.json`. While fixing the four bridge smoke plans
it measured two adjacent tooling gaps that TASK-027 deliberately did NOT
take on:

## Gap 1 — the gate is blind to the plural-list convention

`bin/filelist_registry.py` extracts refs with
`TESTPLAN_REF_RE = re.compile(r"^(rtl_file|test_file):\s*(\S*)\s*$")`
(singular scalar keys only). But at least 8 committed testplans use the
plural list form instead (`rtl_files:` / `test_files:` with `- item`
entries) — e.g. utility-ip/converters (4 plans), dma-ip/stream
`axi_engines_testplan.yaml`, rapids `data_path_beats_testplan.yaml` and
`fub_legacy_gaps_testplan.yaml`, val/common `clock_utilities_testplan.yaml`.
Every one of those refs is INVISIBLE to `--testplans`: nothing checks them,
so a future broken ref in a plural plan would sail through pre-commit/CI.

Measured 2026-10-04 by parsing every `*_testplan.yaml` for both key forms:
258 refs total, 13 not resolving — but almost all of those are intentional
GAP annotations, not drift:

- `bridge_cam_testplan.yaml`: `test_file: Tested via bridge integration
  tests (no standalone test)`
- `bridge_4x4_rw_testplan.yaml` / `bridge_5x3_channels_testplan.yaml`:
  `test_file: ... (DOES NOT EXIST - GAP)`
- `scheduler_group_testplan.yaml`: `test_file: "GAP - Integration tested
  only"`
- `axi_engines_testplan.yaml`: `test_files: "INTEGRATION ..."`
- `fub_legacy_gaps_testplan.yaml`: 4 dissolved legacy rtl names
  (`sink_axi_write_engine.sv` etc., the plan documents exactly those gaps)
  and `test_files: none (TESTING GAP)`
- `uart_axil_bridge_testplan.yaml`: 3 rtl_files that genuinely do not
  resolve (`uart_axil_bridge.sv`, `uart_rx.sv`, `uart_tx.sv` under
  converters/rtl) — the one true-drift case, filed here rather than fixed
  under TASK-027's rule because the plan also mixes scalar and plural forms
  and deserves its own pass.

So a plural-aware gate cannot just start failing on unresolved refs: it
needs to honor the GAP-annotation convention (quoted free text / explicit
GAP markers), or those plans get a sanctioned way to opt out.

## Gap 2 — duplicate scalar keys collapse in the coverage runner

TASK-027's bridge fix made each of the four `bridge_<N>_testplan.yaml`
plans carry two `rtl_file:` lines and two `test_file:` lines (repeated
scalar keys — the only list form the gate regex accepts).
`bin/cov_utils/verify_testplan_coverage.py` loads plans with
`yaml.safe_load`, which keeps only the LAST duplicate key, so the runner
sees the wr variant only (rd is invisible). `parse_testplan` already
natively supports the plural form (`rtl_files:` list, see
verify_testplan_coverage.py:28-33), so the two tools disagree on what a
multi-file plan looks like.

## Done when

- `--testplans` checks plural `rtl_files:`/`test_files:` list entries with
  the same resolve-or-fail rule as scalar refs, with an explicit,
  documented convention for GAP annotations (so the 5 intentional-gap plans
  above keep passing).
- The uart_axil_bridge plan's 3 missing rtl refs are fixed or re-annotated
  under that convention.
- The bridge plans and `verify_testplan_coverage.py` agree on a single
  multi-file schema (preferably plural lists everywhere, once the gate
  understands them); no duplicate scalar keys remain.
- Baseline stays empty; `bin/check_task_ids.py` passes.
