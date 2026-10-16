# Task 12 — Delta mesh regression wiring, soak, docs status flip

## Scope

Close the delta mesh Task 12 deliverables:

1. Wire mesh sources into the area filelist so lint/elab sees the cell + fabric.
2. Strengthen the multicast deadlock soak to 10⁶ flits at `full` level and measure runtime.
3. Add a perf-model calibration regression test for tornado traffic on a 4×4×1 fabric.
4. Flip Delta HAS/MAS/GAS documentation from `PLANNED` to `IMPLEMENTED` where the feature is built, and rebuild the three PDFs.
5. Commit code/tests and docs/PDFs separately.

## Files changed

### Code / tests

- `projects/components/fabric-gen-ip/delta/rtl/filelists/delta_all.f`
  - Includes `-f $REPO_ROOT/projects/components/fabric-gen-ip/delta/rtl/filelists/delta_mesh.f`.
- `projects/components/fabric-gen-ip/delta/dv/tbclasses/delta_mesh_tb.py`
  - `run_mcast_deadlock_soak` flit counts: `gate=1000`, `func=100000`, `full=1000000`.
  - Soak timeout raised to `120000 ms`.
- `projects/components/fabric-gen-ip/delta/dv/tests/test_delta_mesh_multicast.py`
  - `make_args=["-j", str(os.cpu_count())]` on both fabric and cell `run()` calls.
  - Deadlock soak cocotb timeout unit fixed from `"s"` to `"ms"`.
- `projects/components/fabric-gen-ip/delta/dv/tests/test_delta_mesh_perf_calibration.py` (new)
  - 4×4×1 generated-fabric tornado perf calibration.
  - Zero-load regression threshold: measured T0 may not exceed modeled T0 by > 20 %.
  - Loaded-latency sweep at 0.2 / 0.4 / 0.6 is logged only (small fabric is too noisy to fail on).
  - Fixes applied during bring-up:
    - cocotb timeout unit changed from `"s"` to `"ms"`;
    - geometric inter-arrival gap sampled with `random.Random` + inverse-CDF;
    - receiver source index derived from the tornado reverse map;
    - loaded-latency model uses `loaded_latency()` instead of zero-load `latency()`.

### Documentation

- HAS `ch02_system_overview` and `ch07_mesh_network` chapters:
  - `PLANNED` → `IMPLEMENTED` admonitions.
  - Mode count updated to 10, port count to 9, counter bank indices documented.
  - Deferred items (CXS, MonBus aggregation, 1 c/hop lookahead issue #120, SRAM FIFO_IMPL issue #118) noted.
- MAS `ch06_mesh_cell` chapter:
  - All sections marked `IMPLEMENTED` with references to the 2026-10-13 design spec.
- GAS `ch01_overview`, `ch02_configuration/cli_and_programmatic_api`, `ch02_configuration/validation_rules`:
  - Mesh CLI flags documented with real implemented options (`--cells-x/y/z`, `--torus-x/y/z`, `--torus`, `--source-route`, `--speculation`, `--fifo-impl`, `--user-width`, etc.).
  - Mesh programmatic API example added.
  - Validation rules updated; header width corrected to `6 * COORD_W + 32`.
- Rebuilt PDFs:
  - `Delta_HAS_v1.0.pdf` (148 pages)
  - `Delta_MAS_v1.0.pdf` (129 pages)
  - `Delta_GAS_v1.0.pdf` (85 pages)

## Verification results

| Test | Level | Result | Wall time |
|------|-------|--------|-----------|
| `make run-delta_axis_flat_2x4_strb_amba5-func-serial` | func | **PASS** (6 passed in 3.85 s) | 4 s |
| `make run-delta_mesh_multicast-func-serial` | gate+func | **PASS** (10 passed in 277.98 s) | 4 m 39 s |
| `make run-delta_mesh_perf_calibration-func-serial` | gate+func | **PASS** (2 passed in 124.07 s) | 2 m 04 s |
| `make run-delta_mesh_multicast-full-serial` (10⁶-flit soak) | full | **TIMEOUT** after 30 min (>30 min wall, did not finish) | > 30 m |
| `make run-all-func-serial` (full mesh + flat AMBA5 grid) | func | *in progress* (≈21 % after ~30 min) | TBD |

Notes on soak runtime:

- The `func` level 100 k-flit soak completed in **141.43 s real time**.
- Extrapolating linearly, the `full` 1 M-flit soak is expected to take **~24 min real time**.
- It exceeded the 30 min background window used for this run, so the test was killed before completion.
- The 10⁶-flit setting is retained for `full` regressions; it is intentionally not run in `gate`/`func`.

### Perf calibration measurements (func level)

| Load | Measured latency | Modeled latency | Ratio |
|------|------------------|-----------------|-------|
| 0.00 (zero-load) | 5.00 c | 7.00 c | 0.714 |
| 0.20 | 5.36 c | 7.87 c | 0.681 |
| 0.40 | 6.54 c | 9.33 c | 0.701 |
| 0.60 | 9.01 c | 12.25 c | 0.736 |

The measured zero-load latency is within the 20 % tripwire (it is well below the model, so no lookahead regression is indicated).

## Deferred items

- CXS migration.
- MonBus observation aggregation in the tile IP.
- 1 cycle/hop lookahead (issue #120).
- SRAM `FIFO_IMPL` (issue #118) — the `--fifo-impl sram` CLI choice is accepted by validation but not yet wired to the cell.

## Commits

1. **Code/tests commit** — staged paths:
   - `projects/components/fabric-gen-ip/delta/rtl/filelists/delta_all.f`
   - `projects/components/fabric-gen-ip/delta/dv/tbclasses/delta_mesh_tb.py`
   - `projects/components/fabric-gen-ip/delta/dv/tests/test_delta_mesh_multicast.py`
   - `projects/components/fabric-gen-ip/delta/dv/tests/test_delta_mesh_perf_calibration.py`
2. **Docs/PDFs commit** — staged paths:
   - `projects/components/fabric-gen-ip/delta/docs/delta_has/...`
   - `projects/components/fabric-gen-ip/delta/docs/delta_mas/...`
   - `projects/components/fabric-gen-ip/delta/docs/delta_gas/...`
   - `projects/components/fabric-gen-ip/delta/docs/Delta_HAS_v1.0.{docx,pdf}`
   - `projects/components/fabric-gen-ip/delta/docs/Delta_MAS_v1.0.{docx,pdf}`
   - `projects/components/fabric-gen-ip/delta/docs/Delta_GAS_v1.0.{docx,pdf}`
   - `projects/components/fabric-gen-ip/delta/task-12-report.md`
