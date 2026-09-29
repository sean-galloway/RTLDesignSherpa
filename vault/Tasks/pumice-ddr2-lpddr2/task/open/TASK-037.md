# TASK-037: reconcile the stale dv/testplans with the modules that exist

Reconcile the 16 stale testplans in `dv/testplans/` with the modules that
actually exist, or delete them.

## What is wrong

29 of the 50 `rtl_file:` / `test_file:` references across
`projects/components/mem-ctrl-ip/pumice-ddr2-lpddr2/dv/testplans/*.yaml`
point at files that do not exist. They name pre-rearchitecture modules that
the AXI4 front-end rework renamed or
dissolved:

| named in a testplan | what exists now |
|---|---|
| `rd_cmd_cam.sv` | `pumice_rd_cmd_cam.sv` |
| `scheduler.sv` | `pumice_mem_cmd_scheduler.sv` (macro) |
| `axi_intake.sv` | split into `pumice_rd_intake.sv` + `pumice_wr_intake.sv` |
| `wr_cmd_cam.sv`, `xbank_timers.sv`, `wr2rd_forward.sv`, `wr_beat_sequencer.sv`, `rd_cl_aligner.sv`, `page_predictor.sv`, `axi_id_side_table.sv` | no counterpart found |
| `axi_frontend_macro.sv`, `command_scheduler_macro.sv`, `data_path_macro.sv`, `dfi_v21_interface_macro.sv`, `pumice_core_macro.sv`, `pumice_csr_slave.sv` | no counterpart found |

The 16 affected files are every `*_testplan.yaml` except `addr_mapper`,
`dfi_cmd_formatter`, `dfi_signal_pack`, `global_timers`, `init_sequencer`,
`mode_register`, `powerdown_ctrl`, `pumice_top`, `refresh_ctrl`.

## Why it went unnoticed

Before the `mem-ctrl-ip` rename (6a360da01) the *directory* component of
every one of these paths was also wrong -- they said `.../pumice/` and
`.../ddr2-lpddr2/` rather than `pumice-ddr2-lpddr2/`. **All 50 refs were
broken at HEAD**, so nothing distinguished "stale directory" from "stale
module". That rename normalized the directory part and 21 refs started
resolving, which is what exposed the remaining 29 as a different problem.

Nothing reads these testplans in any gate, which is why they rotted through
a whole rearchitecture. That is the part worth fixing: a testplan nobody
parses is a document that cannot be wrong.

## Done when

- Every surviving testplan's `rtl_file` and `test_file` resolve, and
  testplans for dissolved modules are deleted rather than repointed at a
  vaguely similar block.
- A check parses them so this cannot rot again -- extend the existing
  `bin/check_task_ids.py`-style sweep or add the refs to the filelist
  registry's broken-ref pass, which already walks `.f` targets the same way.

## Not in scope

The `mem-ctrl-ip` rename itself, which is done. This item is only the
module-name staleness that rename uncovered.
