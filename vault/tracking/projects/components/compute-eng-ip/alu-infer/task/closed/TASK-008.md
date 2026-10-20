# TASK-008: alu-infer gets its own component area + RDS-DV BFM testbench

**Priority:** P2
**Status:** CLOSED 2026-10-20
**Owner:** sean galloway

## Why

Two owner directives, same day:

1. The alu-infer RTL belongs in `projects/components/compute-eng-ip/alu-infer/`,
   not inside `cell/`, organized like the other component areas
   (dma-ip/stream pattern: flat RTL + per-block filelists + `<area>_all.f`
   lint master + four-line area Makefiles, discoverable `dv/tests` suite).
2. The alu-infer DV must follow the repo methodology end to end: the stream
   area's runner pattern, and every valid/ready interface driven/observed by
   the RDS-DV GAXI BFMs (`GAXIMaster`/`GAXISlave`/`GAXIMonitor`), not
   hand-rolled `dut.*` pokes.

## What

- `git mv` of `alu_infer_{top,rows,pipe,acc}.sv` + `alu_infer_top.f` to
  `alu-infer/rtl/` (+`filelists/alu-infer_all.f`, area Makefile);
  `test_alu_infer.py` to `alu-infer/dv/tests/` (+ Makefile, conftest).
- Cell area fixed: `cell_top.f`/`cell_all.f` include the block's filelist at
  its new home (slice-3 dependency); stale build dirs and markers removed;
  `bin/filelists.toml` gained the `alu-infer` area (registry `--check` and
  `--placement` ratchets pass).
- New `alu-infer/dv/tbclasses/alu_infer_tb.py`: `AluInferTB(TBBase)` owns both
  handshakes through BFMs — issue side by a GAXIMaster (prefix `''`,
  multi-signal fields op_line_a/op_line_b/threshold_imm/func_sel/acc_ctrl),
  result side by a GAXISlave (prefix `result`, fields line/flags), passive
  GAXIMonitors on both. Golden models moved here unchanged. Deterministic
  timing via `set_ready_policy('stall'/'always')` + FlexRandomizer sequences;
  latency/order checks anchor on BFM packet timestamps (master stamps the
  accepting edge, slave the retiring cycle) — immune to BFM phase offsets.
- Runner rewritten to the repo standard: one cocotb test dispatching on
  TEST_TYPE, `generate_params()` by REG_LEVEL, one fully parametrized pytest
  wrapper; func/full add a `GAXI_TIMING_PROFILE` sweep (gaxi_realistic,
  gaxi_backpressure, gaxi_stress) on the mixed soak.
- MAS ch05 rewritten to describe the as-built DV; README/PRD/index placement
  statements reconciled (revs pinned 0.50).

## Evidence (2026-10-20)

| Check | Result |
|---|---|
| `make -C alu-infer/rtl verilator` | PASS (23 modules) |
| `make -C cell/rtl verilator` | PASS (33 modules) |
| alu-infer gate (13 types × PIPE_DEPTH {4,8}) | 26/26 PASS |
| alu-infer func (same × {gate,func} levels + gaxi_realistic/gaxi_backpressure soaks) | 56/56 PASS |
| cell gate (`test_cell`, post-move) | 1/1 PASS |
| `filelist_registry.py --check / --placement` | PASS, alu-infer 4/4 covered |

Note: the pre-BFM suite's exact cycle semantics are preserved — comb rows
measure retirement-cycle 0 after issue, add/sub measure `ADDER_LATENCY`,
the join offers the slow head at exactly its deadline with `ready` held.
