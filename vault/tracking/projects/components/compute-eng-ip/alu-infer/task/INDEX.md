<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# projects/components/compute-eng-ip/alu-infer — tasks

**Next ID: TASK-010** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 6 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 3 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-001** — line-reduce row: sum/max tree over a span of lines into the fp32 accumulator (unlocks softmax/layernorm/pooling); owner ruling 2026-10-19, PRD §3 roadmap
- **TASK-002** — PWL/LUT activation row: 256-entry LUT + linear interpolation for sigmoid/tanh/gelu/exp; exp + reciprocal-multiply covers softmax's divide; owner ruling 2026-10-19, PRD §3 roadmap
- **TASK-003** — const/bias row: emit the immediate register as a result line so programs build bias lines without memory traffic; owner ruling 2026-10-19, PRD §3 roadmap
- **TASK-004** — int8 x4-lane element width via func_sel[8:7] (open item M6): same MAC fabric, 4 MACs/clk; owner ruling 2026-10-19, PRD §3 format roadmap
- **TASK-005** — fp32 single-lane element width via func_sel[8:7] (open item M6): general vector engine; owner ruling 2026-10-19, PRD §3 format roadmap
- **TASK-007** — close the M1-M8 numeric-policy open items at FPGA bring-up (NaN/inf semantics, exception flags, FTZ policy, threshold_imm encoding, element-width field, per-row latency table)

## Active

## Closed

- **TASK-006** — tag/same-tag alignment in RTL: 8-bit tag + tag FIFO + arrival join replace the alu_infer_pipe timer mailbox -- CLOSED 2026-10-20: tag FIFO + join as-built (late row write joins by tag compare); ROW_LATENCY superseded by PIPE_DEPTH/ADDER_LATENCY; 13 tests x {gate,func} x PIPE_DEPTH {4,8} green; MAS 0.50 + diagrams + waveforms + PDF regenerated
- **TASK-008** — alu-infer own component area + RDS-DV BFM testbench -- CLOSED 2026-10-20: RTL moved cell/rtl -> alu-infer/rtl (stream-style area: filelists + lint master + area Makefile), DV rebuilt on GAXI master/slave/monitor BFMs with a tbclasses AluInferTB and a thin TEST_TYPE runner; gate 26/26, func 56/56 (incl. gaxi_realistic/gaxi_backpressure soak profiles); MAS ch05 reconciled
- **TASK-009** — testplan coverage map + standard delay-profile sweep -- CLOSED 2026-10-20: dv/testplans/alu_infer_top_testplan.yaml generated from real per-scenario coverage data (gen_alu_infer_testplan.py checked in beside it), 13/13 scenarios VERIFIED under verify_testplan_coverage.py --strict; soak sweep now uses standard GAXI_RANDOMIZER_CONFIGS profiles (fast/slow_producer/slow_consumer/gaxi_realistic/gaxi_backpressure + FULL adds constrained/burst_pause/high_throughput/gaxi_stress); 62/62 green with COVERAGE=1; verifier '~'-prefix regex bug fixed
