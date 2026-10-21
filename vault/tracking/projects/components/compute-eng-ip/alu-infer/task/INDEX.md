<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# projects/components/compute-eng-ip/alu-infer — tasks

**Next ID: TASK-011** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 2 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 8 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-010** — make the accumulate row close at a real FPGA clock: first synthesis failed 50 MHz by -128 ns (single-cycle fp32 FMA accumulate loop + zero MUL/MAC latency in the harness slot)
- **TASK-007** — close the M1-M8 numeric-policy open items at FPGA bring-up (NaN/inf semantics, exception flags, FTZ policy, threshold_imm encoding, element-width field, per-row latency table)

## Active

## Closed

- **TASK-001** — line-reduce row -- CLOSED 2026-10-20: REDUCE sum/max into the accumulator bank, every format, identity CLEAR, cross-lane fold; softmax sequence in alu-infer DV (1.6e-3 vs float)
- **TASK-002** — PWL/LUT activation row -- CLOSED 2026-10-20: 256-entry LUT loaded in-band, bin/alu_infer_pwl.py builder + bit model; bit-exact + accuracy-bounded test
- **TASK-003** — const/bias row -- CLOSED 2026-10-20: OP_CONST broadcast in every format
- **TASK-004** — int8 x4 lanes -- CLOSED 2026-10-20: saturating rows, int32 MAC/REDUCE with requantize shift, bf16<->int8 CVT
- **TASK-005** — fp32 single lane -- CLOSED 2026-10-20: IEEE fp32 rows on adder/mul/acc ports; fp8 e4m3 added as format 3
- **TASK-006** — tag/same-tag alignment in RTL: 8-bit tag + tag FIFO + arrival join replace the alu_infer_pipe timer mailbox -- CLOSED 2026-10-20: tag FIFO + join as-built (late row write joins by tag compare); ROW_LATENCY superseded by PIPE_DEPTH/ADDER_LATENCY; 13 tests x {gate,func} x PIPE_DEPTH {4,8} green; MAS 0.50 + diagrams + waveforms + PDF regenerated
- **TASK-008** — alu-infer own component area + RDS-DV BFM testbench -- CLOSED 2026-10-20: RTL moved cell/rtl -> alu-infer/rtl (stream-style area: filelists + lint master + area Makefile), DV rebuilt on GAXI master/slave/monitor BFMs with a tbclasses AluInferTB and a thin TEST_TYPE runner; gate 26/26, func 56/56 (incl. gaxi_realistic/gaxi_backpressure soak profiles); MAS ch05 reconciled
- **TASK-009** — testplan coverage map + standard delay-profile sweep -- CLOSED 2026-10-20: dv/testplans/alu_infer_top_testplan.yaml generated from real per-scenario coverage data (gen_alu_infer_testplan.py checked in beside it), 13/13 scenarios VERIFIED under verify_testplan_coverage.py --strict; soak sweep now uses standard GAXI_RANDOMIZER_CONFIGS profiles (fast/slow_producer/slow_consumer/gaxi_realistic/gaxi_backpressure + FULL adds constrained/burst_pause/high_throughput/gaxi_stress); 62/62 green with COVERAGE=1; verifier '~'-prefix regex bug fixed
