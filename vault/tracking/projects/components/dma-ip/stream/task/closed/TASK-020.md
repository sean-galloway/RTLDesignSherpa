# TASK-020: stream-g, STREAM with its schedulers sequenced by gatling firmware

**Priority:** P2
**Status:** CLOSED 2026-10-25 -- all six phases delivered and measured: stream-g on the Genesys 2 with its own firmware, the rapids-g metric set reproduced on STREAM (Genesys 2 book 1.4 ch05, HAS 0.100 5.4, MAS 0.103 ch07), regressions green at every level run, TASK-021 closed; commits a85fa3130, c5f1926f6, 2a2fcb4d0, 7c3274660, 833de614f, 4f50aaa32, c9a0c135c
**Owner:** sean galloway

## Why

Owner 2026-10-24: "Can you add Gatling to stream?" -- the firmware-sequenced STREAM variant that stream
TASK-018 left open, built the way rapids-g was built for RAPIDS (rapids TASK-034/035/036/037/038): the
channel policy (take, validate, start, complete, chain, the EXT run bases) runs as firmware on one
gatling per STREAM core, everything at cycle rate stays hardware, and the two are proven equivalent by
a bench that runs the FSM scheduler and scheduler_g side by side against an independent golden model.

## Shape

STREAM differs from RAPIDS where it matters here: length in beats (no bytes-to-beats ceiling), no
control engines, no packet records, no tile, and a hardware read-ahead prefetch (`cfg_rd_prefetch_enable`:
the read side peeks the next chained descriptor and the write side advances in place inside
CH_XFER_DATA). In stream-g the prefetch stays hardware and takes only a head the firmware has STAGEd
(pre-validation, as on rapids-g), so chains stream exactly as today once staged.

## Phases

1. `rtl/fub/scheduler.sv` -> the FSM wrapper + `rtl/fub/scheduler_core.sv` (the datapath), bit-exact:
   the full STREAM regression from clean and the flows sim cycle counts unchanged.
2. `rtl/fub_g/scheduler_g.sv`: the rapids-g window (STATUS/CMD/HEAD_SUM/bases) over the STREAM core.
3. `rtl/macro_g/stream_seq_g.sv` (rapids_seq_g: gatling, ROM/`FW_WRITABLE` BRAM, scratch, mailbox into
   the STREAM regs) and the generated `scheduler_group_array_g` / `stream_core_g` / `stream_top_g_ch{8,16}`
   from `bin/gen_stream_g.py`, as `gen_rapids_g.py` derives rapids-g.
4. Firmware: the rapids-g executive + policy table (`sched_g.S`) retargeted; `FW_*` registers (closes
   stream TASK-018).
5. DV: the equivalence bench (fub_g), macro_g and top_g rehosts; full gate from clean.
6. Genesys 2 stream harness with `STREAM_G=1`, board == sim, gcompare against stream; HAS/MAS chapter.

## Done when

Every phase above is green from `make clean-all`, the board comparison is measured and in the books,
and stream TASK-018 closes with phase 4.

## Progress 2026-10-24

- Phase 1 committed (a85fa3130): the split, bit-exact (same-seed logs identical, 141 cells).
- Phases 2-5 built: `scheduler_g`, `gen_stream_g.py` + the three fragments, FW_* registers in both maps
  (0x3A0-0x3AC, `FW_CTRL.STREAM_G`), the shared rapids-g firmware and sequencer, the edge table, the
  equivalence bench (`stream_g_equiv_tb_top`, 9 cases x 7 configurations, `_pf` prefetch cases),
  macro_g / top_g re-hosts. Gates from clean: fub_g 64/64 at gate, macro_g 159 (+12 skipped: 1-2 channel,
  SHARED_ENGINES=0), top_g 67 (+2 skipped: 1 channel), product fub 510 / macro 684 (+5) / top 69 unchanged
  on the changed core. FPGA lint of the Genesys 2 harness clean with STREAM_G=0 and =1.
- Found on the way: stream BUG-022 (MonBus packets once per cycle in FETCH_DESC / COMPLETE; fixed on entry);
  the core now refuses a next-address selector above the build's (desc_alg_max, as rapids TASK-035).
- MAS 0.103: Chapter 7 (stream-g), Table 2.4.1 (the core's sequencing port), the FW_* registers.
- Phase 6: `make bitstream STREAM_G=1` on build-perf (harness STREAM_G define, BUILD_CONFIG.STREAM_G).

## Phase 6 (board, 2026-10-24)

- Regressions on the final RTL: fub_g 64 gate / 192 full, macro_g 159 (+12 skipped), top_g 67 (+2 skipped),
  all passing from clean-all. One full-level `linear_pf` seed (20583) stalled a gatling channel before the
  last fix: the in-place prefetch advance and `exec_complete` can coincide and scheduler_g took COMPLETE;
  the advance wins now, as in the FSM (MAS 7.2).
- Genesys 2, `build-perf`, 8 channels, 100 MHz. The FIRST stream-g bitstream was dead on the UART (even the
  harness CSRs) while a STREAM_G=0 control built from the same tree answered on the same port. Vivado's log
  had the cause: `Net host_cmd_valid in module/entity stream_g_top_ch8 does not have driver` -- the
  generated top connected the APB slave to the host_* nets BEFORE the include that declares them; Verilator
  resolved the names, Vivado made implicit undriven nets. `bin/gen_stream_g.py` anchors the include before the
  APB slave generate now; `make bitstream` (make/fpga_flow.mk) prints every "does not have driver" line after
  every build; the lesson is in vault/handbook/design/generated-rtl-discipline.md. The scan also surfaced a
  pre-existing one: utility-ip misc BUG-002 (the observers' `w_comp_stat_*` never driven).
- Area/timing (same tree, same flow): STREAM 66,221 LUT / 59,652 FF / 26 BRAM / 64 DSP, WNS +0.790;
  stream-g 65,472 LUT / 58,265 FF / 29 BRAM / 0 DSP, WNS +0.668 (the DSPs were the EXT run-base multipliers,
  now firmware).
- Throughput, 40-config matrix x {1 MB, 64 KB, 4 KB} on both bitstreams, 240/240 pass: stream-g within
  +0.22 % at 1 MB on every config (mean +0.02 %); the cost is ~140-150 cycles once per channel before its
  first read (4 KB single descriptor: 303 -> 444 cycles), ~1-2 cycles per chained descriptor. Within 10 % of
  STREAM from ~24 KB on a channel's first descriptor, 5 % from ~47 KB, 1 % from ~235 KB. The STREAM control's
  1 MB matrix is cycle-identical to 2026-10-03, so the regenerated harness bridge changed nothing.
  Artifacts: `build-perf/results/perf_sweep_2026-10-24_{fsm,g}_{1MB,64KB,4KB}.{csv,json}`; MAS 7.4.
- ILA collateral left in place for the next board question: `STREAM_CHAR_ILA` marks in the harness,
  `fpga/tcl/build_ila.tcl` / `capture_ila.tcl` (`make bitstream-ila`, `make tcl-capture_ila`).
- Board left on the STREAM control bitstream (today's tree); `make program STREAM_G=1` puts stream-g back.
- Board-side host: `harness_addrs.build_info()` reports `stream_g`; the Genesys 2 UART is the FT232R
  (/dev/ttyUSB3), set FPGA_BOARD=genesys2 so autodetect does not scratch-probe the Nexys A7.
- The rapids-g metric set, on STREAM (owner 2026-10-24: stream-g is the subject, STREAM only as the
  baseline): the gcompare / gscale / gscale1 profiles as `build-perf/csv/*.csv`, run on both bitstreams
  (192/192 points each), `bin/compare_profiles.py` (ratios, 10/5/1 % crossovers); the schedulers-alone
  bench (`fub_g` perf case, 8 and 16 channels); the harness-sim profile runner (`char_csv`,
  `test_stream_g_profiles.py`, `make sim-g*`) for the sim == board check; out-of-context stream_core vs
  stream_core_g at 8 and 16 channels (`fpga/tcl/ooc_stream_core.tcl`, `reports/ooc/`). Written up per the
  owner's placement (2026-10-24, "board details in the board HAS, with all the harness configs and block
  diagrams"): the Genesys 2 book (*STREAM on the Genesys 2 -- The FPGA System*, rev 1.4) Chapter 5 carries
  the stream-g build, Figure 5.1 (the DUT's register path in the harness), Figure 5.2 (the A/B method),
  every measured table and the build-knob tables; STREAM HAS Chapter 5.4 (rev 0.100) keeps the choice
  (selection guide, schedulers-alone bench, crossovers) and points there, the twin of rapids HAS 6.4. Crossovers (every channel busy):
  single descriptor within 10/5/1 % from 4 KB / 8 KB / 32 KB, 16-descriptor chain from 256 B / 512 B /
  1 KB; one channel busy: single 32 KB / 64 KB / 256 KB, chain 4 KB / 4 KB / 16 KB. Filed TASK-021 (the
  lone-channel chain's 32-beat dip).
- Owner 2026-10-24: "Rapids and stream firmware shouldn't be common." stream-g owns its image now:
  `rtl/fw_g/sched_g.S` (forked from rapids-g's, header says so), `bin/gen_stream_g_fw.py` (imports rapids'
  assembler/renderer, writes `rtl/macro_g/generated/fw/sched_g_fw.svh`, `--check`). rapids' `rapids_seq_g.f` split
  into `rapids_seq_g_core.f` (block + gatling, no image) + the rapids image; stream pulls the core and puts its own
  fw directory on the path, the only `sched_g_fw.svh` reachable -- the Vivado flattener SORTS include dirs, so two
  same-named files would have resolved to rapids' in the bitstream regardless of filelist order (verilator -E and
  the FPGA lint prove each design compiles its own). rapids' firmware source and image are byte-identical to HEAD.
- 2026-10-25: the profiles and the matrix re-measured on the rebuilt stream-g bitstream (STREAM's own firmware,
  bit sha256 d416ce72...): lone-channel chain crossovers 2 KB / 2 KB / 8 KB, every-channel-busy chain 256 B /
  256 B / 512 B, singles unchanged; STREAM side cycle-identical to 10-24 on all 96 points. Board book 1.4 Tables
  5.3-5.7 regenerated from the 10-25 pair; HAS 5.4 guide and crossovers updated; the 10-24 (first image) results
  kept beside them.

