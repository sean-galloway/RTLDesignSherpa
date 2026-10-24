# TASK-020: stream-g, STREAM with its schedulers sequenced by gatling firmware

**Priority:** P2
**Status:** active -- opened 2026-10-24
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
