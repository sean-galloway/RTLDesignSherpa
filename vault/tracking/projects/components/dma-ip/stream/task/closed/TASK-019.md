# TASK-019: monbus_axil4_group_1wr in place of monbus_axil4_axil4_group

**Priority:** P3
**Status:** CLOSED 2026-10-25 -- both STREAM tops (and stream-g) on `monbus_axil4_group_1wr`; `MON_GROUP_ERR_*` window + `MON_ERR_REC_COUNT` in the RDL; `test_stream_top_monbus` reads the records from memory (one irq pulse per record, count matches); Genesys 2 harness: error window = top 4 KB of `comp_sram`, `dump_monbus.py` reads it; books at MAS 0.104 / HAS 0.101 / board 1.5
**Owner:** sean galloway

## Why

Owner 2026-10-24: put `rtl/amba/ocelus/monbus_axil4_group_1wr.sv` in place of
`monbus_axil4_axil4_group.sv` in STREAM (and RAPIDS, rapids TASK-039). The 1wr
group is write-only: everything the core accepts lands in memory, error-selected
packets as raw 3-beat records in the error window and the rest in the trace
window, and the host reads records out of memory prompted by `irq_out` and
`err_rec_count`. The AXIL slave-read side of today's group goes away with it.

## What

1. `rtl/top/stream_top_ch8.sv` and `stream_top_ch16.sv` instantiate
   `monbus_axil4_group_1wr`; the monitor's AXIL slave-read port leaves the top.
2. Filelists: `rtl/filelists/macro/monbus_axil_group.f` and
   `rtl/filelists/top/stream_top_common.f` include
   `rtl/amba/filelists/monbus_axil4_group_1wr.f` instead.
3. DV: `dv/tests/top/test_stream_top_monbus.py` and the Genesys 2 stream harness
   read error records from memory on `irq_out` / `err_rec_count`
   (`MonbusGroupHarness`) instead of the slave-read port; the 32-bit err-drain
   path (the fixed f08ccce4 mismatch) is retired with the port.
4. Docs: STREAM HAS/MAS monitor sections and port lists; the board README.

## Done when

Both STREAM tops build on the 1wr group, the full regression passes from
`make clean-all`, the Genesys 2 harness runs on the board with error records
read from memory, and the books carry the new port list.

## Closed (2026-10-25)

- **RTL.** `stream_top_ch8` (and the derived `stream_top_ch16`, `stream_g_top_ch8/16`)
  instantiate `monbus_axil4_group_1wr` (`FIFO_DEPTH_ERR` 192). The `s_axil_err_*`
  port block is gone. New RDL: `MON_GROUP_ERR_BASE_ADDR` (0x26C),
  `MON_GROUP_ERR_LIMIT_ADDR` (0x270), `MON_GROUP_ERR_FLUSH_WATERMARK` (0x274,
  reset 3) and `MON_ERR_REC_COUNT` (0x278, RO, hardware-written). `ERR_SELECT`
  descriptions now say "error window", not "err FIFO".
- **Filelists.** `macro/monbus_axil_group.f`, `top/stream_top_common.f`,
  `top_g/stream_g_top_common.f` include `monbus_axil4_group_1wr.f`; the board
  harness filelist dropped its now-dead `monbus_axil4_axil4_group.f` line.
- **DV.** `MonbusGroupHarness` gained write-only support (`drain_proto=None`,
  `err_window`, `parse_err_records()`, `err_rec_count()`; trace parsing excludes
  the error window). `test_stream_top_monbus` Phase B routes completions to the
  error window and checks: records parse, one `stream_irq` pulse per record,
  `MON_ERR_REC_COUNT` equals the record count, no AXI-protocol completion in the
  trace window, 24-byte stride and wrap. Gate: top 19/19.
- **Board harness (Genesys 2).** No bridge respin: the `stream_err` slot stays
  in `bridge_stream_mon_axil` as RESERVED and `stream_harness` answers SLVERR
  on both its channels. The error window is the top 4 KB of `comp_sram`
  (`bridge_windows.monbus_err_window()`, 170 records); the trace window is the
  rest. `route_monbus()` and `StreamHarnessTB` program both windows by name.
  `dump_monbus.py` reads the error window from memory (count from
  `MON_ERR_REC_COUNT`, `--base`/`--count` to override); `dump_monbus_sram.py`
  is the trace-window reader.
- **Books.** MAS 0.104 (chapter 2.16 retargeted, new figure
  `16_monbus_axil4_group_1wr`, chapters 1/3/4/5 and the index), HAS 0.101
  (interrupt model, block diagram, figures), STREAM FPGA System 1.5 (harness
  and address map). PORT_MAP.md and the stream CLAUDE.md follow.
- **Left as is.** `dv/tests/fub/test_stream_tally_group_chain.py` still drives
  the tally chain from a `monbus_axil4_axil4_group` instance; the slave
  observers (`slave_err`) keep theirs. Both modules still exist in `rtl/amba`.
