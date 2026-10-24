# TASK-048: Re-run characterization once STREAM and RAPIDS drop in the 1wr monbus group

**Priority:** P2
**Status:** deferred (filed 2026-10-23)
**Owner:** TBD
**Un-defers when:** `stream_top_ch8` and `rapids_beats_top` / `rapids_beats_cxs_top` instantiate `monbus_axil4_group_1wr` or `monbus_axi4_group_1wr` in place of the two-port `monbus_axil4_axil4_group` / `monbus_axi4_axi4_group`.

`monbus_group_core_1wr` and its two protocol wrappers (2026-10-23) replace the
slave-read error drain with a second memory window on the one write port:
errors land in their own window as raw records, `irq_out` pulses once per
record landed, and the host reads them out of memory. STREAM and RAPIDS still
carry the two-port groups, and every published number for the group is for
those: the out-of-context rows in
`docs/markdown/rtl-amba/monitor/monitor_characterization.md` (amba TASK-034)
and the on-board `stream_char` / `rapids_char` figures. Once the two tops move
to the 1wr wrappers, those numbers describe a block that is no longer in the
design.

Expected movement, to be measured rather than assumed: the slave-read FUB,
its skids and the 192-bit error FIFO go away; a second `monbus_burst_writer`,
`monbus_wr_mux2` and a 64-bit error beat FIFO (`FIFO_DEPTH_ERR` 192 beats by
default) come in. The write port now carries both windows, so the memory-side
bandwidth split and the error-record latency to the host change shape.

## Do
- Add the 1wr wrappers to the monitor OOC sweep and re-run it on both parts:
  `rtl/amba/fpga/bin/monitor_synth_sweep.sh monbus_axil4_group_1wr monbus_axi4_group_1wr`
  (Kintex-7 325T -2 at 6.667 ns and `TARGETS="xc7a100tcsg324-1:10.0"`), then
  `summary_table.py`; add the rows next to the two-port groups in
  `monitor_characterization.md` and update its "Aggregation" row.
- Re-run the `stream_char` and `rapids_char` board builds and host programs on
  the 1wr tops, with the host reading the error window out of memory on
  `irq_out` (latch it with a `hwset` W1C bit) instead of popping the drain port.
  Re-measure the monitor-build throughput and the error-record latency.
- Update the STREAM and RAPIDS char docs and the perf figures that cite the
  group's cost, and re-check the timing knife edge the monbus CAM route set on
  `stream_char` (the route changed shape; it may have moved).

## Done when
- `monitor_characterization.md` has OOC rows for both 1wr wrappers on both parts, same recipe and defaults as the existing rows
- `stream_char` and `rapids_char` numbers are re-measured on the 1wr tops and their docs say so, dated
- any number elsewhere that quotes the two-port group's cost or latency is either updated or marked as the two-port figure

## Related
- 1wr family: `rtl/amba/ocelus/monbus_group_core_1wr.sv`, `monbus_axil4_group_1wr.sv`, `monbus_axi4_group_1wr.sv`; docs under `docs/markdown/rtl-amba/monitor/`
- amba TASK-034 (closed): the characterization this re-runs
- Consumers today: `projects/components/dma-ip/stream/rtl/top/stream_top_ch8.sv`, `projects/components/dma-ip/rapids/rtl/top_beats/rapids_beats_top.sv`, `rapids_beats_cxs_top.sv`
