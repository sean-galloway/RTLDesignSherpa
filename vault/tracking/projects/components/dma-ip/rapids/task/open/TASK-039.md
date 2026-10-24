# TASK-039: monbus_axil4_group_1wr in place of monbus_axil4_axil4_group

**Priority:** P3
**Status:** open -- 2026-10-24
**Owner:** sean galloway

## Why

Owner 2026-10-24: put `rtl/amba/ocelus/monbus_axil4_group_1wr.sv` in place of
`monbus_axil4_axil4_group.sv` in RAPIDS (and STREAM, stream TASK-019). The 1wr
group is write-only: everything the core accepts lands in memory, error-selected
packets as raw 3-beat records in the error window and the rest in the trace
window, and the host reads records out of memory prompted by `irq_out` and
`err_rec_count`. The AXIL slave-read side of today's group (its read FUB and the
AXIL-to-AXI4 read bridge) goes away with it.

## What

1. Every RAPIDS top that instantiates `monbus_axil4_axil4_group` moves to
   `monbus_axil4_group_1wr`: `rtl/top/rapids_top_base.sv` (and the generated
   `rapids_top`, `rapids_cxs_top`, `rapids_{8,16}ch{,_cxs}_top` through
   `bin/gen_plane_tops.py`), `rtl/top_beats/rapids_beats_top_base.sv` and its
   generated tops, and the rapids-g tops through `bin/gen_rapids_g.py`. The
   monitor's AXIL slave-read port leaves the top-level interface.
2. Filelists: the top closures include `rtl/amba/filelists/monbus_axil4_group_1wr.f`
   instead of `monbus_axil4_axil4_group.f` (`bin/filelists.toml` registry).
3. DV: the top TBs and the Genesys 2 harness stop driving the monitor read port
   and read error records from memory on `irq_out` / `err_rec_count`
   (`MonbusGroupHarness` in `bin/TBClasses/scoreboards/monbus_group`).
4. Docs: HAS/MAS monitor sections and the port lists regenerated; the board
   harness README.

## Done when

Every RAPIDS top builds on the 1wr group, the full regression passes from
`make clean-all` (byte, beats and -g trees), the Genesys 2 harness runs on the
board with error records read from memory, and the books carry the new port
list. STREAM follows under stream TASK-019.
