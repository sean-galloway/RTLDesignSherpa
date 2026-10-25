# TASK-039: monbus_axil4_group_1wr in place of monbus_axil4_axil4_group

**Priority:** P3
**Status:** CLOSED 2026-10-25 -- every RAPIDS top (byte, beats, 8/16ch, CXS, rapids-g) on `monbus_axil4_group_1wr`: `s_axil_err_*` gone, `cfg_mon_err_*` inputs and `mon_err_rec_count` added; TBs and both Genesys 2 harnesses follow; books at Beats HAS 0.18 / Beats MAS 0.15 / HAS 0.95 / MAS 0.85. Board run waived: the Genesys 2 carries STREAM only (owner 2026-10-24)
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

## Closed (2026-10-25)

- **RTL.** `rapids_top_base.sv` and `rapids_beats_top_base.sv` instantiate
  `monbus_axil4_group_1wr` (`FIFO_DEPTH_ERR` 192); the eight plane tops and the
  five rapids-g tops regenerated (`gen_plane_tops.py`, `gen_rapids_g.py`,
  both `--check` clean). The `s_axil_err_*` ports are gone; the tops gained
  `cfg_mon_err_base_addr`, `cfg_mon_err_limit_addr`,
  `cfg_mon_err_flush_watermark` (inputs, beside `cfg_mon_*`) and
  `mon_err_rec_count` (16-bit output). No RDL change: RAPIDS takes its monitor
  windows as top-level ports, not registers.
- **Filelists.** `macro/monbus_axil_group.f`, `top/rapids_top_base_common.f`,
  `top_beats/rapids_beats_top_base.f`, `top_g/rapids_g_top_base_common.f`
  include `monbus_axil4_group_1wr.f`.
- **DV.** `rapids_top_tb.py` / `rapids_beats_top_tb.py` drive the error window
  (0x5000..0x5FFF, watermark 3) instead of quiescing the read port. Gates on
  `top`, `top_beats`, `top_g` run from `make clean-all`.
- **Board harnesses.** `flows-rapids/rtl/rapids_byte_harness.sv` and
  `flows-rapids-beats/rtl/rapids_char_harness.sv` place the error window in
  the 64 KB above the trace window and leave `mon_err_rec_count` unread; both
  lint clean. No board run: the Genesys 2 carries STREAM only (owner,
  2026-10-24), so the board half of "Done when" is waived.
- **Books.** Beats HAS 0.18 (block diagram, MonBus delivery, initialization,
  error handling, resources, seven figures), Beats MAS 0.15 (`rapids_beats_top`,
  register descriptions, two figures), HAS 0.95, MAS 0.85, and the
  rapids_beats board notes.
- **Left as is.** `rtl/macro/monbus_axil_group_2in.sv` (the two-input wrapper
  over `monbus_axil4_axil4_group`, instantiated by no top) and its macro test
  keep the two-port group.
