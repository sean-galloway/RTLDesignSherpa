# TASK-019: monbus_axil4_group_1wr in place of monbus_axil4_axil4_group

**Priority:** P3
**Status:** open -- 2026-10-24
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
