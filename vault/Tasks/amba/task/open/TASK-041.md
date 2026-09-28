# TASK-041: formal task for monbus_group_core / monbus_axil4_axil4_group

**Priority:** P2. Filed 2026-09-28 from the rapids/stream formal pass (rapids
TASK-016).
**Status:** OPEN.

## Why

`formal/stream/monbus_axil_group` proved the legacy `monbus_axil_group`, which
was replaced by `rtl/amba/monitor/monbus_axil4_axil4_group` (a thin wrapper
over `monbus_group_core`). The DUT file is gone, so that task was retired on
2026-09-28; its April PASS described a module that no longer exists. Nothing
in `formal/amba` proves the group core or any of the six protocol wrappers,
and the group is on every DMA's monitor path (STREAM, RAPIDS, the bridge's
WB4/AXI4 variants).

## What to prove

Port the retired harness (`git show dbaedc9ed:formal/stream/monbus_axil_group/formal_monbus_axil_group.sv`)
onto `monbus_group_core`: packet routing by protocol and type (drop mask,
err_select, per-event masks -- 1 = drop), the error FIFO and the raw 3-beat
capture record, the flush watermark, `monbus_ready` never dropping a packet
the FIFOs could take, and a cover for one record written through the
AXI-Lite master. A second thin task per wrapper is optional once the core is
proved.
