# TASK-041: formal task for monbus_group_core / monbus_axil4_axil4_group

**Priority:** P2. Filed 2026-09-28 from the rapids/stream formal pass (rapids
TASK-016).
**Status:** CLOSED 2026-09-28.

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

---

## CLOSED 2026-09-28

`formal/amba/monbus_group_core/` (Makefile, `monbus_group_core.sby`,
`formal_monbus_group_core.sv`, sv2v flat of the `monbus_group.f` closure).
Raw record mode, FIFO_DEPTH_ERR 4, FIFO_DEPTH_WRITE 8, MAX_BURST_BEATS 8,
FLUSH_TIMEOUT_CYCLES 8. Everything is checked at the PORTS against a
harness-side reference model of the routing decision and the 3-beat
expander, so the proof owes nothing to internal names (the retired stream
harness had checked reset values and FIFO bounds only):

- routing: `monbus_ready == dropped || (to_err && !err_fifo_full) || expander-accept`
  cycle-exact, with drop / err-FIFO / write-path decided by the per-protocol
  pkt_mask, err_select and event-mask rule (1 = drop; unknown protocol
  dropped; a masked event reaches neither FIFO) -- so the group never
  withholds ready from a packet the FIFOs could take and never takes one it
  has no room for
- FIFO accounting: `err_fifo_count` steps by records pushed minus records
  read out (a record is three `fub_s` R beats), `write_fifo_count` by expander
  pushes minus `fub_m` W handshakes; both bounded by depth; full flags,
  `irq_out` and `s_rvalid` follow the registered count by one cycle
- the flush burst is a legal AXI write: awvalid/addr/len held to awready,
  8-byte INCR, wstrb all ones, awlen+1 <= MAX_BURST_BEATS, exactly awlen+1 W
  beats with wlast on the last, bready only after it, address in
  [base, limit] and never across 4 KB, and planned only from beats already in
  the FIFO
- 24 assertions, BMC depth 14 (smtbmc z3, 30 min); 14 covers all reached at
  depth 40: each routing outcome, an error record read back through `fub_s`,
  both FIFOs busy, a watermark flush and a timeout flush each carried through
  AW/W/B (the timeout flush at step 17, which is why FLUSH_TIMEOUT is 8 here)

Two things the harness taught: `gaxi_fifo_sync` computes `count` from the
NEXT pointers, so a push shows the same cycle while full/empty are
registered; and `fub_m_awready` may be high the cycle awvalid rises, so a
burst tracker must take the handshake in its first state. Nothing in the
RTL needed to change. The six protocol wrappers remain thin shells over this
core; a per-wrapper task is optional as the item said.
