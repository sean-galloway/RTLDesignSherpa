<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# cdc — Open (accepted, ready to start)

## CDC-003: fifo_async wavedrom scenarios hand-drive dut.read against a live BFM

**Priority:** P3. A TB defect, not an RTL one. Found by the CDC-001 testqc
round (part_03), raised SUSPECTED and confirmed by reading the framework.
**Status:** open 2026-09-16.

`FifoAsyncWaveDromTB` (in `val/cdc/test_fifo_async_wavedrom.py`) writes through
the BFM -- `await self.write_master.send(packet)` -- but reads by poking the
pin directly, at three sites:

```python
self.dut.read.value = 1
await RisingEdge(self.rd_clk)
self.dut.read.value = 0
```

Its base `FifoBufferTB` constructs `self.read_slave = FIFOSlave(...)`, and
`FIFOSlave` extends `FIFOMonitorBase(FIFOComponentBase, BusMonitor)` -- cocotb's
`BusMonitor.__init__` auto-starts `_monitor_recv`. `FIFOSlave` drives the same
pin through `_set_rd_ready()` at five sites (line 191 drives it HIGH during the
receive phase). So two drivers contend for `dut.read`.

This also breaks the repo's standing rule: drive through the BFMs, never
hand-poke a valid/ready interface.

**Why it is filed rather than fixed:** the scenarios exist to emit specific
wavedrom diagrams, and the committed JSON is a deliverable. Moving reads onto
the BFM changes capture timing and therefore the diagrams, which needs a look
at the rendered output rather than a green test.

