# TASK-026: Wishbone B4 CTI/BTE burst hints on wb4_master / wb4_slave

> Migrated 2026-09-27 from `vault/Tasks/amba/closed.md` as **TASK-087** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.

**Priority:** P4 when filed. **Status:** CLOSED 2026-09-10 -- Sean asked for
the bursts, so the parking condition was met by direction rather than by a
consumer appearing. Deferred 2026-09-09.

**What.** B4 registered-feedback cycles: `CTI[2:0]` (classic / constant
address / incrementing / end-of-burst) and `BTE[1:0]` (linear / wrap-4/8/16)
on the request, so a slave that understands them can prefetch or stream.
Both are advisory in B4 and both blocks ignore them today; the pipelined
queues already recover the throughput the hints were invented for on
classic-mode buses.

**Un-defers when:** a Wishbone peer in a real integration needs the hints
(a slave that only streams under CTI, or an interconnect that routes on
BTE), or a FUB with burst descriptors wants them exported. Until then the
family README records them as "not implemented, deliberately".

**Shape when picked up:** optional ports on `wb4_master` (`m_wb_CTI`,
`m_wb_BTE` from new `cmd_cti`/`cmd_bte` queue fields, default classic/
linear) and `wb4_slave` (pass-through to `cmd_*`), a `USE_BURST_HINTS`
parameter so existing consumers see no port change, BFM fields in RDS-DV's
`wb4_packet`, monitor aux bits in `wb4_monitor`, and a formal property that
`CTI = end-of-burst` is the last request of a `CYC` envelope.

**CLOSED 2026-09-10.** `CTI`/`BTE` are carried through the family behind
`USE_BURST_HINTS` (default 0, so no existing consumer changed):

- `wb4_pkg` gains `wb4_cti_t` and `wb4_bte_t`. Both put the non-burst case at
  zero, so a bus with the hint wires tied off is a legal classic bus.
- `wb4_master` takes `cmd_cti`/`cmd_bte` and drives `m_wb_CTI`/`m_wb_BTE`;
  `wb4_slave` takes the bus hints and hands them to its FUB. The hints ride
  **inside the command queue**, so one cannot slip onto a neighbouring
  transfer when the queue delays one.
- Neither block acts on a hint. They are advisory in B4 and deciding what a
  burst means belongs to the peripheral. With the parameter at 0 the ports
  exist and read CLASSIC/LINEAR.
- Threaded through every wrapper: the clock-gated pair, the CDC slave (where
  the hints widen the crossing FIFO so they cross **with** their transfer),
  the retry master, the loopback testcode, and the AXI4-Lite bridge, which
  ties them off because AXI4-Lite has no burst concept to map.

**Proof.** The loopback test gained a `USE_BURST_HINTS` dimension: the TB
drives a plausible pattern (runs of `INCR` closed by `EOB`, classic transfers
between) into the master's command queue and checks each hint arrives at the
slave's FUB **with its own transfer**; with the hints compiled out the
slave's FUB must read CLASSIC/LINEAR whatever the master was handed. Two
mutations caught it: swapping the pack order in the master, and dropping the
hints in the slave, both reported as a mispaired hint at a named address.
All 20 wb4 formal tasks still pass; amba lint PASS.

**Not done, deliberately:** the framework's Wishbone BFMs do not sample
`CTI`/`BTE` off the wires, so the monitor cannot yet check hints on the bus
itself. The loopback covers the pass-through contract end to end, which is
what the RTL promises. `wb4_monitor` does not report hints either; its
`aux_data` has exactly three spare bits for a `CTI` if that is ever wanted.


---
