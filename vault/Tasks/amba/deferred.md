<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# AMBA tasks: deferred

Accepted, deliberately parked. Each block names the condition that un-defers it.

---

### TASK-087: Wishbone B4 CTI/BTE burst hints on wb4_master / wb4_slave

**Priority:** P4 (far future). **Status:** deferred 2026-09-09 at Sean's
direction ("add to far future todo") when the wb4 family landed.

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
