# TASK-006: monbus_group drains everything to the fabric, per-class address steering

**Priority:** P2
**Status:** OPEN
**Owner:** sean galloway

## Why

The `monbus_*_group` family today has two drains: the error FIFO the host
reads back over the AXI-Lite slave behind `irq_out`, and the write FIFO the
group flushes as AXI bursts into one memory ring `[cfg_base_addr,
cfg_limit_addr]`. The owner's direction (2026-10-20): the group should have
**one output only — to the fabric** — with different classes of packets
steered to different addresses/SRAMs. The AXI-Lite read-back path goes away
as a data drain; the interrupt does not.

## What

- Single drain: every packet the group keeps leaves on the master (fabric)
  write path. The error FIFO as a host-read data structure is removed.
- Per-class address steering: packet classes (error, timeout, completion,
  threshold, perf, debug, ...) route to independent address regions —
  per-class `cfg_<class>_base_addr` / `cfg_<class>_limit_addr` rings (or
  equivalent), so a class lands in its own SRAM/ring and the host knows
  where to look by class without demuxing one shared ring.
- **IRQ still asserts on errors**: a packet steered to the error class's
  region also raises/holds `irq_out` (error ring non-empty or per-packet
  policy — pin the exact semantics in the module doc when implemented).
- Config surface grows per-class address registers; the
  `cfg_<proto>_err_select` steering masks are superseded by per-class
  region routing (decide whether err_select survives as a second
  destination mask or is dropped).
- Update the six group wrappers (axi4_axi4, axi4_axil4, axil4_axi4,
  axil4_axil4, wb4_axi4, wb4_axil4), `monbus_group_core`, and the formal
  suite at `formal/amba/monbus_group_core` (the routing rule, `monbus_ready`,
  FIFO accounting, flush-burst legality are proved there and must be
  re-closed against the new routing).
- Whitepaper chapters on drain path selection and the spine need the
  two-drain description replaced with the single fabric drain +
  per-class regions.

## Notes

- Interacts with TASK-005 (global usync timer): both touch the group
  family's record write path; sequence them deliberately.
- Tile/HIVE direction: in-band drains over the fabric are the long-term
  consumer; per-class rings are the near-term shape.
