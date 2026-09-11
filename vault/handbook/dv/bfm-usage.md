---
title: BFM usage
summary: Use RDS-DV framework BFMs; never hand-roll. Map + trap list.
---

# Use the framework BFMs - never re-roll

The CocoTBFramework (RTLDesignSherpa-DV repo, editable-installed) plus the
bin/TBClasses wrappers cover every protocol here. Hand-rolled drivers miss
timing corners; hand-rolled decoders desync from packet formats. Missing
BFM = add it to RDS-DV, never inline.

| Interface | Use |
|---|---|
| custom valid/ready | GAXIMaster/GAXISlave (components.gaxi) |
| AXI4 | axi4 factories + AXI4Sequence (never hand-poke s_axi_*) |
| AXI4-Lite / APB / AXIS | axil4 / apb / axis4+axis5 factories |
| Wishbone B4 (pipelined) | wb4 factories (components.wb4): WB4Master / WB4Slave / WB4Monitor; STALL, CYC and in-order termination are why it is not a GAXI composition |
| MonBus receive | TBClasses.monbus.MonbusSlave |
| MonBus decode | TBClasses.monbus.parse() ONLY |
| MonBus groups | MonbusGroupHarness (scoreboards.monbus_group) |
| Registers | [[registers-by-name]] |

| Arbiters | ArbiterMaster + RoundRobinArbiterMonitor (components.shared) |

Decision line: standard protocol -> factory; custom valid/ready -> GAXI;
<50-line test-local helper may stay embedded; anything reusable -> RDS-DV.

Factory entry points, per family (count = callables in that file):
`gaxi_factories` 8, `axi4_factories` 17, `axil4_factories` 18,
`apb_factories` 7, `axis_factories` 11, `fifo_factories` 14, `wb4_factories` 3. DFI, UART and
SMBus have no factory module - construct their components directly
(`dfi_master_mc.py`, `uart_components.py`, `smbus_components.py`).

This note covers the BFM axis ONLY. What traffic to send (sequences) and what
timing shape to send it at (randomization) are INDEPENDENT choices - see
[[rds-dv-axes]] for the three-axis framing, and [[randomization]] for the
profile catalogue. Using the right BFM says nothing about whether the test
stresses anything.

Authoritative per-family API docs live in RDS-DV itself
(`docs/components/<family>/`, published at
sean-galloway.github.io/RTLDesignSherpa-DV) - read those rather than
reverse-engineering from source.

Traps (each cost real debug time):
- cocotb Monitor.__len__ = queue depth: empty-queue BFM is FALSY, so
  `x.get_stats() if x else {}` silently returns {}. Use `is not None`.
- signal_map requires ALL of {valid, ready, data}.
- Default ready profile delays reach 30 cycles; drain/quiet windows must
  exceed max-delay+refill (~40) AND check bus idle ([[seeds-and-determinism]]
  has the companion rule).
- Don't spawn private _monitor_recv on self-registering components.
- TB classes live in the PROJECT area (projects/**/dv/tbclasses), never in
  the shared framework.

## Out of range means one thing (2026-09-09)

Every memory-backed slave BFM -- AXI4, AXI5, AXIL4, AXIL5 `Slave{Read,Write}`,
`APB`/`APB5 Slave` and `WB4Slave` -- answers an access beyond its `MemoryModel` the
same way: **SLVERR** (`PSLVERR` on APB, `ERR` on Wishbone), **nothing written** (an AXI write
burst is checked whole before any beat lands), **read data 0xDEADDEAD**
replicated to the beat width, **one WARNING** naming the slave, the address
and the model size. It is one code path, `MemoryModel.in_range` /
`oor_warning` / `oor_read_data` in RDS-DV `shared/memory_model.py`, and a
structural unit test there asserts every family calls it.

*Case: before this, the four families disagreed -- AXI4/AXI5 answered OKAY,
dropped the write and returned the ADDRESS as read data; AXIL answered
SLVERR; APB grew its memory. The bridge's boundary probe reached the right
slave past its 4 KB model, got OKAY from an AXI4 slave and SLVERR from an
AXIL one, and the TB comment that called the silent OKAY "the framework
behaviour" was true of one slave type. The tests were first "fixed" by
widening the model (BRIDGE-008); the disagreement stayed until this.*

*Case 2 (2026-09-11): `WB4Slave` was written after the contract and did not
follow it -- a bounds miss raised inside its sampling loop and the whole BFM
died, and it addressed memory with the raw `ADR`, so it could not sit at a
fabric address at all. Both surfaced the day a bridge put a Wishbone
completer at 0x5000_0000 (BRIDGE-019). A new slave family is not done until
it has `base_addr` and the OOR path; the structural unit test in RDS-DV is
the place to add the new class.*

Two consequences for a TB:

- `single_write` / `write_transaction` do **not** raise on an error response;
  they report it in the returned dict. A helper that awaits the write and
  drops the dict passes a SLVERR write silently -- the bridge's generated
  `master_write` did exactly that. Check `result['success']` (or raise).
- The model's limit is not the design's. An address the RTL does not decode
  at all is the design's own error path (the bridge's subtractive slave
  answers DECERR); a probe past the model is answered by the slave the
  address decodes to, and that SLVERR coming back from the right port is
  routing evidence, not a failure.

`APBSlave(error_overflow=False)` keeps the old grow-the-memory behaviour for
a slave meant to accept any address; the default is now the error.

## An ID in flight is a resource (2026-09-10)

The AXI5 BFMs key their response queues on transaction ID: every R or B
beat lands in a per-ID deque and the coroutine that issued that ID pops it.
Two transactions in flight with one ID therefore share one queue, and the
first coroutine to wake takes whichever beat arrived, regardless of whose
it was. AXI itself only permits same-ID reuse for ordinary reads and
writes; an atomic must not share its ID with ANY outstanding transaction
from the same Manager, because a read-return atomic answers on R under its
AW ID and that is the only thing that tells its beat from a read's.

Measured on the bridge A5-3b sign-off test at full depth: a concurrency
phase rotated 14 IDs over 32 in-flight transactions, so word seven reused
word zero's four IDs while word zero was still outstanding. A read then
starved for 5000 cycles waiting on a queue another coroutine had drained,
and it looked exactly like a routing bug in the fabric. The fabric was
fine. The fix is structural, not a bigger timeout: batch the traffic so
that everything in flight at once holds a distinct ID (with a 4-bit ID and
four transactions per word, three words per batch), and await the batch
before reusing one. `AXI5ComplianceChecker` now records ATOMIC_ID_IN_USE
when an atomic is issued under an ID a read or write still holds, and
R_WITHOUT_REQUEST for an R beat nobody asked for; the first would have
named this in the compliance report had the test reached it.

For read-return atomics themselves: `AXI5MasterWrite.atomic_operation`
takes `read_channel=` (the port's `AXI5MasterRead`) and returns
`read_data` / `read_resp` alongside the B result; the paired
`AXI5SlaveWrite` performs the operation on its memory model and hands the
original data to `AXI5SlaveRead.send_read_return`. The generated bridge TB
pairs the two slave BFMs for every AXI5 rw slave.

