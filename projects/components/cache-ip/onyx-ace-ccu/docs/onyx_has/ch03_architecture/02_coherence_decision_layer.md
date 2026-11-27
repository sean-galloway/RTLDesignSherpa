<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# Coherence Decision Layer

**Status:** architecture recorded 2026-11-21 (D3 and D6 decided 2026-11-20, PRD v0.7).

## Snoop fanout: broadcast

onyx v1 keeps no sharer state (D3). Every allocated transaction snoops every attached cache except the requester, and the snoop type follows the request class:

| request class on the sideband | ACSNOOP driven to every peer | why |
|---|---|---|
| `ReadNotSharedDirty`, `ReadShared` | `ReadShared` (4'h1) | the requester wants a readable copy; a peer in M or E supplies it and keeps or drops its own per the caches' Table 3.0 |
| `ReadUnique` | `ReadUnique` (4'h7) | the requester wants the only copy; a peer in M or E supplies it and invalidates |
| `CleanUnique` | `CleanInvalid` (4'h9) | the requester wants its Shared copy unique; peers invalidate, and a peer holding the line dirty passes it (see below) |
| `MakeUnique` | `MakeInvalid` (4'hC) | the requester will write the whole line; peers invalidate without data |

: Table 3.1: Request class to snoop type

**Why `CleanUnique` snoops `CleanInvalid`.** This is IHI 0022's own mapping. A requester that issues a `CleanUnique` holds the line Shared, so no peer can hold it Modified -- but only at the moment it issued the request. A snoop from another transaction can invalidate that Shared copy before the upgrade is granted (the caches' killed-upgrade rule: the upgrade then completes to Invalid and its store is not performed), and the upgrade is still granted afterwards, by which time a peer may have taken the line Modified and written it. A `MakeInvalid` snoop may not carry data, so that peer's stores would be dropped; under `CleanInvalid` it passes the line dirty, onyx absorbs it, and the requester still gets its single no-data beat (onyx BUG-001, found by the core-alone rig).

A directory-lite filter stays a future elaboration parameter; at two to four caches it would save little snoop traffic for a sharer vector per line, and the family plan gives that vector a home in basalt.

## Adjudication: who supplies the line

The gather (Chapter 3.4) yields per transaction the OR of the peers' `DataTransfer` bits, and for the supplying peer its `PassDirty` bit. The decision is the PRD's D6 rule, not "any DataTransfer elides memory":

- **A peer supplied the line.** In MESI exactly one peer can hold a line Exclusive or Modified, and only those states answer a `ReadShared` or `ReadUnique` snoop with data, so at most one `DataTransfer` arrives; it is the supplier. The supplied line is buffered in the slot and replayed to the requester; the memory beats for the slot, if a read was issued, are consumed and dropped. A second `DataTransfer` for the same slot cannot happen under MESI and is a simulation-checked error.
- **No peer supplied the line.** The requester is served from memory once the gather is complete.
- **The supplier passed dirty.** The buffered line is also written to memory (the absorption, with the manager's own write ID), so memory holds the only correct copy once the supplier has invalidated or downgraded. While the absorption is pending the slot keeps its line locked and no write-back to that line reaches memory before it.

## When the memory read issues

The one open cost in the D6 rule is latency against bandwidth, and onyx carries both answers behind `DEFER_AR`:

- `DEFER_AR = 0`: the memory AR issues as soon as the last peer has accepted its AC, before any CR is back. With idle peers the CRs arrive before the first memory beat and nothing stalls; a beat arriving before its verdict holds the memory R channel for the bounded remainder of the slowest peer's service. A `DataTransfer` known before the AR was presented suppresses it; one landing on a presented AR drains the read's beats instead (a presented AR is never withdrawn).
- `DEFER_AR = 1`: the memory AR issues only once every CR is in with no supplier. Every memory read is a necessary one; every miss served from memory pays the gather first.

The write-back hazard the serial order used to prevent for free, a write-back landing in memory between the memory read and the snoop, is covered the same way in both modes: a write-back AW to a line holds while a slot on that line has an incomplete gather or a pending absorption.

The reverse order is held too: a slot's memory read does not issue while the write port holds a burst to the slot's line (from its selection until its BRESP). AXI orders nothing between a read and a write in flight, so the read could return the bytes from before the write, and the snooped cache, answering after its own write-back or WriteClean completed, reports Invalid or Shared, so nothing would replace the stale beats (onyx BUG-002, found by the core-alone rig with a WriteClean followed by a clean eviction).

Write-backs and absorptions to one line land in data-age order. A write-back first presented while a slot on its line still gathers is *old*: it was presented before the line's current owner answered, so its bytes are no newer than anything that slot can absorb (a past owner's drain that had started when a snoop passed the line on). An old write-back is not held behind the line's pending absorption, and the absorption waits while it is presented. A write-back first presented after the verdict is the new owner's and waits for the absorption. Without the first half, a stale drain held across a later slot -- the IO port's ReadOnce absorbing a newer owner's line -- landed on top of the newer bytes (onyx BUG-003, found by the pair rig's full level).

## What the decision drives

The adjudication reads only the CRRESP bits and the table; it never reads data. The CRRESP semantics it relies on are the caches' own (`l1_pkg::amber_snoop_crresp`, HAS Table 3.0 of amber), which the snoop-gather rig (TASK-001 step 1) checked against the RDS-DV snoop responder BFM cell for cell.
