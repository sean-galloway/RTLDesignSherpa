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
| `CleanUnique`, `MakeUnique` | `MakeInvalid` (4'hC) | the requester holds the line and wants it unique; peers invalidate without data |

: Table 3.1: Request class to snoop type

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

## What the decision drives

The adjudication reads only the CRRESP bits and the table; it never reads data. The CRRESP semantics it relies on are the caches' own (`l1_pkg::amber_snoop_crresp`, HAS Table 3.0 of amber), which the snoop-gather rig (TASK-001 step 1) checked against the RDS-DV snoop responder BFM cell for cell.
