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

# Serializer and Point of Serialization

**Stub: open until D5 closes.** This chapter records the invariant landscape for same-address serialization and the candidates for implementing it. No architecture is recorded here until D5 closes.

## Candidates

| Decision | Candidates | What it drives |
|---|---|---|
| D5 Same-address serialization | Per-address scoreboard allowing interleaving of different addresses (recommended; the interesting manager) vs full in-order single outstanding (bring-up mode) | the serializer structure, the deadlock/liveness proof, jet J4 interactions |

## Invariant landscape

Regardless of which D5 candidate is chosen, the serializer must guarantee:

- **No two same-address coherent transactions proceed incompatibly.** Two reads to the same address may interleave; a read and a write that invalidates must be ordered; two writes to the same address must be ordered.
- **Transactions to different addresses may proceed in any order.** This is the concurrency the per-address scoreboard is meant to preserve.
- **Fairness under contention.** Fixed-priority arbitration must not starve a master; timeout counters or round-robin escalation are required (Chinnakonda §8.3).
- **No deadlock under fair arbitration at N ∈ {2, 3, 4}.** This is success criterion 3.

## Named proof obligations

The PRD success criterion 3 names three liveness scenarios from Chinnakonda that become this chapter's eventual exit criteria:

1. **Absence of CU livelock at the PoS.** When one master's `CleanUnique` wins and another master's competing `CleanUnique` is dependent on it, the system must not enter a livelock where ownership is repeatedly won and lost before any store completes.
2. **No WLU/WB-style deadlock in the fanout/gather path.** Snoop responses must make forward progress even when the system interconnect buffers are full of `WriteLineUnique`/`WriteBack` traffic.
3. **Fairness at N ∈ {2, 3, 4}.** No master may be starved under sustained contention from the other masters.

## Background material

Chinnakonda, *Designing a Multiprocessor Cache Subsystem*, §7.5 describes two ways to maintain order on the bus: use the same `ARID`/`AWID` so the interconnect orders the transactions, or hold the second transaction until the first completes. §10.7 describes the banked PoS with per-address linked lists: older completes first, different addresses any order. §10.9.1 notes that device accesses are routed to a dedicated bank for program order. §10.8 gives outstanding-access sizing math (≈40 read + 40 write transactions for 200-cycle DRAM latency on a 1 GHz 16-byte bus). §10.9 describes the CU livelock scenario where an external snoop repeatedly takes away ownership before the winning transaction can complete.

## Status

No architecture recorded. D5 must choose the same-address serialization mechanism before the PoS can be drawn and the named proof obligations can be targeted.
