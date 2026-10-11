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

# Key Features

## N cache-side ACE ports (2–4, D11)

onyx accepts coherent transactions from N attached caches. D11 is open, but the recommended direction is an elaboration parameter supporting 2–4 masters, matching the `culsans` range. The internal resources (fanout width, gather buffering, PoS banks, outstanding-access capacity) must size with N.

## D2 coherent-transaction subset

The front-end decoder handles the recommended research subset: `ReadShared`, `ReadUnique`, `CleanUnique`, `MakeUnique`, `WriteBack`, and `Evict`. The decoder shape depends on whether D2 closes on this subset or grows; the architecture chapter is a stub until D2 closes.

## Snoop fanout: broadcast vs directory-lite (D3)

The v1 candidate is broadcast to all attached caches (the `culsans` shape). A directory-lite elaboration parameter is the deferred candidate: copy-of-L1-tags, L1ID-vector in tag, or a separate snoop filter sized ≈1.5× combined L1. The false-positive-snoop corner (a line thought to be in one cache has been victimized) must be handled regardless of the D3 choice.

## Response gather (D4)

Candidates: a fixed response window in which all caches respond (presumed miss after a proven bound), or tagged outstanding snoop IDs with per-transaction completion. Snoops carry no IDs and must be responded to in issue order; the gather mechanism must respect that rule.

## Same-address serialization (D5)

Candidates: a per-address scoreboard allowing interleaving of different addresses (the interesting manager), or full in-order single outstanding (a bring-up mode). The PoS is where same-address transactions are ordered before they proceed incompatibly.

## Memory-read elision (D6)

Candidates: full adjudication — read memory only when no cache supplied data and no `PassDirty` moved dirty responsibility — or an always-read simplification for bring-up. The safe rule is not "any `DataTransfer` elides memory"; Shared copies may still require the DRAM read.

## MonBus observation (D9)

The D9 direction is `*_monlite` taps for: coherent-transaction start, snoop fanout per transaction, response-gather completion, memory-read elision hit/miss, serialization stalls, and `WriteBack`/`Evict` drains. Tallies live in `monbus_tally_axil` like every other component.

## Design-invariant landscape

Seven proposed liveness rules from the PRD guide the architecture even before the rows close: snoop forward progress; snoops ignore `WriteLineUnique`/`WriteUnique`; snoop responses never depend on `WriteUnique`/`WriteLineUnique` completion; CD never blocks on `WDATA`; multi-copy-atomic stores; CR/CD/CDLAST ordering; and no snoop to the requesting master. These are restated in the snoop fanout contract in [Chapter 4.3](../ch04_interfaces/03_snoop_fanout.md).
