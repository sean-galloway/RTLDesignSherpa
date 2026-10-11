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

# Observation: MonBus

**Stub: open until D9 closes.** This chapter records the D9 direction for observation. No architecture is recorded here until D9 closes.

## D9 direction

Per the PRD, the observation pattern follows amber D8: `*_monlite` taps on the measured paths, tallied by `monbus_tally_axil`. The observer must never stall the measured paths.

## Event classes

The following event classes are candidates for the onyx MonBus interface:

- **Coherent-transaction start.** A cache-side ACE transaction accepted by onyx, tagged by port and transaction type.
- **Snoop fanout per transaction.** Each AC driven to a peer cache, tagged by transaction and target port.
- **Gather completion.** Completion of a response gather, tagged by transaction and result (data from cache, read from memory, or no data needed).
- **Memory-read elision hit/miss.** Whether a coherent read completed without a memory-side AXI4 read.
- **Serialization stalls.** Cycles a transaction waits in the serializer/PoS, tagged by cause (same-address dependency, resource stall, etc.).
- **WB/Evict drains.** `WriteBack` and `Evict` transactions accepted from a cache-side port and forwarded toward memory.

## What the decision drives

D9 fixes which of these events are implemented, their encodings, the counter widths, and how they are exposed through `monbus_tally_axil`. It also drives the placement of `*_monlite` wrappers on the cache-side, snoop, and memory-side paths.

## Status

No observation architecture recorded. D9 must close before the MonBus interface and counter map can be fixed.
