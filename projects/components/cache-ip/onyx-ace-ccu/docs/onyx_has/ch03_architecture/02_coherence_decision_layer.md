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

**Stub: open until D3 and D6 close.** This chapter records the decision landscape for the coherence decision layer: snoop fanout policy and memory-read elision. No architecture is recorded here until D3 and D6 close.

## Candidates

| Decision | Candidates | What it drives |
|---|---|---|
| D3 Snoop fanout | Broadcast to all attached caches (`culsans` shape, recommended v1) vs directory-lite snoop filter as an elaboration parameter vs snoop filter mandatory | fanout logic, gate count, coherence-traffic measurements, whether sharer state is kept |
| D6 Memory-read elision | Full adjudication — read memory only when no cache supplied data and no `PassDirty` (recommended) vs always-read simplification for bring-up | memory traffic, the measurable win onyx exists to quantify |

## What the decisions drive

D3 fixes whether onyx maintains any sharer state. Broadcast is simplest but sends snoops to caches that cannot hold the line; a directory-lite filter reduces snoop traffic at the cost of tracking state. The D3 choice also interacts with D6: if a directory-lite filter is added later, the elision rule must still be correct when the filter has false positives or when multiple Shared copies exist.

D6 fixes the memory-read decision. The CRRESP bits (`DataTransfer`, `PassDirty`, `IsShared`) are the inputs:

- If any cache returns `DataTransfer`, the requester can be supplied from a cache.
- If no cache returns `DataTransfer` and no `PassDirty` moved dirty responsibility, memory must be read.
- If `PassDirty` passed dirty data that the requester did not absorb, memory must be written.

The safe rule is **not** "any `DataTransfer` elides memory." When multiple Shared copies exist, many real systems still read DRAM for Shared copies and accept data only from an O-state holder. A single designated forwarder (MOESIF Forward state) is one way to make elision safe, but that is not in the recommended D2 subset.

## Background material

Chinnakonda, *Designing a Multiprocessor Cache Subsystem*, §10.3–10.5 describe inclusive-directory options: copy-of-L1-tags, L1ID sharer vector in tag, or a separate snoop filter sized ≈1.5× combined L1. §10.6.2 notes the false-positive-snoop corner: when multiple shared responders exist, the manager must pick one, and many systems read DRAM for Shared copies. §10.5–10.6 refine adjudication: with multiple `DataTransfer` responders, the manager must pick one; MOESIF Forward state is one way to designate a single forwarder.

## Status

No architecture recorded. D3 must choose broadcast vs directory-lite, and D6 must choose the elision rule, before the coherence decision layer can be drawn.
