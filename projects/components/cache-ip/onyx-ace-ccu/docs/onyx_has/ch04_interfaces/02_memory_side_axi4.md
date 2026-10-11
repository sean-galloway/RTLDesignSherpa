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

# Memory-Side AXI4 Master

## Port count and shape

onyx has one AXI4 master toward the house memory path. This is the recommended D1 scope (CCU only, not interconnect territory). If D1 closes on the CCU-only candidate, this master is the sole memory-side port. If D1 later moves into interconnect territory, this chapter is superseded by a multi-port or striped memory interface.

## When the memory-side port is read

D6 fixes when onyx reads memory. At 0.1 the recommended direction is full adjudication:

- Read memory only when no cache returned `DataTransfer` and no `PassDirty` moved dirty responsibility.
- If `PassDirty` passed dirty data that the requester did not absorb, write memory.

The always-read simplification is a bring-up candidate; it is not architecture at 0.1.

## AWID policy

AWID assignment is an open D5 detail. The candidate from Chinnakonda §10.10.2 is a unique-AWID freelist: for victims or coherent writes, use unique IDs so the interconnect does not impose ordering; recycle IDs as BRESPs return, preferring the oldest returned ID. Device stores, if ever supported, would use a single ID for program order. The D5 serialization choice determines whether onyx needs this freelist and how wide it must be.

## What is fixed

- One AXI4 master is the working memory-side shape (D1 recommended candidate).
- The memory read/write decision is driven by the D6 adjudication rule.
- Plain AXI4 channel semantics (AW/W/B/AR/R) apply; no snoop channels on this side.

## What is open

- D1: whether the memory side remains one AXI4 master or grows to multiple memory ports.
- D5: AWID policy and ordering requirements imposed on the interconnect.
- D6: whether the full adjudication rule or the bring-up always-read rule is implemented.
