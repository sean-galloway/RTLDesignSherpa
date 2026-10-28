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

# Fabric AXI4 Master Timing

**Status:** planned contract. Both masters are the house
`axi4_master_rd/wr_monlite` wrappers amber uses; the channel contracts are
amber's (amber MAS ch03/02). What changes is how many transactions are in
flight and in what order.

## Read channel (fills)

- ARs issue in MSHR alloc order, one per outstanding miss; multiple ARs may
  be in flight (the wrapper's skid/FIFO plumbing already absorbs this).
- **Single ID:** R beats return in AR order. `jet_mshr` consumes R beats
  against its entries in the same order; the commit pipeline retires
  oldest-AR-first. (Multi-ID fills with out-of-order R are the recorded
  future step.)
- RRESP PassDirty flips the entry's install state to M (amber #106 rule).

## Write channel (drains)

- AW/W/B per WB-buffer entry, oldest-first; one drain at a time on the
  single-ID write channel.
- The WB entry's address stays snoop-visible until BRESP (Chinnakonda
  §10.10.1); BRESP both retires the entry and clears the RAW hazard window
  (a fabric read to the same line may not issue while the write is
  outstanding — enforced at lookup: a read miss matching a valid WB entry
  waits for its BRESP).

## Invariants the channel layer must keep

1. R beats land only in the entry whose AR they answer (in-order single ID
   makes this structural).
2. A drain's last W beat is accepted before its BRESP can retire the entry
   (the wrapper guarantees this).
3. Neither channel ever blocks the other (independent read/write paths —
   the ACE-style two-channel rule).
