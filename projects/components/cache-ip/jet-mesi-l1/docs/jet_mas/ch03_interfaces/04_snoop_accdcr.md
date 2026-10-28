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

# Snoop AC/CD/CR Timing and Ordering

**Status:** planned contract. The wire contract is amber's (amber MAS
ch03/04, onyx D7): AC in, CR/CD out, CD before CR, no-ID in-order per
channel. This chapter records the concurrency deltas.

## AC acceptance

`snoop_ready` deasserts only while the snoop service occupies port B or
during the bounded anti-livelock hold-off window (ch02/01). It never waits
on MSHR or WB occupancy, fill state, or drain state.

## Response production

The match order WB → MSHR → arrays (ch02/05) decides the CRRESP and the CD
source combinationally at grant; the data phase then streams from the
selected source. CRRESP is computed from:

- WB match: the buffered victim's state (M row of the Table 3.0 decode);
- MSHR match: the entry's post-fill state (with PF_GUARD gating CD on
  `beats_rcvd`);
- array hit: the line's state, amber's `l1_snoop_kmap`-equivalent decode.

## Concurrency rules

1. A snoop during another snoop's CD phase queues at AC (single responder,
   inherited).
2. A snoop during a fill commit on the same line answers at the post-commit
   state (PoS ordering, ch02/05 rule 5).
3. A snoop during a WB drain of the same line snarfs (the drain continues;
   the fabric took the data from the buffer).
