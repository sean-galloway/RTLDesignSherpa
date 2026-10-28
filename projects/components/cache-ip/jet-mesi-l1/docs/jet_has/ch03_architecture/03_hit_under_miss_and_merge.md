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

# Hit-Under-Miss and Miss Merging

**Stub at 0.1–0.2; J2 and J3 CLOSED 2026-10-28.** This chapter records the
hit-under-miss and merging decisions and what they drive.

## J2: hit-under-miss scope (DECIDED 2026-10-28, Sean)

**Reads AND writes to any resident line proceed while fills are in
flight.**

- A pending-fill line cannot be "hit": its tag installs only at fill
  commit, so an access to it is the J3 merge case, not a hit.
- A doomed victim stays hittable until the fill's commit tag-write lands:
  its array copy is intact and its MESI state still valid until then.
- The data array (inherited `l1_data_array`: two read ports, one write
  port) serves hits on port A and snoop/bypass reads on port B; the single
  write port arbitrates **fill beats over CPU write hits** — fills must
  retire for the J5/J6 liveness argument, write hits can wait a cycle.

## J3: miss merging policy (DECIDED 2026-10-28, Sean)

**Exact-line aliases merge; no in-flight class escalation.**

- Same class joins: a second read miss onto an outstanding read fill shares
  the fill and responds at commit; a second write miss onto an outstanding
  write fill merges its data at commit (amber's D-4 write-merge semantics).
- Cross-class waits: a write miss behind an outstanding read fill stalls
  until that fill commits, then issues its own upgrade (CLEAN_UNIQUE) — the
  outstanding entry's class is never mutated (no RNSD→RU escalation). A
  read behind an outstanding write fill simply waits and hits the committed
  M line.
- Merging never issues duplicate memory traffic for one line; the merge
  match is one exact-address comparator per MSHR entry (J1).

## What these decisions drive

- the hit/pending hazard exclusion (same comparators as the merge match);
- the W-port arbiter (fill beats > write hits);
- the per-entry merged-requester list (who responds when the fill commits);
- the cross-class stall rule in the allocation path (J6 strict stall).
