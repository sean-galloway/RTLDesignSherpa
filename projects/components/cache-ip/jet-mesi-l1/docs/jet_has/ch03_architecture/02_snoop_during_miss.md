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

# Snoop During Miss

**Stub: open until J4 and J5 decide.** This chapter records the decision landscape for ordering guarantees and snoop handling while one or more misses are outstanding. No architecture is recorded here until J4 and J5 close.

## The J4 ordering problem

When the cache has outstanding misses, it must still answer three questions:

1. Does a snoop to a pending line see the post-fill state, respond from the fill data, or respond that the line is not present?
2. Are CPU-side responses returned in issue order, or out-of-order with ID tags?
3. What happens when a snoop arrives while a victim write-back for the same line is in flight?

The jet PRD calls out the snoop-during-miss requirement explicitly: a probe against a pending line must see the post-fill state or stall cleanly.

## The J5 eviction problem

A dirty victim displaced by an outstanding fill must write back without deadlocking against the fill. The victim buffer depth (0 = block like amber, 1–4 = decouple) and the ordering between fill return and victim drain are J5.

## Background material

Chinnakonda, *Designing a Multiprocessor Cache Subsystem*:

- §7.8 (file 7.7) "Forward Progress Guarantees" shows that a snoop matching a pending miss must still be responded to; holding it until the fill completes can deadlock the system. The response may indicate "not present" if data has not yet arrived, or forward from fill buffers if data has arrived.
- §8.2 "Deadlocks" lists the victim-buffer deadlock: if a fill cannot proceed because no victim buffer is available, and a snoop matching the fill buffer needs forwarding, the architecture must either forward from the fill buffer or reserve a victim buffer per fill.
- §10.8 (file 10.6) "Forward Progress of Snoop responses" discusses "snarfing" data from victim/write buffers so that a snoop response can make forward progress even when the normal write-back path is blocked.

## Status

No architecture recorded. J4 must decide the ordering and snoop-during-miss policy; J5 must decide the victim buffer depth and the fill/victim ordering. The architecture here will be written after both close.
