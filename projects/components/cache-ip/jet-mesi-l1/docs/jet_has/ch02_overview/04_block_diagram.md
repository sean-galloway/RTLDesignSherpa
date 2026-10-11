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

# Block Diagram

This chapter is a stub at 0.1. The block diagram cannot be drawn until J1 (MSHR organization) and J5 (eviction/victim buffering) close, because those decisions change the shape, depth, and connection of the buffers between the cache core and the fabric masters.

Expected shape, described in prose:

- The `amber_core` block is reused unchanged: CPU-side GAXI slave, tag/data arrays, replacement engine, and snoop responder.
- Between the core and the fabric masters sits the **MSHR file**: the table of outstanding misses, the merge logic, and the hazard logic that implements J2.
- The **victim buffer** is deeper than amber's: it must hold dirty victims displaced by fills that have not yet returned, per J5.
- The **fabric master stack** (AXI4 for the pair rig, ACE for the onyx rig) sees multiple outstanding transactions instead of one.
- The **ACE-shaped snoop port** (AC/CD/CR) is inherited from amber, but the snoop responder must now inspect the MSHR file and victim buffers, per J4.
- The **monlite observer** is inherited from amber and is extended to emit the J7 measurement classes.

Once J1 and J5 decide, this chapter will be replaced by a figure showing the exact modules, buffer depths, and datapaths.
