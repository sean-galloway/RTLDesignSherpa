<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/seang-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/seang-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/seang-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/seang-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/seang-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# basalt — Shared L2 (direction)

Named for columnar basalt — the layered foundation everything above rests
on. The cache-ip family's capstone direction: a shared, banked last-level
cache inserting into onyx's memory side, below the coherency point.

**Status: pencil only.** The unit breakdown and open decision rows live in
[PRD.md](PRD.md) (v0.1, 2026-10-11); every row is OPEN and no RTL is gated
until onyx v1 exists. See the family [README](../README.md) for the vision
and the [onyx future-hooks chapter](../onyx-ace-ccu/docs/onyx_has/ch06_integration/03_future_hooks.md)
for how basalt attaches without touching the onyx contract.
