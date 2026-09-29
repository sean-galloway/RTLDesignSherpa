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


# NoC IP

Network-on-chip components. Created 2026-09-29 (Sean) when the component tree
was regrouped into `*-ip` families.

| Directory | What | Status |
|---|---|---|
| [`delta/`](delta/) | the Delta interconnect (one module, a spec that was never written) | **retired 2026-09-27**, kept as it was; the tracker records why |

A live NoC component would arrive here the way `ecc-ip/reed-solomon` did:
README, CLAUDE.md and a PRD with its decision table first, RTL when a consumer
fixes the decisions.
