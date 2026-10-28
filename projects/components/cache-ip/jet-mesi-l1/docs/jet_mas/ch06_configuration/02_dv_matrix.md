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

# DV Matrix Dimensions

**Status:** planned contract. The DV grid multiplies amber's matrix by the
two jet knobs:

| Axis | Values |
|---|---|
| Level | GATE / FUNC / FULL |
| Geometry | tiny (16/2) / default (128/4) |
| `MSHR_COUNT` | 2 / 4 / 8 / 16 |
| `VICTIM_DEPTH` | 1 / 2 / 4 |
| Replacement policy | LRU / FIFO / RANDOM (cache_sim parity); tree-PLRU by RTL self-check |
| Rig | pair (`jet_top`) / onyx (`jet_ace_top`, when onyx lands) |

FULL at the sweep corners is the sign-off grid; the interior is sampled
(seeds pinned per node by the repo-root conftest, as everywhere else).

## What FULL must contain (beyond amber's soak)

- Miss streams that saturate the MSHR file (occupancy at `MSHR_COUNT` for
  sustained windows) with concurrent hits and snoops.
- Merge storms: repeated aliases to outstanding lines.
- Set-oversubscription pressure: miss bursts into one set.
- The composed corner: MSHR-full + WB-full + snoop soak, dynamically —
  complementing the formal proof (ch05/01) at the tiny geometry.
- The amber FULL suite re-run on jet unchanged (the inheritance claim:
  amber's DV content is jet's subset).
