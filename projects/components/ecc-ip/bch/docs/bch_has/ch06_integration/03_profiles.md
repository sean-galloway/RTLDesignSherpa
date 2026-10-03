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

# Candidate Profiles

A profile is a resolved parameter set. These three come from the standards
and papers in `References/`; the first consumer picks one or defines its own.

| Profile | m | t | n / k | `PRIM_POLY` | `FIRST_ROOT` | Source | Notes |
|---|---|---|---|---|---|---|---|
| CCSDS telecommand | 6 | 1 | 63 / 56 | see figure 3-2 of CCSDS 231.0-B-4 section 3 | 112 in the CCSDS field representation | CCSDS 231.0-B-4 section 3 (stored in `References/`) | the classic command link: small t, but a fully worked generator in a free standard -- the natural first RTL profile |
| NAND flash ECC | 13-16 | 12-72 class | page-plus-spare geometry, shortened by construction | per controller vendor | per controller vendor | Cai et al. 2017 (stored) for the error landscape; Nabipour & Javidan 2023 (stored) for (m,t) selection | the profile the memory-controller consumer is expected to name; n runs to thousands of bits, so D6 and the Chien length dominate |
| DVB-T2 / S2 / C2 | m per standard | per standard | per standard | per standard | per standard | ETSI EN 302 755 / 302 307 / 302 769 (linked in `References/`) | BCH cleans the LDPC error floor; interesting only if a broadcast consumer ever appears |

: Table 6.4: Candidate profiles

The CCSDS row is the natural first RTL profile because the generator is
explicit in the stored standard. The NAND flash row is the expected consumer
but its exact (m, t, n) come from the controller vendor. The DVB row is
linked, not stored, because ETSI restricts redistribution.
