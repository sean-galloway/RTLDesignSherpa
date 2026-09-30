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

A profile is a resolved parameter set. These four come from the standards
and papers in `References/`; the first consumer picks one or defines its own.

| Profile | m | t | n / k | `PRIM_POLY` | `FIRST_ROOT` | Scrambler | Source | Notes |
|---|---|---|---|---|---|---|---|---|
| Reference (DVB outer code, full length) | 8 | 8 | 255 / 239 | x^8+x^4+x^3+x^2+1 | 0 | x^15+x^14+1, seed 100101010000000, before the encoder | EN 300 429 / 744 sec. 4.3 (verified) | the profile every count in this document quotes |
| DVB shortened | 8 | 8 | 204 / 188 | same | 0 | same | same | 51 leading zero symbols dropped; MPEG-2 transport packets |
| CCSDS telemetry | 8 | 16 (or 8) | 255 / 223 (239) | x^8+x^7+x^2+x+1 (CCSDS field) | 112 | x^17+x^14+1, seed 11000111000111000, after the encoder (legacy: x^8+x^7+x^5+x^3+1, all ones) | CCSDS 131.0-B-5 sec. 4 and 10 | dual-basis symbol representation; interleave depth 1-8 outside the core |
| Ethernet RS-FEC | 10 | 15 (KP4) / 7 (KR4) | 544 / 514, 528 / 514 | x^10+x^3+1 | 0 | 802.3 scrambler is separate | IEEE 802.3 cl. 91 / 108 (cited) | S > 1 required; m = 10 tables |
| RAID erasure | 8 or 16 | any | any n <= 2^m-1 | any | -- | none | Plank 1997 + 2003 | erasure-only; encoder + erasure decoder, no Chien search |

: Table 6.4: Candidate profiles

The DVB row is the one verified line by line against the standard's text
(2026-09-29); CCSDS is read from the stored Blue Book; the 802.3 and RAID
rows are from the cited documents and should be confirmed against them when
chosen.
