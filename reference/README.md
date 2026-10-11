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

# Reference Documents — Bibliographic Index

Copyrighted standards and reference documents are **not** hosted in this
repository. This file is the citation index: it records what each document
is, why the repo relies on it, and where to obtain it legitimately.

Documents that used to live here were removed 2026-10-11 (commit `books-out`).
If you need the content, follow the obtain links below — JEDEC and IEEE both
sell individual downloads, and university mirrors exist for the academic
note.

## Index

| Document | Citation | Obtain |
| --- | --- | --- |
| IEEE Std 1800-2012, *IEEE Standard for SystemVerilog* | IEEE Std 1800-2012, IEEE Computer Society, 2013. DOI 10.1109/IEEESTD.2013.6469140. | [IEEE Xplore](https://ieeexplore.ieee.org/document/6469140) |
| JESD79-2F, *DDR2 SDRAM Specification* | JEDEC Solid State Technology Association, JESD79-2F, November 2009. | [JEDEC](https://www.jedec.org/standards-documents/docs/jesd79-2f) |
| JESD209-2F, *LPDDR2 Specification* | JEDEC Solid State Technology Association, JESD209-2F, November 2009. | [JEDEC](https://www.jedec.org/standards-documents/docs/jesd209-2f) |
| Ward & Molteno, *Table of Linear Feedback Shift Registers* | Roy Ward and Tim Molteno, University of Otago, 26 October 2007. | [Otago Physics](https://www.physics.otago.ac.nz/) (search "LFSR table Ward Molteno") |

## Roles

- **IEEE 1800-2012** — the language authority for every SystemVerilog source
  and testbench in the repo. Cited in module `## References` sections and the
  authoring docs as "IEEE 1800-2017 §x.y" sections where clauses matter.
- **JESD79-2F / JESD209-2F** — timing, mode-register, and command encodings
  for the DDR2/LPDDR2 behavioral collateral under
  `projects/components/mem-ctrl-ip/` (pumice's LPDDR2 path cites JESD209-2F
  §5.12/§5.13.3 by section throughout its specs and tests).
- **Ward & Molteno** — the canonical maximum-cycle LFSR tap table behind the
  LFSR generators in `rtl/common/`.

## Related archives

The open-access paper archives (`rtl/math/references/`,
`projects/components/riscv-ip/references/papers/`) are governed by their own
README acquisition policies — only legitimately open-access copies are kept,
and each names its source. Those are papers, not books, and they stay.
