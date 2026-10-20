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

# rtl-amba-monitors

Long-form documents about the AMBA Ocelus that are not per-module
reference pages (those stay in the [monitor pages of the rtl-amba index](../rtl-amba/index.md)
under `rtl-amba/`). Each document is a directory with an `index.md` (the
chapter list, which is also the PDF build order) and an `overview.md`.

| Document | Chapters | PDF |
|---|---|---|
| [The Ocelus as a Design Surface](whitepaper/index.md) -- the integrator's white paper | [whitepaper/](whitepaper/overview.md) | `docs/pdfs/Ocelus_White_Paper.pdf` (`generate_rtl_pdfs.sh monitor-wp`) |

## References

The Ocelus is an original design of this repository. The papers and standards below are related work for comparison, not sources of the design; protocol specifications define the rules the monitor observes.

- Hopkins, A.B.T., McDonald-Maier, K.D. "Debug Support for Complex Systems On-Chip: A Review." *IEE Proc. Computers and Digital Techniques*, 153(4):197-207, 2006. DOI: [10.1049/ip-cdt:20050194](https://doi.org/10.1049/ip-cdt:20050194). -- survey of on-chip debug support.
- Vermeulen, B. "Functional Debug Techniques for Embedded Systems." *IEEE Design & Test of Computers*, 25(3):208-215, May/June 2008. DOI: [10.1109/MDT.2008.66](https://doi.org/10.1109/MDT.2008.66). -- survey of functional silicon debug.
- Indexed in `rtl/amba/references/README.md` (Monitor subsystem family; citation only)
