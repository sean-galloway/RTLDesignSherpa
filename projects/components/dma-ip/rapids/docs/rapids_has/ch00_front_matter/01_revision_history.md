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

# Revision History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 0.1 | 2026-09-30 | RTL Design Sherpa | Initial release: the byte-granular RAPIDS, split from the RAPIDS Beats HAS |

: Document Revision History

---

## Change Summary

### Version 0.1 (2026-09-30)

**Initial Release**

- The byte-granular RAPIDS (rapids TASK-019) is the product design. The
  RAPIDS Beats design was its stepping stone and keeps its own book, the
  RAPIDS Beats HAS.
- New chapters where the byte design differs: Product Overview, Key Features,
  System Context, Block Diagram, Data Flow, AXI4 Master Interface, AXIS
  Interface, both use cases, Descriptor Format, Error Handling, Throughput and
  Resource Estimates.
- Chapters unchanged from RAPIDS Beats are linked from the RAPIDS Beats HAS
  rather than copied, so a correction there reaches both books.
- Permanent limitation recorded: TYPE=EXT (row and column striding)
  descriptors stay beat-aligned. Linear descriptors may start at any byte.
