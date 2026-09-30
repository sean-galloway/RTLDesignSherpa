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
| 0.2 | 2026-09-30 | RTL Design Sherpa | Channel reset recovers every error class; the aresetn-only caveats are removed from Error Handling |
| 0.1 | 2026-09-30 | RTL Design Sherpa | Initial release: the byte-granular RAPIDS, split from the RAPIDS Beats HAS |

: Document Revision History

---

## Change Summary

### Version 0.2 (2026-09-30)

**Channel reset closes the data-path error gap**

- The per-channel reset now reaches the AXI read and write engines and both
  byte data paths. The data read and write response errors and the sink packet
  length error clear on a channel reset, and the channel takes a good
  descriptor afterwards. Error Handling no longer tells software to use
  `aresetn` for these.
- Error Handling gains the list of what a channel reset does to work in
  flight, including the sink tail discard and the unterminated source packet.
- Head-of-line blocking on a shared sink stream is unchanged and stays
  documented.

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
