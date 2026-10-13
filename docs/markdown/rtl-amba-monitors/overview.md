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

# rtl-amba-monitors -- Orientation

`rtl-amba/monitor/` answers "what does this module do and what are its
ports". This directory answers the question one level up: how to use the
Ocelus as a design surface. Today it holds one document, the white
paper, split into chapters under [whitepaper/](whitepaper/overview.md); a
future characterization or campaign write-up would sit beside it as its own
directory. Catalogue: [index.md](index.md).

## References

The Ocelus is an original design of this repository. The papers and standards below are related work for comparison, not sources of the design; protocol specifications define the rules the monitor observes.

- Ciordas, C., Basten, T., Rădulescu, A., Goossens, K., van Meerbergen, J. "An Event-Based Monitoring Service for Networks on Chip." *ACM Trans. Design Automation of Electronic Systems*, 10(4):702-723, Oct. 2005. DOI: [10.1145/1109118.1109126](https://doi.org/10.1145/1109118.1109126). -- related work: an event-based monitoring service built from hardware probes.
- Hopkins, A.B.T., McDonald-Maier, K.D. "Debug Support for Complex Systems On-Chip: A Review." *IEE Proc. Computers and Digital Techniques*, 153(4):197-207, 2006. DOI: [10.1049/ip-cdt:20050194](https://doi.org/10.1049/ip-cdt:20050194). -- survey of on-chip debug support.
- Indexed in `rtl/amba/references/README.md` (Monitor subsystem family; citation only)
