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

# Ocelus as a Design Surface

**Audience:** SoC integrators deciding how to instrument a design with the
RTL Design Sherpa monitor system -- branded Ocelus. **Not** a status snapshot of what is in the
tree (that is [overview.md](../../rtl-amba/overview.md)) and not a port list (those are the
per-module pages under [monitor/](../../rtl-amba/monitor/)). This paper sits one level up:
here is the spine, here are the six axes the integrator owns, and here is
what each choice costs.

**Version:** 1.4, 2026-10-20. Numbers are from the tree at 2026-10-12;
each is cited to the page or report it comes from. Revision 1.1 makes the
recommendation explicit: the lite monitor is the realistic choice on every
port, and the full monitor is the exception you justify. Revision 1.2 (2026-10-12) brands the monitor system Ocelus and adds chapter 12, the standing comparison against Nexus (IEEE-ISTO 5001). Revision 1.3 (2026-10-20) redraws the block diagrams to the repo element key; no numbers or text changed. Revision 1.4 (2026-10-20) renames the PDF the Ocelus White Paper and starts every numbered section on its own page.

---
