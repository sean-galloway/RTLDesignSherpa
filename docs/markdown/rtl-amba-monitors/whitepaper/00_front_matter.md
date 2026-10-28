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

# Ocelus: Reconstructing What Happened

**Audience:** SoC integrators deciding how to instrument a design with the
RTL Design Sherpa monitor system -- branded Ocelus. **Not** a status snapshot of what is in the
tree (that is [overview.md](../../rtl-amba/overview.md)) and not a port list (those are the
per-module pages under [monitor/](../../rtl-amba/monitor/)). This paper starts with an SoC
failure and follows the evidence: how passive monitors turn independent symptoms into an
ordered error history, how a shared microsecond time base connects events across the chip,
and how the five fabric planes deliver that history to software. It then works through a real
implementation end to end, the axes the integrator owns, and what each choice costs.

**Version:** 0.9, 2026-10-26. Ocelus and this paper remain at version 0.9
until Ocelus has been validated in silicon. Numbers are from the tree at
2026-10-12; each is cited to the page or report it comes from. The paper
recommends the lite monitor on every port, with the full monitor as the
exception requiring justification. It frames Ocelus as five planes (protocol,
error, debug, perf, output), connects them through an SoC incident and a
memory-resident error history, distinguishes event order from drain order,
and presents the proposed global usync time base.

---
