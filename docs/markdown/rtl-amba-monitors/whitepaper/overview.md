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

# Monitor System White Paper -- Orientation

**What it is:** the monitor system seen from one level up -- for an SoC
integrator deciding how to instrument a design, not for someone looking up a
port. It names the spine (ports, arbiter tree, group, two drains), the six
axes the integrator owns (identity allocation, insertion points, timestamp
policy, drain path, packet filtering, aggregation topology), what each choice
costs in LUTs and flops from the characterization sweep, and how to validate
a tweak in simulation. Revision 1.1's recommendation: the lite monitor on
every port; the full monitor is the exception you justify.

**Read it:** [index.md](index.md) is the chapter list in order; the branded
PDF is `docs/pdfs/RTL_AMBA_Monitor_Whitepaper.pdf`. Start with chapter 2,
"Which monitor", if you only have five minutes.

**What it is not:** a status snapshot of the tree (that is
[rtl-amba/overview.md](../../rtl-amba/overview.md)) or a port reference (the
[monitor pages of the rtl-amba index](../../rtl-amba/index.md)). The numbers it
quotes come from
[monitor_characterization.md](../../rtl-amba/monitor/monitor_characterization.md)
and are dated in the front matter.
