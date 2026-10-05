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


# Utility IP

Reusable building blocks that serve every other family and belong to none of
them. Created 2026-09-29 (Sean) when the component tree was regrouped into
`*-ip` families; both members moved with history and keep their own README,
CLAUDE.md, rtl/, dv/ and task lanes (`vault/Tasks/projects/components/utility-ip/<ip>/`).
Python imports use `projects.components.utility_ip.<ip>...` (the alias in
`projects/components/__init__.py` maps the underscore name onto this directory).

| Directory | What | Status |
|---|---|---|
| [`converters/`](converters/README.md) | AXI data-width converters (upsize / dnsize / wide-align) and protocol converters (AXI4 to APB4/APB5/AXIL/WB4 and back, PeakRDL adapter) | production; MAS under `converters/docs/converter_mas/` |
| [`misc/`](misc/README.md) | ROM/RAM wrappers, interface observers, DMA address generator, monbus tallies, the shared bit/symbol error injector, Verilator stubs | production |
