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

**[← Back to DE10-Standard](../README.md)** | **[← FPGA Systems Index](../../index.md)**

# DE10-Standard Fabric Benchmark

Apples-to-apples comparison of two AXI fabrics on identical silicon,
endpoints, and traffic: the **bridge-generated crossbar** vs the **Intel
Platform Designer (Qsys) interconnect**. Two mirror-image flavors — injector
fills DRAM then `stream` drains it to the CRC checker; `stream` reads a PRBS
slave and writes DRAM — with obs blocks measuring bandwidth and latency on
both. Two axes: size of design and delivered performance.

- **PRD:** [PRD.md](PRD.md) — what we benchmark, how, and what ships.
- **Status:** PRD drafted; collateral-blocked (Quartus/PD IP intake pending).

## Layout (planned)

| Path | Holds |
| --- | --- |
| `quartus/` | Leg A (bridge) + Leg B (Intel PD) Quartus projects, generated as collateral arrives |
| `rtl/` | Bridge config TOML(s) for Leg A, thin wrapper tops, obs hookups |
| `scripts/` | System Console / JTAG-AXI drivers, Fitter+TimeQuest report parsers |
| `data/` | Measurement CSVs per leg per run date |
| `docs/` | Analysis document (built via the standard doc flow) |
