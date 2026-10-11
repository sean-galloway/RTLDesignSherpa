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

# FPGA Systems

Board-targeted integrations of the RTL Design Sherpa component IPs: each
board area groups the IPs built for that board under
`<board>/<ip-area>/<ip>`.

| Board area | Contents |
| --- | --- |
| [Genesys2](Genesys2/) | dma-ip (stream), ecc-ip (bch, reed-solomon), mem-ctrl-ip |
| [NexysA7](NexysA7/) | Scaled-down/demo variants of the above |
| [DE10-Standard](DE10-Standard/) | fabric-benchmark — bridge vs Intel PD fabric comparison |
| [boards/](boards/) | Board constraint collections |
| [docs/](docs/) | FPGA systems MAS |
