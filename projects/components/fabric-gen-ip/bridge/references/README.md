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

# Reference Archive for `projects/components/fabric-gen-ip/bridge`

Canonical references for the Bridge AXI4 full crossbar generator. This directory is the central references store for the area; per-design citations live in the relevant `docs/bridge_has/` chapters and in `PRD.md`.

## Acquisition Policy

No local PDFs are archived here. The documents below are commercial books; only bibliographic citations, ISBNs, and public catalogue links are recorded.

## Reference Index

| Document | Citation | Link | Role in this component |
| --- | --- | --- | --- |
| Dally & Towles, *Principles and Practices of Interconnection Networks* | Dally & Towles, *Principles and Practices of Interconnection Networks*, Morgan Kaufmann, 2004. ISBN 978-0122007514. | [WorldCat](https://search.worldcat.org/search?q=978-0122007514) | Topology/traffic (ch3), routing (ch7-10), flow control & buffering (ch11-12), router architecture (ch15-16), arbitration (ch17-18), buses (ch21). |
| Duato/Yalamanchili/Lionel, *Interconnection Networks* | Duato, Yalamanchili, & Lionel, *Interconnection Networks: An Engineering Approach*, Morgan Kaufmann, 2003. ISBN 978-1558608528. | [WorldCat](https://search.worldcat.org/search?q=978-1558608528) | Deadlock freedom (ch3), routing theory (ch4), performance evaluation methodology (ch9). |
| Jantsch & Tenhunen (eds.), *Networks on Chip* | Jantsch & Tenhunen (eds.), *Networks on Chip*, Kluwer, 2003. ISBN 978-1402073392. | [WorldCat](https://search.worldcat.org/search?q=978-1402073392) | RNI/adapter concept (ch5 §3.4.2), QoS channel contracts (ch12), priority/aging arbitration practice (ch13). |
| Maaref, *Architecting and Building High-Speed SoCs* | Maaref, *Architecting and Building High-Speed SoCs*, Packt, 2022. ISBN 978-1801810999. | [WorldCat](https://search.worldcat.org/search?q=978-1801810999) | AMBA suite overview, OCP, DMA/coherency context (ch3). |
| Eschemann, *The FPGA Programming Handbook* | Bruno & Eschemann, *The FPGA Programming Handbook*, Packt, 2023. ISBN 978-1805125594. | [WorldCat](https://search.worldcat.org/search?q=978-1805125594) | Educational secondary source for AXI channel explanations (ch8). |
| Roy, *Advanced Digital System Design* | Roy, *Advanced Digital System Design*, Springer, 2023. ISBN 978-3-031-41084-0. | [WorldCat](https://search.worldcat.org/search?q=978-3-031-41084-0) | AXI channel/feature descriptions (ch18 §18.2.2-18.2.3). |
| ARM, *AMBA AXI and ACE Protocol Specification* | ARM, *AMBA AXI and ACE Protocol Specification*, ARM IHI 0022E. | [ARM documentation](https://developer.arm.com/documentation/ihi0022/latest) | The AXI4 protocol authority itself. |

---

**Maintained By:** RTL Design Sherpa Project
