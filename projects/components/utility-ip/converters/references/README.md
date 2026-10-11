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

# Reference Archive for `projects/components/utility-ip/converters`

Canonical references for the protocol and data-width conversion modules in the Converters component. This directory is the central references store for the area; per-design citations live in the relevant `docs/converter_mas/` chapters.

## Acquisition Policy

No local PDFs are archived here. The documents below are ARM proprietary specifications; only ARM documentation links and full bibliographic citations are recorded.

## Reference Index

| Document | Citation | ARM Link | Role in this component |
| --- | --- | --- | --- |
| AMBA 3 AXI Protocol Specification | ARM, *AMBA 3 AXI Protocol Specification*, ARM IHI 0022. | [ARM documentation](https://developer.arm.com/documentation/ihi0022/latest) | Defines AXI3 protocol semantics used by `axi4_to_axi3` and `axi3_to_axi4`: 4-bit `AxLEN` (max 16 beats), 2-bit `AxLOCK`, write-data `WID`, and the absence of `QoS`/`REGION`. |
| AMBA AXI and ACE Protocol Specification | ARM, *AMBA AXI and ACE Protocol Specification*, ARM IHI 0022E. | [ARM documentation](https://documentation-service.arm.com/static/5f915b62f86e16515cdc3b1c) | Defines AXI4 protocol semantics used by `axi4_to_axi3` and `axi3_to_axi4`: 8-bit `AxLEN` (max 256 beats), 1-bit `AxLOCK`, no `WID`, and the `QoS`/`REGION` qualifiers. |

## Lint Posture

The converter area is linted under the repo's `-Wno-fatal` Verilator posture. Several `UNUSEDSIGNAL` warnings are expected and benign: `QoS`/`REGION` are dropped on the AXI4-to-AXI3 boundary, unused address/length fields remain in the `active_req`/`active_aw` descriptor structs for API symmetry, and the purely combinational `axi3_to_axi4_rd` does not use `aclk`/`aresetn`. These warnings do not indicate functional defects and are accepted rather than worked around with artificial tie-offs.

---

**Maintained By:** RTL Design Sherpa Project
