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

# Monitor Package Reference

Documentation for the four SystemVerilog packages that define the monbus
packet format and per-protocol event-code enums.

| Doc | Covers | RTL |
|-----|--------|-----|
| [`monitor_package_spec.md`](./monitor_package_spec.md) | Universal types: 128-bit packet structure, 64-bit side-band timestamp, protocol enum, packet-type enum, helper functions. Start here. | `rtl/amba/includes/ocelus_common_pkg.sv` |
| [`monitor_amba4_pkg.md`](./monitor_amba4_pkg.md)       | AMBA4 event codes for AXI4, APB4, and AXI4-Stream (19 enums). | `rtl/amba/includes/ocelus_amba4_pkg.sv` |
| [`monitor_amba5_pkg.md`](./monitor_amba5_pkg.md)       | AMBA5 extensions: AXI5 atomic / trace, APB5 wakeup / parity / user, AXIS5 wakeup / parity / CRC (8 enums). | `rtl/amba/includes/ocelus_amba5_pkg.sv` |
| [`monitor_arbiter_pkg.md`](./monitor_arbiter_pkg.md)   | ARB and CORE event codes for arbiter monitors and custom subsystems (12 enums + unified union). | `rtl/amba/includes/ocelus_arbiter_pkg.sv` |
| [`monitor_wb4_pkg.md`](./monitor_wb4_pkg.md)           | Wishbone B4 event codes for `wb4_monitor` (5 enums). NOT re-exported by `ocelus_pkg`. | `rtl/amba/includes/ocelus_wb4_pkg.sv` |
| [`monitor_cxs_pkg.md`](./monitor_cxs_pkg.md)           | CXS event codes for `cxs_monitor_lite` (6 enums, `PROTOCOL_CXS`). NOT re-exported by `ocelus_pkg`. | `rtl/amba/includes/ocelus_cxs_pkg.sv` |

The aggregating wrapper `ocelus_pkg` re-exports every type from the four
split packages, so legacy code that imports `ocelus_pkg::*;` continues
to compile. New code should import the specific package it needs — see
the [Backward Compatibility](./monitor_package_spec.md#backward-compatibility)
section of the spec.

## References

- Arm. *AMBA AXI and ACE Protocol Specification*, ARM IHI 0022, Issue H, 2020. [developer.arm.com/documentation/ihi0022/h](https://developer.arm.com/documentation/ihi0022/h), sec. A3.4.5 "Read and write response structure", A7.2 "Exclusive accesses", and Part E (AMBA 5 features).
- Arm. *AMBA APB Protocol Specification*, ARM IHI 0024, Issue E, 2023. [developer.arm.com/documentation/ihi0024/e](https://developer.arm.com/documentation/ihi0024/e), sec. 3.4 "Error response", 3.7 "Wake-up signaling", ch. 5 (parity).
- Arm. *AMBA AXI-Stream Protocol Specification*, ARM IHI 0051, Issue B, 2021. [developer.arm.com/documentation/ihi0051/b](https://developer.arm.com/documentation/ihi0051/b), sec. 2.3 "Wake-up signaling", 2.6 "Packet boundaries", ch. 5 (parity).
- OpenCores. *Wishbone B4: WISHBONE System-on-Chip (SoC) Interconnection Architecture for Portable IP Cores*, 2010, sec. 3.1.5 "Use of [ACK_O], [ERR_O] and [RTY_O]".
- Indexed in `rtl/amba/references/README.md`

---

## Navigation

- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
