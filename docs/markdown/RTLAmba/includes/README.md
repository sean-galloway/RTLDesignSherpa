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
| [`monitor_package_spec.md`](./monitor_package_spec.md) | Universal types: 128-bit packet structure, 64-bit side-band timestamp, protocol enum, packet-type enum, helper functions. Start here. | `rtl/amba/includes/monitor_common_pkg.sv` |
| [`monitor_amba4_pkg.md`](./monitor_amba4_pkg.md)       | AMBA4 event codes for AXI4, APB4, and AXI4-Stream (19 enums). | `rtl/amba/includes/monitor_amba4_pkg.sv` |
| [`monitor_amba5_pkg.md`](./monitor_amba5_pkg.md)       | AMBA5 extensions: AXI5 atomic / trace, APB5 wakeup / parity / user, AXIS5 wakeup / parity / CRC (8 enums). | `rtl/amba/includes/monitor_amba5_pkg.sv` |
| [`monitor_arbiter_pkg.md`](./monitor_arbiter_pkg.md)   | ARB and CORE event codes for arbiter monitors and custom subsystems (12 enums + unified union). | `rtl/amba/includes/monitor_arbiter_pkg.sv` |

The aggregating wrapper `monitor_pkg` re-exports every type from the four
split packages, so legacy code that imports `monitor_pkg::*;` continues
to compile. New code should import the specific package it needs — see
the [Backward Compatibility](./monitor_package_spec.md#backward-compatibility)
section of the spec.

---

## Navigation

- **[← Back to RTLAmba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
