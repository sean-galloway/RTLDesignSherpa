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

# Power Management / ACPI Controller

**Status:** 📋 Planned - Structure Created
**Priority:** Medium
**Address:** `0x4000_5000 - 0x4000_5FFF` (4KB window)

---

## Overview

Power Management and ACPI-compatible register interface for system power control.

## Planned Features

- Clock gating control per block
- Power domain sequencing
- Reset generation and distribution
- Wake event handling
- Sleep/idle mode control
- ACPI-compatible registers
- APB register interface
- Interrupt generation for power events

## Applications

- Low-power system design
- Battery-powered devices
- Dynamic power management
- Thermal management
- OS power management interface
- Wake-on-event systems

## Files (To Be Created)

- `apb_pm_acpi.sv` - Top-level wrapper with APB interface
- `pm_acpi_core.sv` - Core power management logic
- `pm_clock_gate_ctrl.sv` - Clock gating control
- `pm_power_sequencer.sv` - Power domain sequencing
- `pm_acpi_config_regs.sv` - Register wrapper
- `pm_acpi_regs.sv` - PeakRDL generated registers
- `pm_acpi_regs_pkg.sv` - PeakRDL generated package

## Development Status

- [ ] SystemRDL register specification
- [ ] Clock gating logic implementation
- [ ] Power sequencing logic
- [ ] Wake event handling
- [ ] Core PM logic implementation
- [ ] APB wrapper
- [ ] Basic testbench
- [ ] Medium testbench
- [ ] Full testbench
- [ ] Documentation

---

**Last Updated:** 2025-10-29
