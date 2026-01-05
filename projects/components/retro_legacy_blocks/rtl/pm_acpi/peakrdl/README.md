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

# PM_ACPI PeakRDL Register Specification

This directory contains the SystemRDL specification for PM_ACPI (Power Management ACPI) controller registers.

## Register Generation

To generate the SystemVerilog register files from the RDL specification:

```bash
cd projects/components/retro_legacy_blocks/rtl/pm_acpi/peakrdl
python ../../../../../../../bin/peakrdl_generate.py pm_acpi_regs.rdl
```

This will generate:
- `../pm_acpi_regs.sv` - Register block implementation
- `../pm_acpi_regs_pkg.sv` - Package with type definitions and structs

## Register Map Overview

The PM_ACPI register map provides ACPI-compatible power management functionality:

### Global Control (0x000-0x00F)
- **ACPI_CONTROL** (0x000): Global enable, PM timer enable, GPE enable, power state
- **ACPI_STATUS** (0x004): PME, wake, timer overflow, state transition (W1C)
- **ACPI_INT_ENABLE** (0x008): Interrupt enable masks
- **ACPI_INT_STATUS** (0x00C): Interrupt status flags (W1C)

### PM1 Registers (0x010-0x01F)
- **PM1_CONTROL** (0x010): Sleep control, power button override
- **PM1_STATUS** (0x014): Timer, power button, sleep button, RTC, wake status (W1C)
- **PM1_ENABLE** (0x018): PM1 event enable masks

### PM Timer (0x020-0x02F)
- **PM_TIMER_VALUE** (0x020): Current timer value (read-only, 32-bit)
- **PM_TIMER_CONFIG** (0x024): Timer clock divider configuration

### GPE Registers (0x030-0x03F)
- **GPE0_STATUS_LO** (0x030): GPE status bits [15:0] (W1C)
- **GPE0_STATUS_HI** (0x034): GPE status bits [31:16] (W1C)
- **GPE0_ENABLE_LO** (0x038): GPE enable bits [15:0]
- **GPE0_ENABLE_HI** (0x03C): GPE enable bits [31:16]

### Clock and Power Control (0x050-0x06F)
- **CLOCK_GATE_CTRL** (0x050): Clock gating control [31:0]
- **CLOCK_GATE_STATUS** (0x054): Clock gate status (read-only)
- **POWER_DOMAIN_CTRL** (0x058): Power domain control [7:0]
- **POWER_DOMAIN_STATUS** (0x05C): Power domain status (read-only)
- **WAKE_STATUS** (0x060): Wake event sources (W1C)
- **WAKE_ENABLE** (0x064): Wake event enable mask
- **RESET_CTRL** (0x068): Reset generation control
- **RESET_STATUS** (0x06C): Reset source information (read-only)

## Key Features

- **ACPI Compatibility**: PM1 registers follow ACPI specification pattern
- **32-bit PM Timer**: Configurable divider for 3.579545 MHz equivalent
- **32 GPE Events**: General Purpose Events with W1C status and enable masks
- **Clock Gating**: 32 clock gate control bits
- **Power Domains**: 8 power domain control bits
- **Wake Events**: Multiple wake sources (GPE, power button, RTC, external)
- **W1C Status Registers**: Write-1-to-clear for proper interrupt handling
- **12-bit Address Space**: Matches RLB standard (0x000-0xFFF)

## Power States

The PM_ACPI controller supports simplified ACPI power states:
- **S0**: Working state (full power, all clocks active)
- **S1**: Sleep state (clock gating, context retained, quick wake)
- **S3**: Deep sleep (power domains off, context lost, wake from events)

## PM Timer

The PM timer is a 32-bit free-running counter that:
- Increments at 3.579545 MHz equivalent (configurable via divider)
- Rolls over approximately every 1200 seconds (20 minutes)
- Generates overflow interrupt when reaching 0xFFFFFFFF
- Read-only from software perspective
- Can be used for precise timing and power management

## Integration

The generated register files are used by:
- `pm_acpi_config_regs.sv` - Maps hwif to pm_acpi_core interface
- `apb_pm_acpi.sv` - Top-level APB wrapper

See parent directory README.md for complete integration details.
