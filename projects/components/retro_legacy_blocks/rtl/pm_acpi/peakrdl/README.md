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

`pm_acpi_regs.rdl` is the source of truth. `../pm_acpi_regs.sv` and
`../pm_acpi_regs_pkg.sv` are GENERATED - never hand-edit them, or the next
regeneration silently reverts the edit.

```bash
cd projects/components/retro_legacy_blocks/rtl/pm_acpi/peakrdl
python ../../../../../../bin/peakrdl_generate.py pm_acpi_regs.rdl \
    --copy-rtl .. --no-html --no-regmap
```

This writes into a local `generated/` scratch directory, copies the RTL up to
`../pm_acpi_regs.sv` and `../pm_acpi_regs_pkg.sv`, and leaves the Markdown in
`generated/docs/pm_acpi_regs.md`. Afterwards:

1. Refresh the checked-in `pm_acpi_regs.md` by keeping its first 23 lines (the
   house documentation header) and appending the newly generated body.
2. Delete `generated/` - a second, orphaned copy of generated output drifts
   silently and captures the next regeneration.

`--no-regmap` is deliberate: unlike hpet/pit/pic, no DV code imports a
`pm_acpi_regmap.py`, so emitting one would create a file nothing keeps in sync.
Add it (and drop the flag) if a helper script ever needs it.

Generated outputs:
- `../pm_acpi_regs.sv` - Register block implementation
- `../pm_acpi_regs_pkg.sv` - Package with type definitions and structs
- `pm_acpi_regs.md` - Register documentation (checked in, header preserved)

## Field conventions this map relies on (GitHub #54)

- **Every W1C status field is a live MIRROR**, not storage:
  `sw=rw; hw=w; precedence=sw; onwrite=woclr; swmod;` with reset 0.
  `pm_acpi_core` owns the sticky bit and `pm_acpi_config_regs` turns the
  software write into a per-bit clear pulse. `hwset` was REMOVED because it
  ignores `next` entirely - a multi-bit `hwset` sets ALL bits of the field, and
  the non-hwset branch reloads `next` every cycle, so a single-bit status could
  not hold state at all.
- **Self-clearing request bits are `singlepulse`**: `ACPI_CONTROL.soft_reset`,
  `PM1_CONTROL.sleep_enable`, `RESET_CTRL.sys_reset` and `.periph_reset`. The
  wrapper no longer ties their `next` inputs to zero to fake an auto-clear.
- **Storage-only fields say so in their descriptions**:
  `ACPI_CONTROL.low_power_req`, `PM1_CONTROL.pwrbtn_ovr` and `.slpbtn_ovr`.
  They are not routed to the core.
- **The address decode is strict.** `pm_acpi_config_regs` compares the whole
  12-bit address against the thirty-eight register offsets and drops everything
  else with PSLVERR. If you MOVE or ADD a register here, update the `ADDR_*`
  localparams in that file; the `a_regblk_addr_mapped` assertion is the guard.

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
- **32-bit PM Timer**: Configurable divider targeting ACPI 3.579545 MHz
  (~3.571 MHz at the default /28 from 100 MHz)
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
- Increments at ~3.571 MHz with the default divider (ACPI target
  3.579545 MHz; configurable)
- Rolls over approximately every 1200 seconds (20 minutes)
- Generates overflow interrupt when reaching 0xFFFFFFFF
- Read-only from software perspective
- Can be used for precise timing and power management

## Integration

The generated register files are used by:
- `pm_acpi_config_regs.sv` - Maps hwif to pm_acpi_core interface
- `apb4_pm_acpi.sv` - Top-level APB wrapper

See parent directory README.md for complete integration details.
