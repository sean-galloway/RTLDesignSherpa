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

# APB PM/ACPI - Register Map

This register map is generated from the PeakRDL specification
(`rtl/pm_acpi/peakrdl/pm_acpi_regs.rdl`) and matches the synthesized register
block in `rtl/pm_acpi/pm_acpi_regs.sv`. Offsets are byte offsets from the block
base address. All registers are 32 bits wide with 32-bit access.

> Note: This block does not implement the classic ACPI PM1a/PM1b fixed-hardware
> layout (PM1_STS/PM1_EN/PM1_CNT at 0x00-0x0C, GPE0/GPE1). It is a custom
> PeakRDL register file. Fields such as BM_STS, GBL_STS, GBL_EN, SCI_EN, BM_RLD,
> GBL_RLS and a second GPE bank (GPE1) do not exist in the RTL.

## Register Summary

| Offset | Name | Access | Reset | Description |
|--------|------|--------|-------|-------------|
| 0x000 | ACPI_CONTROL | RW | 0x00000000 | Global control and power state |
| 0x004 | ACPI_STATUS | W1C | 0x00000000 | Global status and power events |
| 0x008 | ACPI_INT_ENABLE | RW | 0x00000000 | Interrupt enable mask |
| 0x00C | ACPI_INT_STATUS | W1C | 0x00000000 | Interrupt status |
| 0x010 | PM1_CONTROL | RW | 0x00000000 | PM1 control (sleep, button override) |
| 0x014 | PM1_STATUS | W1C | 0x00000000 | PM1 status flags |
| 0x018 | PM1_ENABLE | RW | 0x00000000 | PM1 event enable mask |
| 0x01C | (Reserved) | - | - | Reserved |
| 0x020 | PM_TIMER_VALUE | RO | 0x00000000 | PM Timer current value (32-bit) |
| 0x024 | PM_TIMER_CONFIG | RW | 0x0000001B | PM Timer clock divider |
| 0x028-0x02C | (Reserved) | - | - | Reserved |
| 0x030 | GPE0_STATUS_LO | W1C | 0x00000000 | GPE0 status bits [15:0] |
| 0x034 | GPE0_STATUS_HI | W1C | 0x00000000 | GPE0 status bits [31:16] |
| 0x038 | GPE0_ENABLE_LO | RW | 0x00000000 | GPE0 enable bits [15:0] |
| 0x03C | GPE0_ENABLE_HI | RW | 0x00000000 | GPE0 enable bits [31:16] |
| 0x050 | CLOCK_GATE_CTRL | RW | 0xFFFFFFFF | Clock gating control [31:0] |
| 0x054 | CLOCK_GATE_STATUS | RO | 0x00000000 | Clock gate status |
| 0x058 | POWER_DOMAIN_CTRL | RW | 0x000000FF | Power domain control [7:0] |
| 0x05C | POWER_DOMAIN_STATUS | RO | 0x00000000 | Power domain status |
| 0x060 | WAKE_STATUS | W1C | 0x00000000 | Wake event sources |
| 0x064 | WAKE_ENABLE | RW | 0x00000000 | Wake event enable mask |
| 0x068 | RESET_CTRL | RW | 0x00000000 | Reset generation control |
| 0x06C | RESET_STATUS | RO | 0x00000000 | Reset source information |

Access legend: RW = read/write, RO = read-only (hardware-updated),
W1C = read status / write 1 to clear.

Addresses 0x070-0xFFF are decoded as reserved. The register block only decodes
the offsets listed above; unmapped reads in the decoded range return 0.

---

## ACPI_CONTROL (0x000)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 0 | acpi_enable | RW | 0 | Enable ACPI functionality (0=disabled, 1=enabled) |
| 1 | pm_timer_enable | RW | 0 | Enable PM Timer (0=stopped, 1=running) |
| 2 | gpe_enable | RW | 0 | Enable GPE event processing |
| 5:4 | current_state | RO | 0 | Current power state (0=S0, 1=S1, 3=S3), hardware-updated |
| 6 | low_power_req | RW | 0 | Request low power mode entry |
| 7 | soft_reset | RW | 0 | Soft reset PM controller (write 1, auto-clears) |
| 31:8 | reserved | RO | 0 | Reserved |

---

## ACPI_STATUS (0x004)

Write 1 to clear each bit.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 0 | pme_status | W1C | 0 | Power Management Event occurred |
| 1 | wake_status | W1C | 0 | System woke from low power state |
| 2 | timer_overflow | W1C | 0 | PM Timer overflow occurred |
| 3 | state_transition | W1C | 0 | Power state transition complete |
| 31:4 | reserved | RO | 0 | Reserved |

---

## ACPI_INT_ENABLE (0x008)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 0 | pme_enable | RW | 0 | Enable interrupt on PME event |
| 1 | wake_enable | RW | 0 | Enable interrupt on wake event |
| 2 | timer_ovf_enable | RW | 0 | Enable interrupt on PM timer overflow |
| 3 | state_trans_enable | RW | 0 | Enable interrupt on power state transition |
| 4 | pm1_enable | RW | 0 | Enable interrupt on any PM1 event |
| 5 | gpe_int_enable | RW | 0 | Enable interrupt on any GPE event |
| 31:6 | reserved | RO | 0 | Reserved |

---

## ACPI_INT_STATUS (0x00C)

Write 1 to clear each bit.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 0 | pme_int | W1C | 0 | PME interrupt pending |
| 1 | wake_int | W1C | 0 | Wake interrupt pending |
| 2 | timer_ovf_int | W1C | 0 | Timer overflow interrupt pending |
| 3 | state_trans_int | W1C | 0 | State transition interrupt pending |
| 4 | pm1_int | W1C | 0 | PM1 interrupt pending |
| 5 | gpe_int | W1C | 0 | GPE interrupt pending |
| 31:6 | reserved | RO | 0 | Reserved |

---

## PM1_CONTROL (0x010)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 2:0 | sleep_type | RW | 0 | Sleep type (0=S0, 1=S1, 3=S3) |
| 3 | sleep_enable | RW | 0 | Enter sleep state (write 1; hardware auto-clears one cycle later) |
| 4 | pwrbtn_ovr | RW | 0 | Override power button behavior |
| 5 | slpbtn_ovr | RW | 0 | Override sleep button behavior |
| 31:6 | reserved | RO | 0 | Reserved |

---

## PM1_STATUS (0x014)

Write 1 to clear each bit.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 0 | tmr_sts | W1C | 0 | PM Timer carry/overflow |
| 1 | pwrbtn_sts | W1C | 0 | Power button pressed |
| 2 | slpbtn_sts | W1C | 0 | Sleep button pressed |
| 3 | rtc_sts | W1C | 0 | RTC alarm occurred |
| 4 | wak_sts | W1C | 0 | System wake event |
| 31:5 | reserved | RO | 0 | Reserved |

---

## PM1_ENABLE (0x018)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 0 | tmr_en | RW | 0 | Enable PM timer events |
| 1 | pwrbtn_en | RW | 0 | Enable power button events |
| 2 | slpbtn_en | RW | 0 | Enable sleep button events |
| 3 | rtc_en | RW | 0 | Enable RTC alarm events |
| 31:4 | reserved | RO | 0 | Reserved |

---

## PM_TIMER_VALUE (0x020)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 31:0 | timer_value | RO | 0 | Current 32-bit PM timer count (hardware-updated) |

The counter is 32 bits and increments at a divided clock rate (see
PM_TIMER_CONFIG). At the default divider it advances at a 3.579545 MHz
equivalent rate and rolls over roughly every 1200 seconds.

---

## PM_TIMER_CONFIG (0x024)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 15:0 | timer_div | RW | 0x001B | Clock divider: timer_clk = pm_clk / (timer_div + 1) |
| 31:16 | reserved | RO | 0 | Reserved |

Reset value 0x001B (27 decimal) divides by 28, yielding the 3.579545 MHz
equivalent tick for a ~100 MHz pm_clk.

---

## GPE0_STATUS_LO (0x030)

Write 1 to clear. Covers GPE sources 0-15.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 15:0 | gpe_status | W1C | 0 | General Purpose Event status bits 0-15 |
| 31:16 | reserved | RO | 0 | Reserved |

---

## GPE0_STATUS_HI (0x034)

Write 1 to clear. Covers GPE sources 16-31.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 15:0 | gpe_status | W1C | 0 | General Purpose Event status bits 16-31 |
| 31:16 | reserved | RO | 0 | Reserved |

---

## GPE0_ENABLE_LO (0x038)

Covers GPE sources 0-15.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 15:0 | gpe_enable | RW | 0 | General Purpose Event enable bits 0-15 |
| 31:16 | reserved | RO | 0 | Reserved |

---

## GPE0_ENABLE_HI (0x03C)

Covers GPE sources 16-31.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 15:0 | gpe_enable | RW | 0 | General Purpose Event enable bits 16-31 |
| 31:16 | reserved | RO | 0 | Reserved |

The 32 GPE sources are exposed as two 16-bit LO/HI register pairs. There is no
second GPE bank (no GPE1).

---

## CLOCK_GATE_CTRL (0x050)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 31:0 | clk_gate_ctrl | RW | 0xFFFFFFFF | Clock gate enable per block (0=gated/off, 1=enabled/on) |

---

## CLOCK_GATE_STATUS (0x054)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 31:0 | clk_gate_status | RO | 0 | Actual clock gate state per block (hardware-updated) |

---

## POWER_DOMAIN_CTRL (0x058)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 7:0 | pwr_domain_ctrl | RW | 0xFF | Power domain enable per domain (0=off, 1=on) |
| 31:8 | reserved | RO | 0 | Reserved |

---

## POWER_DOMAIN_STATUS (0x05C)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 7:0 | pwr_domain_status | RO | 0 | Actual power domain state (hardware-updated) |
| 31:8 | reserved | RO | 0 | Reserved |

---

## WAKE_STATUS (0x060)

Write 1 to clear each bit.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 0 | gpe_wake | W1C | 0 | Woke from GPE event |
| 1 | pwrbtn_wake | W1C | 0 | Woke from power button |
| 2 | rtc_wake | W1C | 0 | Woke from RTC alarm |
| 3 | ext_wake | W1C | 0 | Woke from external signal |
| 31:4 | reserved | RO | 0 | Reserved |

---

## WAKE_ENABLE (0x064)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 0 | gpe_wake_en | RW | 0 | Enable wake from GPE events |
| 1 | pwrbtn_wake_en | RW | 0 | Enable wake from power button |
| 2 | rtc_wake_en | RW | 0 | Enable wake from RTC alarm |
| 3 | ext_wake_en | RW | 0 | Enable wake from external signal |
| 31:4 | reserved | RO | 0 | Reserved |

---

## RESET_CTRL (0x068)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 0 | sys_reset | RW | 0 | Generate system reset (write 1, auto-clears) |
| 1 | periph_reset | RW | 0 | Generate peripheral reset (write 1, auto-clears) |
| 31:2 | reserved | RO | 0 | Reserved |

---

## RESET_STATUS (0x06C)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 0 | por_reset | RO | 0 | Last reset was power-on reset |
| 1 | wdt_reset | RO | 0 | Last reset was watchdog timeout |
| 2 | sw_reset | RO | 0 | Last reset was software initiated |
| 3 | ext_reset | RO | 0 | Last reset was external pin |
| 31:4 | reserved | RO | 0 | Reserved |

---

## Implementation Notes (known RTL deviations)

The register file decodes and stores these registers, but several software-visible
behaviors are not yet wired through to the PM core. These are RTL issues tracked
separately (not fixed in documentation); they are documented here so software
does not rely on behavior the current RTL does not provide:

- ACPI_CONTROL.soft_reset (bit 7) and RESET_CTRL.sys_reset/periph_reset are not
  connected to the core; the reset-request outputs are hardwired to 0. Writing
  them auto-clears but has no effect.
- ACPI_CONTROL.low_power_req (bit 6) and PM1_CONTROL.pwrbtn_ovr/slpbtn_ovr
  (bits 4/5) are decoded but unused by the core.
- PM1_ENABLE per-source enables (tmr_en/pwrbtn_en/slpbtn_en/rtc_en) are decoded
  but do not currently gate PM1 status or the PM1 interrupt.
- Clearing GPE0_STATUS_LO/HI clears the register bits, but the core's internal
  GPE sticky status has no clear path, so the aggregated GPE interrupt source can
  remain asserted until reset.
- W1C status fields (ACPI_STATUS, ACPI_INT_STATUS, PM1_STATUS, WAKE_STATUS) have
  a hardware-update path whose `next` input is undriven in the current build;
  treat set-and-hold behavior of these status bits as unreliable until fixed.

---

**Back to:** [PM/ACPI Specification Index](../pm_acpi_mas_index.md)
