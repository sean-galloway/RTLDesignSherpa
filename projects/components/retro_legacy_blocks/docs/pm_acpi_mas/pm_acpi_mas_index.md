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

# pm_acpi MAS -- Micro Architecture Specification

**Component:** APB Power Management / ACPI Controller
**Version:** 1.2
**Last Updated:** 2026-09-10
**Status:** RTL Functional -- per-bit sticky W1C status owned by the core
(ACPI_STATUS, ACPI_INT_STATUS, PM1_STATUS, WAKE_STATUS, GPE0_STATUS), a GPE
clear path that drops the interrupt and unblocks sleep, PM1_ENABLE gating the
interrupt, a level `pm_interrupt`, a latched wake request so a pulsed source
lands in S0 and stays, SYNC_STAGES input synchronizers, strict address decode
with PSLVERR and a sticky RESET_STATUS (issue #54 fixes, 2026-09-09).
S5 soft off, a debounced power button with the ACPI long-press override, a PM
timer with a prescaler, a 64-bit mode and a comparator, an optional rail
sequencer with a per-rail acknowledge, and GPE in two banks with per-source
edge or level and an optional run/wake split all landed 2026-09-10; RLB-009
is closed apart from what was always out of scope.

---

## Overview

> Status (2026-07-22): Only the Chapter 1 overview and the Chapter 5 register
> map exist in this tree today. The remaining chapters listed below are planned
> but not yet written; they are shown without links.

### Block Diagram

![PM/ACPI Block Diagram](assets/svg/pm_acpi_top.png)

### Version History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2025-12-01 | RTL Design Sherpa | Initial specification |
| 1.1 | 2026-09-09 | RTL Design Sherpa | Issue #54 fixes: sticky per-bit W1C status moved into pm_acpi_core with set-wins-over-clear and PSTRB-honoured clears, GPE status on the synchronized edge with a W1C clear that drops gpe_int and unblocks sleep, PM1_ENABLE per-source interrupt gating (wak_sts has no enable), level pm_interrupt over enabled sticky bits, latched wake outranking sleep_type with a one-shot sleep_enable, SYNC_STAGES synchronizers on rtc_alarm/ext_wake_n/gpe_events, strict 21-register decode with PSLVERR (no 0x80 aliasing), sticky por_reset/sw_reset with wired RESET_CTRL requests and a soft_reset that clears all status; storage-only fields stated; deferred work moved to RLB-009 |
| 1.2 | 2026-09-10 | RTL Design Sherpa | RLB-009 closed. S5 soft off: as dark as S3 but retains nothing, so LEAVING it pulses sys_reset_req -- a wake from soft off is a boot, not a resume; current_state reports encoding 2 for it, the one the three previous states left free. Buttons: a candidate level must hold for BUTTON_TIMING.debounce_cycles before it is accepted (0 = accept immediately, the old behaviour), and holding the accepted level for 2^long_press_shift cycles is the power-button override, ENABLED by PM1_CONTROL.pwrbtn_ovr rather than commanded by it. PM timer: a power-of-two prescaler ahead of the divider reaches the slow end of the range without widening a field software already uses; the counter is always 64 bits and timer_64bit only chooses WHICH carry counts as an overflow; PM_TIMER_MATCH is an equality comparator on the low word that drives the interrupt through ACPI_INT_ENABLE.timer_match_enable; PM_TIMER_VALUE_HI is a snapshot latched when the low word is read, so a pair of reads cannot straddle a carry. Rail sequencer (PWR_SEQ_CONFIG/STATUS, off at reset): clocks gated before the rails drop and restored only after they are all back, rails walked 7-to-0 out and 0-to-7 in with a programmable gap, each step optionally waiting for power_domain_ack, and no timeout because a made-up one turns a board fault into a silent half-powered state. GPE: per-source edge or level (GPEx_TRIGGER), a second bank on gpe1_events with its own status/enable/trigger/wake registers, and ACPI_CONTROL.gpe_split_enable separating the runtime interrupt arming from the wake arming. RESET_STATUS.wdt_reset and ext_reset come from device pins now, latched rather than sampled. Fifteen new registers take the map to thirty-eight and the decode to eight address bits, moving the first alias of ACPI_CONTROL from 0x080 to 0x100 |

---

## Navigation

### Chapter 1: Overview
- [01_overview.md](ch01_overview/01_overview.md) - Component overview
- 02_architecture.md - Architecture *(planned, not yet written)*

### Chapter 2: Blocks
- 00_overview.md - Block hierarchy *(planned, not yet written)*

### Chapter 3: Interfaces
- 00_overview.md - Interface summary *(planned, not yet written)*

### Chapter 4: Programming Model
- 00_overview.md - Programming overview *(planned, not yet written)*

### Chapter 5: Registers
- [01_register_map.md](ch05_registers/01_register_map.md) - Register map
