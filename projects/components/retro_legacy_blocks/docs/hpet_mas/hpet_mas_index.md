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

# APB HPET Micro-Architecture Specification

**Component:** APB High Precision Event Timer (HPET)
**Version:** 1.3
**Last Updated:** 2026-09-09
**Status:** RTL Functional - register interface validated; HPET_STATUS
per-bit W1C with a reset value and a core-owned status mirror, independent
counter halves, strobe-driven comparator loads and the no-re-fire armed
latch are as specified (fixed 2026-09-08, issue #46); periodic catch-up
(missed periods skipped, never burst; period 1 steps to counter + 1), the
stopped-timer-only comparator re-arm and the next-epoch hold (an advance
that carries out of the compare width is held off until the counter wraps
there) are as specified (review rounds 1 and 2, 2026-09-09)

---

## Overview

This MAS describes the APB HPET as the RTL exists today. The register-side defects that issue #46 collected -- a W1C that cleared every bit on any write, status storage with no reset, a counter load that shipped the previous write's other half, and completed one-shots re-firing on every enable -- were fixed on 2026-09-08, and two review rounds the next day tightened the rules the chapters below now state: a comparator write re-arms only a stopped timer (so a half-written 64-bit comparator can never fire on the torn value), a periodic timer that falls behind catches up silently instead of firing once and going quiet (at period 1 by stepping to counter + 1), and a comparator whose advance carries out of the compare width is held in the counter's next epoch until the counter wraps there, rather than matching early. The two intentional limitations that remain (legacy replacement and `timer_value_set` are storage with nothing behind them) are called out in-line where you'll meet them. The spec is organized into five chapters covering the micro-architecture of the APB HPET component.

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2026-01-04 | RTL Design Sherpa | Initial MAS release |
| 1.1 | 2026-09-08 | RTL Design Sherpa | Issue #46 fixes: per-bit W1C status mirror with reset, independent counter halves, strobe-driven comparator loads, armed-latch fire (no re-fire on enable), HPET_ID from parameters |
| 1.2 | 2026-09-09 | RTL Design Sherpa | Issue #46 review: comparator writes re-arm only a stopped timer (torn 64-bit value cannot fire; disable-write-enable contract), periodic catch-up skips missed periods without bursting, period 0/1 behaviour, same-cycle write-and-fire rule, halted-counter rule for byte-strobed counter writes |
| 1.3 | 2026-09-09 | RTL Design Sherpa | Issue #46 review round 2: period-1 catch-up steps to counter + 1 and terminates on advance >= counter; next-epoch hold bit (`r_comp_next_epoch`) for an advance that carries out of the compare width, with its four clears and the width consequences; stopped-timer comparator write always re-arms (a value at or below the counter fires on enable, no wait for wrap); running-timer reprogramming consequences stated as outside the contract; width-masked advance in 32-bit mode |

: Table: Version History

---

## Navigation

### Chapter 1: Overview
- [01_overview.md](ch01_overview/01_overview.md) - Component overview, features, applications
- [02_architecture.md](ch01_overview/02_architecture.md) - High-level architecture and block hierarchy
- [03_clocks_and_reset.md](ch01_overview/03_clocks_and_reset.md) - Clock domains and reset behavior
- [04_acronyms.md](ch01_overview/04_acronyms.md) - Acronyms and terminology
- [05_references.md](ch01_overview/05_references.md) - External references and standards

### Chapter 2: Blocks
- [00_overview.md](ch02_blocks/00_overview.md) - Block hierarchy overview
- [01_hpet_core.md](ch02_blocks/01_hpet_core.md) - Core timer logic (counter, comparators, FSM)
- [02_hpet_config_regs.md](ch02_blocks/02_hpet_config_regs.md) - Configuration register wrapper
- [03_hpet_regs.md](ch02_blocks/03_hpet_regs.md) - PeakRDL generated register file
- [04_apb4_hpet_top.md](ch02_blocks/04_apb4_hpet_top.md) - Top-level integration
- [05_fsm_summary.md](ch02_blocks/05_fsm_summary.md) - FSM state summary table

### Chapter 3: Interfaces
*(planned, not yet written - see `../../rtl/hpet/apb4_hpet.sv` for the current port list)*
- 01_top_level.md - Top-level signal list
- 02_apb_interface_spec.md - APB protocol specification
- 03_hpet_clock_interface.md - HPET clock domain interface
- 04_interrupt_interface.md - Timer interrupt outputs

### Chapter 4: Programming Model
*(planned, not yet written - see the HPET section of [../../CLAUDE.md](../../CLAUDE.md) for programming notes)*
- 01_initialization.md - Software initialization sequence
- 02_timer_configuration.md - Configuring timers (one-shot, periodic)
- 03_interrupt_handling.md - Interrupt service routines
- 04_use_cases.md - Common use case examples

### Chapter 5: Registers
- [01_register_map.md](ch05_registers/01_register_map.md) - Complete register address map and field descriptions
