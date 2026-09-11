# pm_acpi Timing Diagrams

## Overview

This directory contains WaveDrom timing diagrams for PM/ACPI (Power Management / Advanced Configuration and Power Interface) operational scenarios.

| File | Scenario | Description |
|------|----------|-------------|
| `pm_sleep_entry.json` | Sleep Entry | PM1_CONTROL write initiates S3 suspend |
| `pm_wake_event.json` | Wake Event | Wake from S3 (drawn with the power button, a one-cycle source; the latched wake request lands it in S0) |
| `pm_timer.json` | PM Timer | PM timer read for OS timing |
| `pm_gpe_event.json` | GPE Event | General Purpose Event raises pm_interrupt |

## Waveforms

> Note: The signal names below are ACPI-generic illustrations for the diagrams.
> Several do not exist as RTL ports: there are no dedicated `slp_s3_n/slp_s4_n/slp_s5_n`
> sleep pins, no `pwrok`, `pm_tmr_clk`, `sci_n`, `smi_n`, or `wake_lan`, and no
> `cache_flush_req`. The RTL uses a single active-high `pm_interrupt`, an active-low
> `ext_wake_n`, and a `pm_clk` timer clock. See Chapter 3 (interfaces) once written.

### APB Interface (External)
- `s_apb_PSEL`, `s_apb_PENABLE`, `s_apb_PREADY` - Control signals
- `s_apb_PWRITE`, `s_apb_PADDR`, `s_apb_PWDATA`, `s_apb_PRDATA` - Data signals

### Power Pins (External)
- `slp_s3_n`, `slp_s4_n`, `slp_s5_n` - Sleep state outputs (active low)
- `pwrok` - Main power OK input
- `pm_tmr_clk` - PM timer clock (3.579545 MHz)

### Wake Sources (External)
- `wake_pwrbtn_n` - Power button wake
- `wake_rtc` - RTC alarm wake
- `wake_lan` - Wake-on-LAN
- `gpe_in[n]` - General purpose event inputs

### Interrupt Outputs (External)
- `sci_n` - System Control Interrupt (to OS)
- `smi_n` - System Management Interrupt (to SMM)

### PM Core (Internal)
- **Sleep:** `slp_typ`, `slp_en`, `r_sleep_state`, `cache_flush_req`
- **Wake:** `r_wake_sts`, `wake_enabled`, `wake_trigger`
- **Timer:** `r_pm_timer`, `tmr_overflow`
- **GPE:** `gpe_sync`, `gpe_edge`, `gpe_en`, `GPE0_STS`, `gpe_active`

### Rendering to SVG

```bash
# Render all files
for f in *.json; do
    wavedrom-cli -i "$f" > "${f%.json}.svg"
done
```

### 1. Sleep Entry (S3 Suspend)
Shows the sleep sequence:
1. Software writes PM1_CONTROL with sleep_type and sleep_enable
2. The PM core FSM enters the requested state (S1 or S3)
3. Clock gating / power domain outputs update for the target state
4. state_transition status is set on completion

### 2. Wake Event
Shows the wake from S3 via the power button, a one-cycle source:
1. System in S3 sleep (power domains off)
2. Enabled wake source (power button press, after its 3-flop synchronizer) detected
3. Wake status set in WAKE_STATUS / PM1_STATUS.wak_sts and the wake request latched in the core
4. FSM passes through TRANSITION back to S0; the latched request outranks the still-programmed sleep_type
5. Power restored, system stays in S0; pm_interrupt asserts if enabled and holds until the status is cleared

### 3. PM Timer
Shows PM timer operation:
- 32-bit free-running counter (PM_TIMER_VALUE, 0x020)
- ~3.571 MHz via PM_TIMER_CONFIG divider (default divide-by-28 from
  100 MHz; ACPI target 3.579545 MHz)
- OS reads for high-resolution timing
- Overflow generates tmr_sts / timer_overflow event if enabled

### 4. GPE Event
Shows General Purpose Event handling:
1. External GPE input rising edge detected, after its SYNC_STAGES synchronizer
2. That one GPE status bit set in GPE0_STATUS_LO/HI, and held
3. If GPE enabled (GPE0_ENABLE_LO/HI and ACPI_INT_ENABLE.gpe_int_enable), pm_interrupt asserted
4. OS reads status, services event
5. OS writes 1-to-clear status bit
6. pm_interrupt deasserted; the same clear unblocks the next sleep entry

### Register Reference

> These tables reflect the RTL register map. See
> `docs/pm_acpi_mas/ch05_registers/01_register_map.md` for the authoritative
> map. The diagrams above use ACPI-generic labels that differ from these names.

#### PM1 Status (PM1_STATUS, 0x014, W1C)
| Bit | Name | Description |
|-----|------|-------------|
| 4 | wak_sts | System wake event |
| 3 | rtc_sts | RTC alarm occurred |
| 2 | slpbtn_sts | Sleep button pressed |
| 1 | pwrbtn_sts | Power button pressed |
| 0 | tmr_sts | PM timer carry/overflow |

#### PM1 Enable (PM1_ENABLE, 0x018, RW)
| Bit | Name | Description |
|-----|------|-------------|
| 3 | rtc_en | RTC alarm enable |
| 2 | slpbtn_en | Sleep button enable |
| 1 | pwrbtn_en | Power button enable |
| 0 | tmr_en | PM timer enable |

#### PM1 Control (PM1_CONTROL, 0x010, RW)
| Bits | Name | Description |
|------|------|-------------|
| 5 | slpbtn_ovr | Sleep button override (storage only) |
| 4 | pwrbtn_ovr | Power button override (storage only) |
| 3 | sleep_enable | Enter sleep (write 1, one-shot, auto-clears) |
| 2:0 | sleep_type | Sleep type (0=S0, 1=S1, 3=S3) |

#### Sleep Types
| sleep_type | State | Description |
|------------|-------|-------------|
| 000 | S0 | Working |
| 001 | S1 | Sleep (clock gating, context retained) |
| 011 | S3 | Deep sleep (power domains off, wake from events) |

S0, S1, S3 and S5 are implemented; other sleep_type encodings fall through to S0. current_state is a two-bit ENCODING, not the ACPI number: 0=S0, 1=S1, 2=S5, 3=S3.

## References

- **PM RTL:** `rtl/pm_acpi/apb4_pm_acpi.sv`
- **PM Testbench:** `dv/tbclasses/pm_acpi/pm_acpi_tb.py`
- **Constraint Class:** none yet for PM/ACPI (see `bin/TBClasses/wavedrom_user/hpet.py` and `apb.py` for examples)
- **ACPI Spec:** Advanced Configuration and Power Interface Specification
