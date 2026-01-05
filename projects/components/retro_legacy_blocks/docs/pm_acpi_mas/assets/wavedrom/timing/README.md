# PM/ACPI Timing Diagrams - WaveDrom JSON Files

This directory contains WaveDrom timing diagrams for PM/ACPI (Power Management / Advanced Configuration and Power Interface) operational scenarios.

## Files

| File | Scenario | Description |
|------|----------|-------------|
| `pm_sleep_entry.json` | Sleep Entry | PM1_CNT write initiates S3 suspend |
| `pm_wake_event.json` | Wake Event | Power button triggers wake from S3 |
| `pm_timer.json` | PM Timer | ACPI timer read for OS timing |
| `pm_gpe_event.json` | GPE Event | General Purpose Event triggers SCI |

## Signal Hierarchy

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

## Rendering to SVG

```bash
# Render all files
for f in *.json; do
    wavedrom-cli -i "$f" > "${f%.json}.svg"
done
```

## Scenarios Explained

### 1. Sleep Entry (S3 Suspend)
Shows ACPI sleep sequence:
1. OS writes PM1_CNT with SLP_TYP (sleep type) and SLP_EN (sleep enable)
2. PM controller initiates cache flush
3. Asserts appropriate SLP_Sx# signal
4. Power is removed from non-essential components

### 2. Wake Event
Shows wake from S3 via power button:
1. System in S3 sleep (SLP_S3# asserted, power off)
2. Wake source (power button) detected
3. Wake status latched
4. SLP_S3# deasserted
5. Power restored, system resumes to S0

### 3. PM Timer
Shows ACPI PM timer operation:
- 24-bit (or 32-bit extended) free-running counter
- Clocked at 3.579545 MHz (14.31818 MHz / 4)
- OS reads for high-resolution timing
- Overflow generates TMR_STS event if enabled

### 4. GPE Event
Shows General Purpose Event handling:
1. External GPE input edge detected
2. GPE status bit set in GPE0_STS
3. If GPE enabled (GPE0_EN), SCI# asserted
4. OS reads status, services event
5. OS writes 1-to-clear status bit
6. SCI# deasserted

## Register Reference

### PM1 Status (PM1_STS)
| Bit | Name | Description |
|-----|------|-------------|
| 15 | WAK_STS | Wake status |
| 10 | RTC_STS | RTC alarm status |
| 8 | PWRBTN_STS | Power button status |
| 5 | GBL_STS | Global lock status |
| 4 | BM_STS | Bus master status |
| 0 | TMR_STS | Timer overflow status |

### PM1 Enable (PM1_EN)
| Bit | Name | Description |
|-----|------|-------------|
| 10 | RTC_EN | RTC alarm enable |
| 8 | PWRBTN_EN | Power button enable |
| 5 | GBL_EN | Global lock enable |
| 0 | TMR_EN | Timer overflow enable |

### PM1 Control (PM1_CNT)
| Bits | Name | Description |
|------|------|-------------|
| 12:10 | SLP_TYP | Sleep type (S1-S5) |
| 13 | SLP_EN | Sleep enable |
| 0 | SCI_EN | SCI enable |

### Sleep Types
| SLP_TYP | State | Description |
|---------|-------|-------------|
| 000 | S0 | Working |
| 001 | S1 | Sleeping (CPU stopped) |
| 010 | S2 | Sleeping (CPU off) |
| 011 | S3 | Suspend to RAM |
| 100 | S4 | Suspend to Disk |
| 101 | S5 | Soft Off |

## References

- **PM RTL:** `rtl/pm/apb_pm_acpi.sv`
- **PM Testbench:** `dv/tbclasses/pm/pm_tb.py`
- **Constraint Class:** `bin/CocoTBFramework/tbclasses/wavedrom_user/pm.py`
- **ACPI Spec:** Advanced Configuration and Power Interface Specification
