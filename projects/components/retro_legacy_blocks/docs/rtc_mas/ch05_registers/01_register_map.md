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

# APB RTC - Register Map

## Register Summary

| Offset | Name | Access | Reset | Description |
|--------|------|--------|-------|-------------|
| 0x00 | RTC_SECONDS | RW | 0x00 | Seconds (BCD 0-59) |
| 0x04 | RTC_MINUTES | RW | 0x00 | Minutes (BCD 0-59) |
| 0x08 | RTC_HOURS | RW | 0x00 | Hours (BCD 0-23/1-12) |
| 0x0C | RTC_DAY | RW | 0x01 | Day of week (1-7) |
| 0x10 | RTC_DATE | RW | 0x01 | Day of month (BCD 1-31) |
| 0x14 | RTC_MONTH | RW | 0x01 | Month (BCD 1-12) |
| 0x18 | RTC_YEAR | RW | 0x00 | Year (BCD 0-99) |
| 0x1C | RTC_CENTURY | RW | 0x20 | Century (BCD 20-29) |
| 0x20 | RTC_ALM_SEC | RW | 0x00 | Alarm seconds |
| 0x24 | RTC_ALM_MIN | RW | 0x00 | Alarm minutes |
| 0x28 | RTC_ALM_HOUR | RW | 0x00 | Alarm hours |
| 0x2C | RTC_ALM_DATE | RW | 0x00 | Alarm date |
| 0x30 | RTC_CONTROL | RW | 0x00 | Control |
| 0x34 | RTC_STATUS | RO/W1C | 0x00 | Status |

---

## RTC_CONTROL (0x30)

| Bit | Name | Access | Description |
|-----|------|--------|-------------|
| 0 | RTC_EN | RW | RTC enable |
| 1 | ALM_EN | RW | Alarm enable |
| 2 | PIE | RW | Periodic interrupt enable |
| 3 | AIE | RW | Alarm interrupt enable |
| 4 | UIE | RW | Update interrupt enable |
| 5 | HR24 | RW | 24-hour mode (0=12hr, 1=24hr) |
| 7:6 | Reserved | RO | Reserved |

---

## RTC_STATUS (0x34)

| Bit | Name | Access | Description |
|-----|------|--------|-------------|
| 0 | UIP | RO | Update in progress |
| 1 | PF | W1C | Periodic flag |
| 2 | AF | W1C | Alarm flag |
| 3 | UF | W1C | Update flag |
| 4 | IRQF | RO | IRQ flag (PF|AF|UF when enabled) |
| 7:5 | Reserved | RO | Reserved |

---

## BCD Format

Time/date values stored in BCD:
- Seconds: 0x00-0x59
- Minutes: 0x00-0x59
- Hours (24hr): 0x00-0x23
- Hours (12hr): 0x01-0x12 + bit 7 for PM
- Date: 0x01-0x31
- Month: 0x01-0x12
- Year: 0x00-0x99

---

**Back to:** [RTC Specification Index](../rtc_index.md)
