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

## Register Summary

| Offset | Name | Access | Description |
|--------|------|--------|-------------|
| 0x00 | PM1_STS | RO/W1C | PM1 Status |
| 0x04 | PM1_EN | RW | PM1 Enable |
| 0x08 | PM1_CNT | RW | PM1 Control |
| 0x0C | PM_TMR | RO | PM Timer |
| 0x10 | GPE0_STS | RO/W1C | GPE0 Status |
| 0x14 | GPE0_EN | RW | GPE0 Enable |
| 0x18 | GPE1_STS | RO/W1C | GPE1 Status |
| 0x1C | GPE1_EN | RW | GPE1 Enable |

---

## PM1_STS (0x00)

| Bit | Name | Access | Description |
|-----|------|--------|-------------|
| 0 | TMR_STS | W1C | Timer overflow status |
| 4 | BM_STS | W1C | Bus master status |
| 5 | GBL_STS | W1C | Global release status |
| 8 | PWRBTN_STS | W1C | Power button status |
| 9 | SLPBTN_STS | W1C | Sleep button status |
| 10 | RTC_STS | W1C | RTC alarm status |
| 15 | WAK_STS | W1C | Wake status |

---

## PM1_EN (0x04)

| Bit | Name | Access | Description |
|-----|------|--------|-------------|
| 0 | TMR_EN | RW | Timer overflow enable |
| 5 | GBL_EN | RW | Global release enable |
| 8 | PWRBTN_EN | RW | Power button enable |
| 9 | SLPBTN_EN | RW | Sleep button enable |
| 10 | RTC_EN | RW | RTC alarm enable |

---

## PM1_CNT (0x08)

| Bit | Name | Access | Description |
|-----|------|--------|-------------|
| 0 | SCI_EN | RW | SCI enable |
| 1 | BM_RLD | RW | Bus master reload |
| 2 | GBL_RLS | RW | Global release |
| 12:10 | SLP_TYP | RW | Sleep type |
| 13 | SLP_EN | RW | Sleep enable |

---

## PM_TMR (0x0C)

| Bits | Name | Access | Description |
|------|------|--------|-------------|
| 23:0 | TMR_VAL | RO | Timer value (3.579545 MHz) |

---

**Back to:** [PM/ACPI Specification Index](../pm_acpi_index.md)
