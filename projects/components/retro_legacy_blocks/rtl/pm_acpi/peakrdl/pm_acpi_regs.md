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

<!---
Markdown description for SystemRDL register map.

Don't override. Generated from: $root
-->

## pm_acpi_regs address map

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x70

<p>ACPI-compatible power management controller with clock gating and GPE support</p>

|Offset|     Identifier    |              Name             |
|------|-------------------|-------------------------------|
| 0x00 |    ACPI_CONTROL   |     ACPI Control Register     |
| 0x04 |    ACPI_STATUS    |      ACPI Status Register     |
| 0x08 |  ACPI_INT_ENABLE  | ACPI Interrupt Enable Register|
| 0x0C |  ACPI_INT_STATUS  | ACPI Interrupt Status Register|
| 0x10 |    PM1_CONTROL    |      PM1 Control Register     |
| 0x14 |     PM1_STATUS    |      PM1 Status Register      |
| 0x18 |     PM1_ENABLE    |      PM1 Enable Register      |
| 0x20 |   PM_TIMER_VALUE  |    PM Timer Value Register    |
| 0x24 |  PM_TIMER_CONFIG  |PM Timer Configuration Register|
| 0x30 |   GPE0_STATUS_LO  |    GPE0 Status Low Register   |
| 0x34 |   GPE0_STATUS_HI  |   GPE0 Status High Register   |
| 0x38 |   GPE0_ENABLE_LO  |    GPE0 Enable Low Register   |
| 0x3C |   GPE0_ENABLE_HI  |   GPE0 Enable High Register   |
| 0x50 |  CLOCK_GATE_CTRL  |  Clock Gate Control Register  |
| 0x54 | CLOCK_GATE_STATUS |   Clock Gate Status Register  |
| 0x58 | POWER_DOMAIN_CTRL | Power Domain Control Register |
| 0x5C |POWER_DOMAIN_STATUS|  Power Domain Status Register |
| 0x60 |    WAKE_STATUS    |      Wake Status Register     |
| 0x64 |    WAKE_ENABLE    |      Wake Enable Register     |
| 0x68 |     RESET_CTRL    |     Reset Control Register    |
| 0x6C |    RESET_STATUS   |     Reset Status Register     |

### ACPI_CONTROL register

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x4

<p>Global ACPI power management control</p>

|Bits|   Identifier  |Access|Reset|        Name       |
|----|---------------|------|-----|-------------------|
|  0 |  acpi_enable  |  rw  | 0x0 |    ACPI Enable    |
|  1 |pm_timer_enable|  rw  | 0x0 |  PM Timer Enable  |
|  2 |   gpe_enable  |  rw  | 0x0 |     GPE Enable    |
| 5:4| current_state |   r  |  —  |Current Power State|
|  6 | low_power_req |  rw  | 0x0 |   Low Power Mode  |
|  7 |   soft_reset  |  rw  | 0x0 |     Soft Reset    |
|31:8|    reserved   |   r  | 0x0 |      Reserved     |

#### acpi_enable field

<p>Enable ACPI functionality (0=disabled, 1=enabled)</p>

#### pm_timer_enable field

<p>Enable PM Timer (0=stopped, 1=running)</p>

#### gpe_enable field

<p>Enable GPE event processing</p>

#### current_state field

<p>Current power state: 0=S0, 1=S1, 3=S3</p>

#### low_power_req field

<p>Request low power mode entry</p>

#### soft_reset field

<p>Soft reset PM controller (write 1, auto-clears)</p>

#### reserved field

<p>Reserved bits</p>

### ACPI_STATUS register

- Absolute Address: 0x4
- Base Offset: 0x4
- Size: 0x4

<p>Global ACPI status and events (write 1 to clear)</p>

|Bits|   Identifier   |  Access |Reset|         Name         |
|----|----------------|---------|-----|----------------------|
|  0 |   pme_status   |rw, woclr| 0x0 |      PME Status      |
|  1 |   wake_status  |rw, woclr| 0x0 |      Wake Status     |
|  2 | timer_overflow |rw, woclr| 0x0 |    Timer Overflow    |
|  3 |state_transition|rw, woclr| 0x0 |Power State Transition|
|31:4|    reserved    |    r    | 0x0 |       Reserved       |

#### pme_status field

<p>Power Management Event occurred (W1C)</p>

#### wake_status field

<p>System woke from low power state (W1C)</p>

#### timer_overflow field

<p>PM Timer overflow occurred (W1C)</p>

#### state_transition field

<p>Power state transition complete (W1C)</p>

#### reserved field

<p>Reserved bits</p>

### ACPI_INT_ENABLE register

- Absolute Address: 0x8
- Base Offset: 0x8
- Size: 0x4

<p>Interrupt enable mask for ACPI events</p>

|Bits|    Identifier    |Access|Reset|          Name         |
|----|------------------|------|-----|-----------------------|
|  0 |    pme_enable    |  rw  | 0x0 |       PME Enable      |
|  1 |    wake_enable   |  rw  | 0x0 |      Wake Enable      |
|  2 | timer_ovf_enable |  rw  | 0x0 | Timer Overflow Enable |
|  3 |state_trans_enable|  rw  | 0x0 |State Transition Enable|
|  4 |    pm1_enable    |  rw  | 0x0 |    PM1 Event Enable   |
|  5 |  gpe_int_enable  |  rw  | 0x0 |       GPE Enable      |
|31:6|     reserved     |   r  | 0x0 |        Reserved       |

#### pme_enable field

<p>Enable interrupt on PME event</p>

#### wake_enable field

<p>Enable interrupt on wake event</p>

#### timer_ovf_enable field

<p>Enable interrupt on PM timer overflow</p>

#### state_trans_enable field

<p>Enable interrupt on power state transition</p>

#### pm1_enable field

<p>Enable interrupt on any PM1 event</p>

#### gpe_int_enable field

<p>Enable interrupt on any GPE event</p>

#### reserved field

<p>Reserved bits</p>

### ACPI_INT_STATUS register

- Absolute Address: 0xC
- Base Offset: 0xC
- Size: 0x4

<p>Interrupt status for ACPI events (write 1 to clear)</p>

|Bits|   Identifier  |  Access |Reset|           Name           |
|----|---------------|---------|-----|--------------------------|
|  0 |    pme_int    |rw, woclr| 0x0 |       PME Interrupt      |
|  1 |    wake_int   |rw, woclr| 0x0 |      Wake Interrupt      |
|  2 | timer_ovf_int |rw, woclr| 0x0 | Timer Overflow Interrupt |
|  3 |state_trans_int|rw, woclr| 0x0 |State Transition Interrupt|
|  4 |    pm1_int    |rw, woclr| 0x0 |       PM1 Interrupt      |
|  5 |    gpe_int    |rw, woclr| 0x0 |       GPE Interrupt      |
|31:6|    reserved   |    r    | 0x0 |         Reserved         |

#### pme_int field

<p>PME interrupt pending (W1C)</p>

#### wake_int field

<p>Wake interrupt pending (W1C)</p>

#### timer_ovf_int field

<p>Timer overflow interrupt pending (W1C)</p>

#### state_trans_int field

<p>State transition interrupt pending (W1C)</p>

#### pm1_int field

<p>PM1 interrupt pending (W1C)</p>

#### gpe_int field

<p>GPE interrupt pending (W1C)</p>

#### reserved field

<p>Reserved bits</p>

### PM1_CONTROL register

- Absolute Address: 0x10
- Base Offset: 0x10
- Size: 0x4

<p>ACPI PM1 control register (sleep, power button)</p>

|Bits| Identifier |Access|Reset|         Name        |
|----|------------|------|-----|---------------------|
| 2:0| sleep_type |  rw  | 0x0 |      Sleep Type     |
|  3 |sleep_enable|  rw  | 0x0 |     Sleep Enable    |
|  4 | pwrbtn_ovr |  rw  | 0x0 |Power Button Override|
|  5 | slpbtn_ovr |  rw  | 0x0 |Sleep Button Override|
|31:6|  reserved  |   r  | 0x0 |       Reserved      |

#### sleep_type field

<p>Sleep type: 0=S0, 1=S1, 3=S3</p>

#### sleep_enable field

<p>Enable sleep state entry (write 1 to enter sleep)</p>

#### pwrbtn_ovr field

<p>Override power button behavior</p>

#### slpbtn_ovr field

<p>Override sleep button behavior</p>

#### reserved field

<p>Reserved bits</p>

### PM1_STATUS register

- Absolute Address: 0x14
- Base Offset: 0x14
- Size: 0x4

<p>ACPI PM1 status flags (write 1 to clear)</p>

|Bits|Identifier|  Access |Reset|        Name       |
|----|----------|---------|-----|-------------------|
|  0 |  tmr_sts |rw, woclr| 0x0 |    Timer Status   |
|  1 |pwrbtn_sts|rw, woclr| 0x0 |Power Button Status|
|  2 |slpbtn_sts|rw, woclr| 0x0 |Sleep Button Status|
|  3 |  rtc_sts |rw, woclr| 0x0 |  RTC Alarm Status |
|  4 |  wak_sts |rw, woclr| 0x0 |    Wake Status    |
|31:5| reserved |    r    | 0x0 |      Reserved     |

#### tmr_sts field

<p>PM Timer carry/overflow (W1C)</p>

#### pwrbtn_sts field

<p>Power button pressed (W1C)</p>

#### slpbtn_sts field

<p>Sleep button pressed (W1C)</p>

#### rtc_sts field

<p>RTC alarm occurred (W1C)</p>

#### wak_sts field

<p>System wake event (W1C)</p>

#### reserved field

<p>Reserved bits</p>

### PM1_ENABLE register

- Absolute Address: 0x18
- Base Offset: 0x18
- Size: 0x4

<p>PM1 event enable mask</p>

|Bits|Identifier|Access|Reset|        Name       |
|----|----------|------|-----|-------------------|
|  0 |  tmr_en  |  rw  | 0x0 |    Timer Enable   |
|  1 | pwrbtn_en|  rw  | 0x0 |Power Button Enable|
|  2 | slpbtn_en|  rw  | 0x0 |Sleep Button Enable|
|  3 |  rtc_en  |  rw  | 0x0 |  RTC Alarm Enable |
|31:4| reserved |   r  | 0x0 |      Reserved     |

#### tmr_en field

<p>Enable PM timer events</p>

#### pwrbtn_en field

<p>Enable power button events</p>

#### slpbtn_en field

<p>Enable sleep button events</p>

#### rtc_en field

<p>Enable RTC alarm events</p>

#### reserved field

<p>Reserved bits</p>

### PM_TIMER_VALUE register

- Absolute Address: 0x20
- Base Offset: 0x20
- Size: 0x4

<p>PM Timer current value (read-only, increments at 3.579545 MHz equivalent)</p>

|Bits| Identifier|Access|Reset|    Name   |
|----|-----------|------|-----|-----------|
|31:0|timer_value|   r  |  —  |Timer Value|

#### timer_value field

<p>Current PM timer count value</p>

### PM_TIMER_CONFIG register

- Absolute Address: 0x24
- Base Offset: 0x24
- Size: 0x4

<p>PM Timer divider and control</p>

| Bits|Identifier|Access|Reset|     Name    |
|-----|----------|------|-----|-------------|
| 15:0| timer_div|  rw  | 0x1B|Timer Divider|
|31:16| reserved |   r  | 0x0 |   Reserved  |

#### timer_div field

<p>Clock divider for PM timer: timer_clk = sys_clk / (divider + 1)</p>

#### reserved field

<p>Reserved bits</p>

### GPE0_STATUS_LO register

- Absolute Address: 0x30
- Base Offset: 0x30
- Size: 0x4

<p>GPE0 status bits [15:0] (write 1 to clear)</p>

| Bits|Identifier|  Access |Reset|       Name      |
|-----|----------|---------|-----|-----------------|
| 15:0|gpe_status|rw, woclr| 0x0 |GPE Status [15:0]|
|31:16| reserved |    r    | 0x0 |     Reserved    |

#### gpe_status field

<p>General Purpose Event status bits 0-15 (W1C)</p>

#### reserved field

<p>Reserved bits</p>

### GPE0_STATUS_HI register

- Absolute Address: 0x34
- Base Offset: 0x34
- Size: 0x4

<p>GPE0 status bits [31:16] (write 1 to clear)</p>

| Bits|Identifier|  Access |Reset|       Name       |
|-----|----------|---------|-----|------------------|
| 15:0|gpe_status|rw, woclr| 0x0 |GPE Status [31:16]|
|31:16| reserved |    r    | 0x0 |     Reserved     |

#### gpe_status field

<p>General Purpose Event status bits 16-31 (W1C)</p>

#### reserved field

<p>Reserved bits</p>

### GPE0_ENABLE_LO register

- Absolute Address: 0x38
- Base Offset: 0x38
- Size: 0x4

<p>GPE0 enable mask [15:0]</p>

| Bits|Identifier|Access|Reset|       Name      |
|-----|----------|------|-----|-----------------|
| 15:0|gpe_enable|  rw  | 0x0 |GPE Enable [15:0]|
|31:16| reserved |   r  | 0x0 |     Reserved    |

#### gpe_enable field

<p>General Purpose Event enable bits 0-15</p>

#### reserved field

<p>Reserved bits</p>

### GPE0_ENABLE_HI register

- Absolute Address: 0x3C
- Base Offset: 0x3C
- Size: 0x4

<p>GPE0 enable mask [31:16]</p>

| Bits|Identifier|Access|Reset|       Name       |
|-----|----------|------|-----|------------------|
| 15:0|gpe_enable|  rw  | 0x0 |GPE Enable [31:16]|
|31:16| reserved |   r  | 0x0 |     Reserved     |

#### gpe_enable field

<p>General Purpose Event enable bits 16-31</p>

#### reserved field

<p>Reserved bits</p>

### CLOCK_GATE_CTRL register

- Absolute Address: 0x50
- Base Offset: 0x50
- Size: 0x4

<p>Clock gating control for system blocks [31:0]</p>

|Bits|  Identifier |Access|   Reset  |       Name       |
|----|-------------|------|----------|------------------|
|31:0|clk_gate_ctrl|  rw  |0xFFFFFFFF|Clock Gate Control|

#### clk_gate_ctrl field

<p>Clock gate enable per block (0=gated/off, 1=enabled/on)</p>

### CLOCK_GATE_STATUS register

- Absolute Address: 0x54
- Base Offset: 0x54
- Size: 0x4

<p>Clock gate status (read-only, reflects actual gate state)</p>

|Bits|   Identifier  |Access|Reset|       Name      |
|----|---------------|------|-----|-----------------|
|31:0|clk_gate_status|   r  |  —  |Clock Gate Status|

#### clk_gate_status field

<p>Actual clock gate state per block (0=gated, 1=active)</p>

### POWER_DOMAIN_CTRL register

- Absolute Address: 0x58
- Base Offset: 0x58
- Size: 0x4

<p>Power domain enable control [7:0]</p>

|Bits|   Identifier  |Access|Reset|        Name        |
|----|---------------|------|-----|--------------------|
| 7:0|pwr_domain_ctrl|  rw  | 0xFF|Power Domain Control|
|31:8|    reserved   |   r  | 0x0 |      Reserved      |

#### pwr_domain_ctrl field

<p>Power domain enable per domain (0=off, 1=on)</p>

#### reserved field

<p>Reserved bits</p>

### POWER_DOMAIN_STATUS register

- Absolute Address: 0x5C
- Base Offset: 0x5C
- Size: 0x4

<p>Power domain status (read-only)</p>

|Bits|    Identifier   |Access|Reset|        Name       |
|----|-----------------|------|-----|-------------------|
| 7:0|pwr_domain_status|   r  |  —  |Power Domain Status|
|31:8|     reserved    |   r  | 0x0 |      Reserved     |

#### pwr_domain_status field

<p>Actual power domain state (0=off, 1=on)</p>

#### reserved field

<p>Reserved bits</p>

### WAKE_STATUS register

- Absolute Address: 0x60
- Base Offset: 0x60
- Size: 0x4

<p>Wake event sources (write 1 to clear)</p>

|Bits| Identifier|  Access |Reset|       Name      |
|----|-----------|---------|-----|-----------------|
|  0 |  gpe_wake |rw, woclr| 0x0 |     GPE Wake    |
|  1 |pwrbtn_wake|rw, woclr| 0x0 |Power Button Wake|
|  2 |  rtc_wake |rw, woclr| 0x0 |     RTC Wake    |
|  3 |  ext_wake |rw, woclr| 0x0 |  External Wake  |
|31:4|  reserved |    r    | 0x0 |     Reserved    |

#### gpe_wake field

<p>Woke from GPE event (W1C)</p>

#### pwrbtn_wake field

<p>Woke from power button (W1C)</p>

#### rtc_wake field

<p>Woke from RTC alarm (W1C)</p>

#### ext_wake field

<p>Woke from external signal (W1C)</p>

#### reserved field

<p>Reserved bits</p>

### WAKE_ENABLE register

- Absolute Address: 0x64
- Base Offset: 0x64
- Size: 0x4

<p>Wake event enable mask</p>

|Bits|  Identifier  |Access|Reset|          Name          |
|----|--------------|------|-----|------------------------|
|  0 |  gpe_wake_en |  rw  | 0x0 |     GPE Wake Enable    |
|  1 |pwrbtn_wake_en|  rw  | 0x0 |Power Button Wake Enable|
|  2 |  rtc_wake_en |  rw  | 0x0 |     RTC Wake Enable    |
|  3 |  ext_wake_en |  rw  | 0x0 |  External Wake Enable  |
|31:4|   reserved   |   r  | 0x0 |        Reserved        |

#### gpe_wake_en field

<p>Enable wake from GPE events</p>

#### pwrbtn_wake_en field

<p>Enable wake from power button</p>

#### rtc_wake_en field

<p>Enable wake from RTC alarm</p>

#### ext_wake_en field

<p>Enable wake from external signal</p>

#### reserved field

<p>Reserved bits</p>

### RESET_CTRL register

- Absolute Address: 0x68
- Base Offset: 0x68
- Size: 0x4

<p>Reset generation and control</p>

|Bits| Identifier |Access|Reset|      Name      |
|----|------------|------|-----|----------------|
|  0 |  sys_reset |  rw  | 0x0 |  System Reset  |
|  1 |periph_reset|  rw  | 0x0 |Peripheral Reset|
|31:2|  reserved  |   r  | 0x0 |    Reserved    |

#### sys_reset field

<p>Generate system reset (write 1, auto-clears)</p>

#### periph_reset field

<p>Generate peripheral reset (write 1, auto-clears)</p>

#### reserved field

<p>Reserved bits</p>

### RESET_STATUS register

- Absolute Address: 0x6C
- Base Offset: 0x6C
- Size: 0x4

<p>Reset source information (read-only)</p>

|Bits|Identifier|Access|Reset|     Name     |
|----|----------|------|-----|--------------|
|  0 | por_reset|   r  |  —  |Power-On Reset|
|  1 | wdt_reset|   r  |  —  |Watchdog Reset|
|  2 | sw_reset |   r  |  —  |Software Reset|
|  3 | ext_reset|   r  |  —  |External Reset|
|31:4| reserved |   r  | 0x0 |   Reserved   |

#### por_reset field

<p>Last reset was power-on reset</p>

#### wdt_reset field

<p>Last reset was watchdog timeout</p>

#### sw_reset field

<p>Last reset was software initiated</p>

#### ext_reset field

<p>Last reset was external pin</p>

#### reserved field

<p>Reserved bits</p>
