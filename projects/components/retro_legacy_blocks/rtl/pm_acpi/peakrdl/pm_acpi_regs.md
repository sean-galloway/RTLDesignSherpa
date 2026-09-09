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

<p>This block's SCI_EN. Gates GPE event CAPTURE and the
pm_interrupt PIN: with it clear the pin is held low. It
does NOT gate PM1 or WAKE status recording, so events that
happen while ACPI is disabled are still there to read once
it is enabled.</p>

#### pm_timer_enable field

<p>Enable PM Timer (0=stopped, 1=running)</p>

#### gpe_enable field

<p>Enable GPE event processing</p>

#### current_state field

<p>Current power state: 0=S0, 1=S1, 3=S3</p>

#### low_power_req field

<p>STORAGE ONLY - no hardware effect (GH#54 H3). The bit is
readable and writable and nothing in pm_acpi_core consumes
it: there is no separate 'low power mode' distinct from the
S1/S3 states, and the RDL never specified one. Sleep entry
is requested through PM1_CONTROL.sleep_type + sleep_enable.
The field is kept for register-map compatibility and is
documented as software scratch rather than being silently
routed to an unused core input.</p>

#### soft_reset field

<p>Write 1 to soft-reset the PM controller (self-clearing, so
it always reads 0). One pulse clears every sticky status
register (ACPI_STATUS, ACPI_INT_STATUS, PM1_STATUS,
WAKE_STATUS, GPE0_STATUS_LO/HI), drops the latched wake
request, forces the power-state FSM back to S0 and switches
RESET_STATUS from por_reset to sw_reset. Configuration
registers are NOT affected.</p>

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

<p>UNCONDITIONAL per-source EVENT LOG (write 1 to clear). Every
bit records its event whether or not the matching
ACPI_INT_ENABLE bit is set, and each clears independently.
This register does NOT drive the pm_interrupt pin - that is
the OR of ENABLED bits in ACPI_STATUS, PM1_STATUS and
GPE0_STATUS - so clearing an interrupt does not mean clearing
two registers. Read it to find out WHAT happened; clear the
status register to make the pin drop.</p>

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

<p>PME event recorded (W1C). Set by a power/sleep button press, a wake event or a completed power-state transition.</p>

#### wake_int field

<p>Wake event recorded (W1C). Set by any enabled wake source.</p>

#### timer_ovf_int field

<p>PM timer overflow event recorded (W1C).</p>

#### state_trans_int field

<p>Power-state transition event recorded (W1C).</p>

#### pm1_int field

<p>PM1 event recorded (W1C). Set by any of the five PM1_STATUS sources - the SAME sources the PM1 interrupt term uses - regardless of PM1_ENABLE.</p>

#### gpe_int field

<p>GPE event recorded (W1C). Set by a captured GPE EDGE, not by the pending level, so it can be dismissed before GPE0_STATUS_LO/HI is drained. Independent of the GPE0_ENABLE mask; it does follow GPE capture being enabled at all (ACPI_CONTROL.acpi_enable and .gpe_enable), because a GPE this block was told not to watch is not an event it observed.</p>

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

<p>Write 1 to request entry to the state selected by
sleep_type. This is a ONE-SHOT request (self-clearing, so it
always reads 0) and pm_acpi_core rising-edge detects it, so
a wake event that returns the machine to S0 cannot be undone
by the still-programmed sleep_type: software does not have
to rewrite sleep_type after a wake (GH#54 H5).
Corner: a wake landing in the EXACT cycle of this write is
not latched - it is still recorded in ACPI_STATUS,
PM1_STATUS and WAKE_STATUS and still raises pm_interrupt if
enabled, but the machine sleeps and the NEXT wake returns
it to S0.</p>

#### pwrbtn_ovr field

<p>STORAGE ONLY - no hardware effect (GH#54 H3). 'Override
power button behavior' never named a concrete effect (no
target state, no mask semantics), so rather than invent one
the field is documented as software scratch and is not
routed to pm_acpi_core. The power button always sets
PM1_STATUS.pwrbtn_sts; mask its interrupt with
PM1_ENABLE.pwrbtn_en and its wake with
WAKE_ENABLE.pwrbtn_wake_en.</p>

#### slpbtn_ovr field

<p>STORAGE ONLY - no hardware effect (GH#54 H3), for the same
reason as pwrbtn_ovr. Mask the sleep button's interrupt with
PM1_ENABLE.slpbtn_en.</p>

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

<p>RTC alarm occurred (W1C). Set on the synchronized rtc_alarm
ASSERTION EDGE, not the level, so a W1C clears it even
while the pin is still held; the pin must deassert and
reassert to record another alarm.</p>

#### wak_sts field

<p>System wake event (W1C)</p>

#### reserved field

<p>Reserved bits</p>

### PM1_ENABLE register

- Absolute Address: 0x18
- Base Offset: 0x18
- Size: 0x4

<p>PM1 event enable mask. Each bit gates its source's contribution
to pm_interrupt; PM1_STATUS still records the event either way
(GH#54 H3 - before the fix these bits were routed to
pm_acpi_core and never used). PM1_STATUS.wak_sts has no enable
bit, matching ACPI: a wake is reported but is not an interrupt
source on its own.</p>

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

<p>RTC alarm wake source asserted (W1C). Edge-set, like
PM1_STATUS.rtc_sts.</p>

#### ext_wake field

<p>External wake source asserted (W1C). Set on the
synchronized ext_wake_n ASSERTION EDGE, not the level, so a
W1C clears it even while the pin is still held low.</p>

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

<p>Write 1 to pulse the sys_reset_req output for one PM-clock
cycle (self-clearing, so it always reads 0). What the system
does with that request is outside this block.</p>

#### periph_reset field

<p>Write 1 to pulse the periph_reset_req output for one
PM-clock cycle (self-clearing, so it always reads 0).</p>

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

<p>Reads 1 while the last reset of this block was the
power-on/system reset (a STICKY LEVEL, not the one-cycle
pulse it used to be - software could never observe that
through APB latency, GH#54 round_2 item 7). Cleared only
when ACPI_CONTROL.soft_reset executes, which hands the
'last reset' title to sw_reset.</p>

#### wdt_reset field

<p>ALWAYS READS 0 - apb4_pm_acpi has no watchdog input port, so
a watchdog reset is not observable here (GH#54 round_2 item
7). Kept for register-map compatibility; wiring it would
take a new device pin.</p>

#### sw_reset field

<p>Reads 1 once ACPI_CONTROL.soft_reset has been executed at
least since the last hardware reset (sticky level; por_reset
drops in the same cycle).</p>

#### ext_reset field

<p>ALWAYS READS 0 - apb4_pm_acpi has no external-reset input
port, so an external reset is indistinguishable from a
power-on reset here (GH#54 round_2 item 7).</p>

#### reserved field

<p>Reserved bits</p>
