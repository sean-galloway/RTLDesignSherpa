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

# pm_acpi -- Register Map

## Overview

This register map is generated from the PeakRDL specification
(`rtl/pm_acpi/peakrdl/pm_acpi_regs.rdl`) and matches the synthesized register
block in `rtl/pm_acpi/pm_acpi_regs.sv`. Offsets are byte offsets from the block
base address. All registers are 32 bits wide with 32-bit access.

> Note: This block does not implement the classic ACPI PM1a/PM1b fixed-hardware
> layout (PM1_STS/PM1_EN/PM1_CNT at 0x00-0x0C, GPE0/GPE1). It is a custom
> PeakRDL register file. Fields such as BM_STS, GBL_STS, GBL_EN, SCI_EN, BM_RLD,
> GBL_RLS and a second GPE bank (GPE1) do not exist in the RTL.

### Register Summary

| Offset | Name | Access | Reset | Description |
|--------|------|--------|-------|-------------|
| 0x000 | ACPI_CONTROL | RW | 0x00000000 | Global control and power state |
| 0x004 | ACPI_STATUS | W1C | 0x00000000 | Global status and power events |
| 0x008 | ACPI_INT_ENABLE | RW | 0x00000000 | Interrupt enable mask |
| 0x00C | ACPI_INT_STATUS | W1C | 0x00000000 | Interrupt status |
| 0x010 | PM1_CONTROL | RW | 0x00000000 | PM1 control (sleep, button override) |
| 0x014 | PM1_STATUS | W1C | 0x00000000 | PM1 status flags |
| 0x018 | PM1_ENABLE | RW | 0x00000000 | PM1 event enable mask |
| 0x01C | (Reserved) | - | - | Not decoded: dropped with PSLVERR |
| 0x020 | PM_TIMER_VALUE | RO | 0x00000000 | PM Timer current value (32-bit) |
| 0x024 | PM_TIMER_CONFIG | RW | 0x0000001B | PM Timer clock divider |
| 0x028-0x02C | (Reserved) | - | - | Not decoded: dropped with PSLVERR |
| 0x030 | GPE0_STATUS_LO | W1C | 0x00000000 | GPE0 status bits [15:0] |
| 0x034 | GPE0_STATUS_HI | W1C | 0x00000000 | GPE0 status bits [31:16] |
| 0x038 | GPE0_ENABLE_LO | RW | 0x00000000 | GPE0 enable bits [15:0] |
| 0x03C | GPE0_ENABLE_HI | RW | 0x00000000 | GPE0 enable bits [31:16] |
| 0x040-0x04C | (Reserved) | - | - | Not decoded: dropped with PSLVERR |
| 0x050 | CLOCK_GATE_CTRL | RW | 0xFFFFFFFF | Clock gating control [31:0] |
| 0x054 | CLOCK_GATE_STATUS | RO | 0xFFFFFFFF | Clock gate status (reads the live core state; all gates enabled at reset) |
| 0x058 | POWER_DOMAIN_CTRL | RW | 0x000000FF | Power domain control [7:0] |
| 0x05C | POWER_DOMAIN_STATUS | RO | 0x000000FF | Power domain status (reads the live core state; all domains powered at reset) |
| 0x060 | WAKE_STATUS | W1C | 0x00000000 | Wake event sources |
| 0x064 | WAKE_ENABLE | RW | 0x00000000 | Wake event enable mask |
| 0x068 | RESET_CTRL | RW | 0x00000000 | Reset generation control |
| 0x06C | RESET_STATUS | RO | 0x00000001 | Reset source information (por_reset reads 1 out of reset) |
| 0x070-0xFFC | (Reserved) | - | - | Not decoded: dropped with PSLVERR |

Access legend: RW = read/write, RO = read-only (hardware-updated),
W1C = read status / write 1 to clear.

The decode is strict. Only the twenty-one mapped registers are visible to
software, compared on the whole 12-bit address, register by register.
Everything else in the 4 KB window -- the gaps at 0x01C, 0x028-0x02C and
0x040-0x04C as much as the space above 0x070 -- is dropped: the write is
ignored, the read returns 0, and the access is answered with PSLVERR. There
is no aliasing anywhere in the window (the map used to repeat every 0x80
bytes because only PADDR[6:0] reached the register block; fixed 2026-09-09,
issue #54).

Every W1C status register in this map is a live mirror of a register that
pm_acpi_core owns. The hardware event sets a bit and it holds until software
writes a 1 to that bit; a write of 0 is a no-op, a write to one status
register never touches another, PSTRB is honoured so a byte-strobed write
can only clear bits inside the enabled bytes, and a set that lands in the
same cycle as a clear wins. ACPI_CONTROL.soft_reset clears all of them at
once.

---

## Functional Description

Bit-level definitions, one section per register.

### ACPI_CONTROL (0x000)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 0 | acpi_enable | RW | 0 | SCI_EN-like master enable. Gates GPE event capture (no GPE0_STATUS bit sets while it is 0) and the `pm_interrupt` pin (held low while it is 0). PM1_STATUS and WAKE_STATUS still record their events while it is 0, so software can see what happened before it enabled the block |
| 1 | pm_timer_enable | RW | 0 | Enable PM Timer (0=stopped, 1=running) |
| 2 | gpe_enable | RW | 0 | Enable GPE event processing |
| 5:4 | current_state | RO | 0 | Current power state (0=S0, 1=S1, 3=S3), hardware-updated; reads 0 (S0) while the FSM is in its transition state |
| 6 | low_power_req | RW | 0 | Storage only, no hardware effect. There is no low-power mode distinct from S1/S3; sleep entry goes through PM1_CONTROL. Reads back what was written |
| 7 | soft_reset | RW | 0 | Write 1 to soft-reset the PM controller (self-clearing, always reads 0). Exactly one core-clock pulse per write, however many cycles the bus holds the write -- the wrapper edge-detects the field. Clears every sticky status register (ACPI_STATUS, ACPI_INT_STATUS, PM1_STATUS, WAKE_STATUS, GPE0_STATUS_LO/HI), drops the latched wake request, returns the FSM to S0 and switches RESET_STATUS from por_reset to sw_reset. Configuration registers are untouched |
| 31:8 | reserved | RO | 0 | Reserved |

---

### ACPI_STATUS (0x004)

Write 1 to clear each bit. Each bit, ANDed with its ACPI_INT_ENABLE bit,
is one term of `pm_interrupt`.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 0 | pme_status | W1C | 0 | Power Management Event occurred: a button press, an enabled wake event or a completed state transition |
| 1 | wake_status | W1C | 0 | An enabled wake event occurred |
| 2 | timer_overflow | W1C | 0 | PM Timer overflow occurred |
| 3 | state_transition | W1C | 0 | Power state transition complete (the cycle the FSM leaves TRANSITION) |
| 31:4 | reserved | RO | 0 | Reserved |

---

### ACPI_INT_ENABLE (0x008)

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

### ACPI_INT_STATUS (0x00C)

Write 1 to clear each bit. This register is an unconditional per-source
event log: each bit sets when its event occurs, whether or not the
corresponding enable is set, and each bit is cleared by its own W1C
independently of ACPI_STATUS, PM1_STATUS and GPE0_STATUS. It does not feed
`pm_interrupt` (the enabled bits of those three do), so dropping an
interrupt means clearing one register, not two, and this one can be cleared
before or after the register that owns the interrupt.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 0 | pme_int | W1C | 0 | PME event recorded |
| 1 | wake_int | W1C | 0 | Wake event recorded |
| 2 | timer_ovf_int | W1C | 0 | Timer overflow event recorded |
| 3 | state_trans_int | W1C | 0 | State transition event recorded |
| 4 | pm1_int | W1C | 0 | PM1 event recorded: set whenever any PM1_STATUS bit sets (timer, power button, sleep button, RTC alarm, wake), enabled or not |
| 5 | gpe_int | W1C | 0 | GPE event recorded: set from the GPE edge events, not from the GPE pending level, so it can be cleared before or after GPE0_STATUS |
| 31:6 | reserved | RO | 0 | Reserved |

---

### PM1_CONTROL (0x010)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 2:0 | sleep_type | RW | 0 | Sleep type (0=S0, 1=S1, 3=S3); other values are treated as 0 and the FSM stays in S0 |
| 3 | sleep_enable | RW | 0 | Write 1 to request entry to the state in sleep_type. One-shot: self-clearing (always reads 0) and rising-edge detected in the core, so one write is one sleep request and a wake that returns the machine to S0 is not undone by the still-programmed sleep_type |
| 4 | pwrbtn_ovr | RW | 0 | Storage only, no hardware effect. The power button always sets PM1_STATUS.pwrbtn_sts; mask its interrupt with PM1_ENABLE.pwrbtn_en and its wake with WAKE_ENABLE.pwrbtn_wake_en |
| 5 | slpbtn_ovr | RW | 0 | Storage only, no hardware effect. Mask the sleep button's interrupt with PM1_ENABLE.slpbtn_en |
| 31:6 | reserved | RO | 0 | Reserved |

---

### PM1_STATUS (0x014)

Write 1 to clear each bit. The event is recorded whether or not its
PM1_ENABLE bit is set, and whether or not ACPI_CONTROL.acpi_enable is set;
the enables only gate the interrupt. rtc_sts is edge-latched: `rtc_alarm`
passes the synchronizer and then a rising-edge detector, and the edge sets
the bit. A W1C clears it even while the alarm is still asserted, and the
alarm must deassert and reassert to set it again -- the same rule as the
GPE bits and the buttons.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 0 | tmr_sts | W1C | 0 | PM Timer carry/overflow |
| 1 | pwrbtn_sts | W1C | 0 | Power button pressed |
| 2 | slpbtn_sts | W1C | 0 | Sleep button pressed |
| 3 | rtc_sts | W1C | 0 | RTC alarm occurred |
| 4 | wak_sts | W1C | 0 | System wake event. Has no PM1_ENABLE bit (ACPI reports a wake, it is not an interrupt source on its own), so it never contributes to `pm_interrupt` |
| 31:5 | reserved | RO | 0 | Reserved |

---

### PM1_ENABLE (0x018)

Each bit gates its source's contribution to `pm_interrupt` (together with
ACPI_INT_ENABLE.pm1_enable); PM1_STATUS still records the event either way.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 0 | tmr_en | RW | 0 | Enable PM timer events |
| 1 | pwrbtn_en | RW | 0 | Enable power button events |
| 2 | slpbtn_en | RW | 0 | Enable sleep button events |
| 3 | rtc_en | RW | 0 | Enable RTC alarm events |
| 31:4 | reserved | RO | 0 | Reserved |

---

### PM_TIMER_VALUE (0x020)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 31:0 | timer_value | RO | 0 | Current 32-bit PM timer count (hardware-updated) |

The counter is 32 bits and increments at a divided clock rate (see
PM_TIMER_CONFIG). At the default divider it advances at ~3.571 MHz from a
100 MHz pm_clk (100/28 -- 0.23% below the ACPI-standard 3.579545 MHz; an
exact tick needs pm_clk = 100.227 MHz) and rolls over roughly every 1200
seconds.

---

### PM_TIMER_CONFIG (0x024)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 15:0 | timer_div | RW | 0x001B | Clock divider: timer_clk = pm_clk / (timer_div + 1) |
| 31:16 | reserved | RO | 0 | Reserved |

Reset value 0x001B (27 decimal) divides by 28, yielding a 3.5714 MHz tick
from a 100.000 MHz pm_clk -- 0.23% below the ACPI-standard 3.579545 MHz
(an exact tick needs pm_clk = 100.227 MHz or a fractional divider).

---

### GPE0_STATUS_LO (0x030)

Covers GPE sources 0-15. A bit sets on a rising edge of its synchronized
`gpe_events` input while ACPI_CONTROL.acpi_enable and gpe_enable are both
set, and holds until software writes a 1 to it. Clearing is never gated by
the enables, so the register can always be drained. Each bit ANDed with its
GPE0_ENABLE bit is a pending GPE; the OR of those, gated by
ACPI_INT_ENABLE.gpe_int_enable, is the GPE term of `pm_interrupt`, and the
same OR gated by WAKE_ENABLE.gpe_wake_en is the GPE wake. Clearing the bit
therefore drops the interrupt and unblocks the next sleep entry.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 15:0 | gpe_status | W1C | 0 | General Purpose Event status bits 0-15 |
| 31:16 | reserved | RO | 0 | Reserved |

---

### GPE0_STATUS_HI (0x034)

Covers GPE sources 16-31, with the same set, hold and clear rules as
GPE0_STATUS_LO.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 15:0 | gpe_status | W1C | 0 | General Purpose Event status bits 16-31 |
| 31:16 | reserved | RO | 0 | Reserved |

---

### GPE0_ENABLE_LO (0x038)

Covers GPE sources 0-15.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 15:0 | gpe_enable | RW | 0 | General Purpose Event enable bits 0-15 |
| 31:16 | reserved | RO | 0 | Reserved |

---

### GPE0_ENABLE_HI (0x03C)

Covers GPE sources 16-31.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 15:0 | gpe_enable | RW | 0 | General Purpose Event enable bits 16-31 |
| 31:16 | reserved | RO | 0 | Reserved |

The 32 GPE sources are exposed as two 16-bit LO/HI register pairs. There is no
second GPE bank (no GPE1).

---

### CLOCK_GATE_CTRL (0x050)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 31:0 | clk_gate_ctrl | RW | 0xFFFFFFFF | Clock gate enable per block (0=gated/off, 1=enabled/on) |

---

### CLOCK_GATE_STATUS (0x054)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 31:0 | clk_gate_status | RO | 0xFFFFFFFF (live) | Actual clock gate state per block (reads the core register, which resets all-enabled) |

---

### POWER_DOMAIN_CTRL (0x058)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 7:0 | pwr_domain_ctrl | RW | 0xFF | Power domain enable per domain (0=off, 1=on) |
| 31:8 | reserved | RO | 0 | Reserved |

---

### POWER_DOMAIN_STATUS (0x05C)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 7:0 | pwr_domain_status | RO | 0xFF (live) | Actual power domain state (reads the core register, which resets all-powered) |
| 31:8 | reserved | RO | 0 | Reserved |

Sleep states override the CTRL values: in S1 the core forces
clock_gate_en = CLOCK_GATE_CTRL & 0x3 (only blocks 0-1 may stay on);
in S3 clock_gate_en = 0 and power_domain_en = POWER_DOMAIN_CTRL & 0x1
(domain 0 always-on). The STATUS registers therefore read back values
software never wrote while sleeping.

---

### WAKE_STATUS (0x060)

Write 1 to clear each bit. A bit sets when its source fires while the
matching WAKE_ENABLE bit is set, whatever ACPI_CONTROL.acpi_enable holds;
the same event sets PM1_STATUS.wak_sts and ACPI_STATUS.wake_status and arms
the core's latched wake request. The RTC and external sources are
edge-latched: `rtc_alarm` and `ext_wake_n` pass their synchronizers and
then a rising-edge detector, and the edge sets the bit, so a W1C clears it
while the pin is still asserted and the pin must deassert and reassert to
set it again -- the same rule as GPE and the buttons. The GPE wake request
itself stays pending until its GPE0_STATUS bit is cleared.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 0 | gpe_wake | W1C | 0 | Woke from GPE event |
| 1 | pwrbtn_wake | W1C | 0 | Woke from power button |
| 2 | rtc_wake | W1C | 0 | Woke from RTC alarm |
| 3 | ext_wake | W1C | 0 | Woke from external signal |
| 31:4 | reserved | RO | 0 | Reserved |

---

### WAKE_ENABLE (0x064)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 0 | gpe_wake_en | RW | 0 | Enable wake from GPE events |
| 1 | pwrbtn_wake_en | RW | 0 | Enable wake from power button |
| 2 | rtc_wake_en | RW | 0 | Enable wake from RTC alarm |
| 3 | ext_wake_en | RW | 0 | Enable wake from external signal |
| 31:4 | reserved | RO | 0 | Reserved |

---

### RESET_CTRL (0x068)

Both request fields are one-shots. A write of 1 produces exactly one
core-clock pulse on the output, however many cycles the bus holds the write,
because the wrapper edge-detects the singlepulse field; the same rule
applies to ACPI_CONTROL.soft_reset.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 0 | sys_reset | RW | 0 | Write 1 to pulse the `sys_reset_req` output for exactly one core-clock cycle per write (self-clearing, always reads 0). What the system does with the request is outside this block |
| 1 | periph_reset | RW | 0 | Write 1 to pulse the `periph_reset_req` output for exactly one core-clock cycle per write (self-clearing, always reads 0) |
| 31:2 | reserved | RO | 0 | Reserved |

---

### RESET_STATUS (0x06C)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 0 | por_reset | RO | 1 | Sticky level: reads 1 from hardware reset until ACPI_CONTROL.soft_reset executes, which hands the last-reset title to sw_reset |
| 1 | wdt_reset | RO | 0 | Always reads 0: this block has no watchdog input pin, so a watchdog reset is not observable here |
| 2 | sw_reset | RO | 0 | Sticky level: reads 1 once ACPI_CONTROL.soft_reset has executed since the last hardware reset (por_reset drops in the same cycle) |
| 3 | ext_reset | RO | 0 | Always reads 0: this block has no external-reset input pin, so an external reset is indistinguishable from a power-on reset here |
| 31:4 | reserved | RO | 0 | Reserved |

---

## Design Notes

### Where the status lives

The register block stores configuration and mirrors status. Every W1C bit
-- ACPI_STATUS, ACPI_INT_STATUS, PM1_STATUS, WAKE_STATUS and
GPE0_STATUS_LO/HI -- is a flop in pm_acpi_core of the shape
`(status & ~software_clear) | hardware_set`, and pm_acpi_config_regs turns a
software write into a one-cycle per-bit clear mask (write data ANDed with
the byte enables, at that register's own address). That is why a set wins
over a same-cycle clear, why a write to one register cannot disturb another,
and why PSTRB is honoured. This replaced a register block that held the
state itself with an undriven update input, so that single-bit status could
not hold and a GPE edge set all sixteen bits at once (fixed 2026-09-09,
issue #54).

### What feeds pm_interrupt

`pm_interrupt` is a level, the OR of these enabled sticky bits, and it
deasserts only when software has cleared every enabled source:

| Term | Status | Enable |
|------|--------|--------|
| PME, wake, timer overflow, state transition | ACPI_STATUS bit N | ACPI_INT_ENABLE bit N |
| PM1 | PM1_STATUS bit N (wak_sts excluded) | PM1_ENABLE bit N, then ACPI_INT_ENABLE.pm1_enable |
| GPE | GPE0_STATUS bit N | GPE0_ENABLE bit N, then ACPI_INT_ENABLE.gpe_int_enable |

ACPI_CONTROL.acpi_enable sits in front of the pin, SCI_EN-like: while it
is 0 `pm_interrupt` stays low and no GPE event is captured, but PM1_STATUS
and WAKE_STATUS keep recording their events, so software can see what
happened before it enabled the block.

ACPI_INT_STATUS is not in that OR. It is an unconditional per-source event
log: each bit sets when its event occurs whether or not the corresponding
enable is set (gpe_int from the GPE edge events, not from the GPE pending
level), and each bit is cleared by its own W1C independently, so it can be
cleared before or after the register that feeds the pin.

### Sleep and wake

PM1_CONTROL.sleep_enable is a one-shot: from S0, one write with sleep_type
1 or 3 takes the FSM through TRANSITION into S1 or S3. In S1 or S3 any
enabled wake source takes it through TRANSITION back to S0, and the core
latches the wake request so that in TRANSITION a latched or live wake
outranks the still-programmed sleep_type. A one-cycle power-button press
lands in S0 and stays there; software does not have to unprogram sleep_type
after a wake. The latch drops on reaching S0 and on the next sleep request.
One corner: a wake event that lands in the exact cycle of the sleep request
is not latched as a wake -- the sticky status bit and the level interrupt
still record it, the machine enters the programmed sleep state, and the next
wake event brings it back.

### Storage-only fields

ACPI_CONTROL.low_power_req and PM1_CONTROL.pwrbtn_ovr/slpbtn_ovr read and
write but are not routed to the core; there is no low-power mode distinct
from S1/S3, and "override the button" never named a concrete effect. They
are documented as storage, not as defects. RESET_STATUS.wdt_reset and
ext_reset read 0 for the same kind of reason: the block has no pin that
could report them.

### Deferred

Clock-gate and power-domain transitions are instant, there is no S5 state,
GPE is edge-only with a single bank, the timer is 32-bit only, and the
buttons get a synchronizer rather than a real debouncer. None of these are
defects; they are tracked as RLB-009 in `vault/Tasks/RLB/open.md`.

---

## Navigation

**Back to:** [PM/ACPI Specification Index](../pm_acpi_mas_index.md)
