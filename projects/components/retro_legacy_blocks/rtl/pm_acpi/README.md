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


# Power Management / ACPI Controller - APB Implementation

**Status:** Implemented and defect-clean against GitHub #54
**Priority:** Medium
**Address:** `0x4000_5000 - 0x4000_5FFF` (4KB window)

**Test status:** 6/6 configurations green at FULL (CDC_ENABLE 0/1, 2026-09-09):
basic 8/8, medium 10/10, full 12/12, GH#54 defect suite 17/17 in each.

---

## Overview

APB-based ACPI-style power management block: a 32-bit PM timer, an S0/S1/S3
power-state machine, 32 general-purpose events, 32 clock-gate controls, 8 power
domains, four wake sources and a single aggregated interrupt.

Three layers, the same shape every RLB block uses:

    apb4_pm_acpi          APB4 slave (+ optional CDC), parameter plumbing
      pm_acpi_config_regs peakrdl_to_cmdrsp + strict decode + pm_acpi_regs
      pm_acpi_core        timer, FSM, GPE, wake, sticky status, interrupt

`pm_acpi_regs.sv` / `pm_acpi_regs_pkg.sv` are GENERATED from
`peakrdl/pm_acpi_regs.rdl`. Never hand-edit them; see `peakrdl/README.md`.

## Features

- ACPI-style PM1 control/status/enable and a global ACPI status/interrupt pair
- 32-bit PM timer, configurable divider (~3.571 MHz from 100 MHz at the /28
  default; the ACPI target is 3.579545 MHz)
- 32 GPE sources, rising-edge detected, per-bit sticky status and enable mask
- Every status bit is EDGE-set, including the two level pins (rtc_alarm,
  ext_wake_n), so a W1C takes effect while the pin is still asserted
- Power state FSM: S0 working, S1 sleep (clocks gated except bits [1:0]),
  S3 suspend (all clocks gated, all power domains but 0 off)
- Wake from GPE, power button, RTC alarm or an external pin, with the wake
  request LATCHED so a one-cycle source lands in S0 and stays
- Strict address decode: only the twenty-one mapped registers are visible,
  every other address in the 4 KB window is dropped and answered with PSLVERR
- Input synchronizers on rtc_alarm, ext_wake_n and gpe_events (SYNC_STAGES,
  default 2, unconditional); 3-flop chains on the two buttons
- APB4 slave, optional CDC (pclk vs pm_clk)

## Status is sticky and the core owns it

Every W1C status bit - ACPI_STATUS (4), ACPI_INT_STATUS (6), PM1_STATUS (5),
WAKE_STATUS (4) and GPE0_STATUS_LO/HI (32) - lives in `pm_acpi_core` as

    r_status <= (r_status & ~software_clear) | hardware_set;

A hardware event sets, a software write of 1 to that bit clears, a write of 0
does nothing, a W1C of one bit leaves the others alone, and a set that races a
clear WINS. The generated register fields are live MIRRORS of those registers
(`sw=rw hw=w precedence=sw onwrite=woclr`, no `hwset`);
`pm_acpi_config_regs` decodes the clear mask from the write data and byte
enables at the register's own address, one pulse per transaction.

This replaces a register block that held the state itself with `hwset` and an
undriven `next`, which reloaded the field every cycle there was neither a write
nor a set - so a single-bit status could not hold at all, and a multi-bit
`hwset` on GPE0_STATUS set all sixteen bits at once (issue #54 C2, round_2
items 1-2).

## Every status bit is edge-set

GPE, both buttons, `rtc_alarm` and `ext_wake_n` all set their status bit on the
synchronized ASSERTION EDGE, never on the level. Setting from a level re-armed
the bit every cycle, so a W1C could not take effect while the pin was still
asserted - software could see the event but never dismiss it, and with
`pm1_int` behind it the interrupt could not be dropped either. The pin must
deassert and reassert to record a second event.

The wake terms follow the same rule, so no wake term is a raw pin level:

| source | wake term |
|--------|-----------|
| GPE | the enabled-and-pending level of the sticky GPE status (W1C clears it, so an unacknowledged GPE keeps the machine awake) |
| power button | the press edge |
| RTC alarm | the `rtc_alarm` assertion edge |
| external | the `ext_wake_n` assertion edge |

**Consequence, stated rather than hidden:** a level source already asserted
*before* the sleep request neither blocks sleep entry nor wakes the machine. It
has to deassert and reassert. `WAKE_STATUS` records the original assertion
either way.

## The interrupt is a level

`pm_interrupt` is the OR of ENABLED STICKY status bits and deasserts only when
software has cleared every enabled source:

| term | status | enable |
|------|--------|--------|
| PME / wake / timer overflow / state transition | ACPI_STATUS bit N | ACPI_INT_ENABLE bit N |
| PM1 | PM1_STATUS bit N | PM1_ENABLE bit N, then ACPI_INT_ENABLE.pm1_enable |
| GPE | GPE0_STATUS bit N | GPE0_ENABLE bit N, then ACPI_INT_ENABLE.gpe_int_enable |

`PM1_STATUS.wak_sts` has no enable bit in the register map (matching ACPI: a
wake is reported, it is not an interrupt source), so it is masked out of the
PM1 term.

`ACPI_CONTROL.acpi_enable` is this block's **SCI_EN**: it gates GPE event
CAPTURE and the `pm_interrupt` PIN. It does *not* gate PM1 or WAKE status
recording, so with ACPI disabled the block still keeps a history of what
happened - enabling ACPI later shows software what it missed rather than a
blank slate.

`ACPI_INT_STATUS` is an unconditional per-source EVENT LOG: every bit sets on
its event whether or not the matching `ACPI_INT_ENABLE` bit is set, and each
clears independently. It deliberately does NOT feed `pm_interrupt` - if it did,
dropping one interrupt would mean clearing two registers. `gpe_int` there is
set by a captured GPE EDGE rather than the pending level, so it can be
dismissed before `GPE0_STATUS` is drained. Read `ACPI_INT_STATUS` to find out
WHAT happened; clear the status register to make the pin drop.

## Sleep and wake

`PM1_CONTROL.sleep_enable` is a `singlepulse` one-shot in the register map and
is rising-edge detected in the core, so one write is one sleep request:

    S0 --sleep_enable, sleep_type 1|3--> TRANSITION --> S1 | S3
    S1|S3 --enabled wake event--> TRANSITION --> S0

In `PWR_TRANSITION` a latched or live wake OUTRANKS the still-programmed
`sleep_type`. `r_wake_pending` arms on any enabled wake event while the machine
is out of S0 and is dropped on reaching S0 or on a new sleep request. Software
therefore does not have to unprogram `sleep_type` after a wake (issue #54 H5).

**One-cycle corner:** a wake event landing in the *exact* cycle of the sleep
request is not latched - the request clears the latch in that cycle, and the
machine is still in S0, where the latch is held clear anyway. The event is not
lost: it is recorded in `ACPI_STATUS.wake_status`, `PM1_STATUS.wak_sts` and its
`WAKE_STATUS` bit, and raises `pm_interrupt` if enabled. The machine sleeps and
the next wake returns it to S0. Widening the latch to cover that cycle would
let a wake arriving *before* software asked to sleep block sleep entry
outright, which is the failure the S0 clear exists to prevent.

`sleep_type` values other than 0, 1 and 3 are treated as 0 (stay in S0).

## Registers that are storage only

| field | why |
|-------|-----|
| `ACPI_CONTROL.low_power_req` | there is no low-power mode distinct from S1/S3; sleep entry goes through PM1_CONTROL |
| `PM1_CONTROL.pwrbtn_ovr` | "override power button behavior" never named a concrete effect |
| `PM1_CONTROL.slpbtn_ovr` | same |

They read and write, they are documented as storage in the RDL, and they are
not routed to `pm_acpi_core` - a register that does nothing should not look
like a connected input nobody reads (issue #54 H3).

`RESET_STATUS.wdt_reset` and `.ext_reset` always read 0: this module has no
watchdog or external-reset input pin, so those reset sources are not
observable here. `.por_reset` is a sticky LEVEL (it was a one-cycle pulse no
APB read could ever land on) and hands over to `.sw_reset` when
`ACPI_CONTROL.soft_reset` executes.

## Reset requests

`RESET_CTRL.sys_reset` / `.periph_reset` are `singlepulse` bits that produce
EXACTLY ONE pm_clk pulse on `sys_reset_req` / `periph_reset_req`. That is a
contract, not an accident: `peakrdl_to_cmdrsp` holds its request for the accept
cycle plus `CMD_WAIT_ACK`, so a `singlepulse` field arrives at the core as a
TWO-cycle level, and the core rising-edge detects all four self-clearing
request bits (`sleep_enable`, `soft_reset`, `sys_reset`, `periph_reset`) so one
software write is one core pulse whatever the bridge does with the width. What the system does
with the request is outside this block. `ACPI_CONTROL.soft_reset` clears every
sticky status register, the GPE status, the latched wake and returns the FSM to
S0; configuration registers are untouched.

## Parameters

| parameter | default | meaning |
|-----------|---------|---------|
| `CDC_ENABLE` | 0 | 0 = one clock (pclk drives everything), 1 = pm_clk is asynchronous to pclk and the APB slave carries an async FIFO |
| `USE_JOHNSON` | 0 | CDC FIFO pointer encoding: 0 Gray (power-of-2 depth), 1 Johnson |
| `SYNC_STAGES` | 2 | depth of the rtc_alarm / ext_wake_n / gpe_events synchronizers, >= 2 |

With `CDC_ENABLE = 1`, `pm_interrupt` and the clock-gate / power-domain / reset
outputs are in the `pm_clk` domain. Synchronize them externally if a consumer
runs on another clock.

## Contracts

- Drive `rtc_alarm`, `ext_wake_n` and any `gpe_events` bit for at least two
  pm_clk periods. Anything shorter can fall between synchronizer samples.
- A GPE is RISING-EDGE detected. A source held high forever produces one event,
  not a level.
- `PM_TIMER_VALUE` is read-only; there is no software path to preload it. The
  DV suite pokes `pm_acpi_core.r_pm_timer_count` by hierarchical name to reach
  an overflow in finite simulation time.

## Files

| file | role |
|------|------|
| `apb4_pm_acpi.sv` | top: APB4 slave (+ CDC), instantiates the other two |
| `pm_acpi_config_regs.sv` | adapter, strict decode, W1C mask decode, hwif mapping |
| `pm_acpi_core.sv` | timer, FSM, GPE, wake, sticky status, interrupt |
| `pm_acpi_regs.sv` | GENERATED register block |
| `pm_acpi_regs_pkg.sv` | GENERATED hwif package |
| `peakrdl/pm_acpi_regs.rdl` | the register source of truth |
| `peakrdl/pm_acpi_regs.md` | generated register documentation |
| `filelists/apb4_pm_acpi.f` | compile closure |

## Not implemented

Deferred work is recorded in `vault/Tasks/RLB/open.md` (RLB-009), not in a
tracker next to the code. In short: clock-gate and power-domain transitions are
instant, there is no S5 state, GPE is edge-only with a single bank, the timer
is 32-bit only, and the buttons get a synchronizer rather than a real
debouncer.

---

**Last Updated:** 2026-09-09
