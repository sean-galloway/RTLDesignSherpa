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

# RLB Top - Power Management: Sleep and Wake Across Blocks

## Overview

Sleep in this subsystem belongs to exactly one block: the PM/ACPI
controller on window 5. The other nine blocks do not implement power
states, are not clock-gated by the PM block inside `rlb_top`, and keep
running on `pclk` through a sleep. What the PM block *does* produce on
its output pins — `pm_clock_gate_en[31:0]` and `pm_power_domain_en[7:0]`
— is a board-level clock-and-power policy that a consuming SoC may
honour, ignore, or wire to nothing. This page sequences the part
software controls: arming wake sources, entering S1/S3/S5, and reading
the subsystem back to S0. Register-level field detail is the PM/ACPI
book's; this page is the order of operations and the subsystem-level
facts that change it.

All addresses below are in window 5 (base `RLB_BASE + 0x5000`); see
[Chapter 5](../ch05_registers/01_register_map.md) and the pm_acpi
register chapter for the field tables.

## Who Participates

| Block | Role in sleep |
| --- | --- |
| PM/ACPI | Owns it. The sleep FSM, wake latches, and the gate/domain outputs all live here |
| 8259 pair, IOAPIC | Unchanged. Their programming survives sleep — an interrupt controller does not need re-initialization after wake |
| HPET, PIT, RTC, GPIO, UART, SMBus | Ignore sleep inside the subsystem. Their `*_clk`/`*_resetn` pins are unused (`CDC_ENABLE(0)`) and nothing gates their `pclk`. If a system wants them quiet in S3, the board consumes the PM gate outputs above the subsystem |
| APB fabric | Stays live. The crossbar decodes regardless of power state, which is what lets software read `WAKE_STATUS` after a wake |

Two consequences follow. First, there is no per-block quiesce sequence
inside `rlb_top` — software does not park the UART or silence the PIT
before sleeping; it simply stops caring, because nothing in the
subsystem asserts their interrupts into the fabric unless their own
event occurs. Second, `pm_clock_gate_en` / `pm_power_domain_en` are
*outputs for a board*, not a mechanism this subsystem enforces: in
simulation they can be observed and ignored.

## Step 1: Bring the PM Block Up

The PM block is one of the ten windows brought up by
[Initialization](01_initialization.md) step 5 — enable blocks — with one
extra gate before it matters: `ACPI_CONTROL.acpi_enable` (0x000 bit 0)
is the SCI_EN-like master switch. While it is 0, `pm_interrupt` is held
low and no GPE event is captured, though `PM1_STATUS` and `WAKE_STATUS`
still record their events. Set it before arming anything that must
interrupt.

## Step 2: Arm the Wake Sources

A source wakes the machine only when both halves are programmed:

1. **Global wake mask** — `WAKE_ENABLE` (0x064): bits for GPE, power
   button, RTC alarm, and external wake.
2. **Per-bank enables** — for GPE sources, program `GPE0_ENABLE` /
   `GPE1_ENABLE` (0x038-0x03C, 0x09C-0x0A0) and the matching
   `GPE0_WAKE_EN` / `GPE1_WAKE_EN` registers, and choose edge or level
   per source with `GPE0_TRIGGER` / `GPE1_TRIGGER`. The PM/ACPI book's
   GPE section owns the interrupt/wake split; the short version is that
   a source can be armed to wake a sleeping machine without interrupting
   a running one.

The non-GPE wake inputs are pins, and three of them need board
attention, stated here because they are the usual "sleep works but never
wakes" causes:

| Wake input | Pin | Board responsibility |
| --- | --- | --- |
| Power button | `pm_power_button_n` | Drive from the chassis switch; debounce window in `BUTTON_TIMING` (0x070) |
| Sleep button | `pm_sleep_button_n` | Optional; mask with `PM1_ENABLE.slpbtn_en` if absent |
| RTC alarm | `pm_rtc_alarm` | **Not wired to the RTC inside `rlb_top`** — `rtc_alarm_irq` is an output pin and `pm_rtc_alarm` is an input pin. Connect them at the board/SoC level if the RTC should wake the system |
| External wake | `pm_ext_wake_n` | Tie inactive if unused |

## Step 3: Enter Sleep

Program `PM1_CONTROL` (0x010):

1. Write `sleep_type` (bits 2:0): 1 = S1, 3 = S3, 5 = S5. Other values
   are treated as 0 and the FSM stays in S0.
2. Write `sleep_enable` (bit 3) = 1. This is a **one-shot**: the bit
   self-clears, and the core rising-edge-detects it, so one write is one
   sleep request and a wake that returns the machine to S0 is not undone
   by the still-programmed `sleep_type`.

On a board with real power rails, enable the rail sequencer first
(`PWR_SEQ_CONFIG`, 0x07C): `seq_enable` turns the clock/rail moves into
an ordered walk — clocks gated first on the way down, rails 7 to 0; rails
0 to 7 first on the way up, clocks ungated last — with optional
per-rail acknowledge and a programmable inter-step delay. Without it the
transitions are instant, which is correct in simulation and wrong on a
board. A rail that never acknowledges stalls the walk deliberately;
`PWR_SEQ_STATUS` (0x080) is where to look (`seq_busy` parked on a rail
index). There is no timeout, by design.

The hardware then walks the FSM through TRANSITION into the programmed
state. What the state means at the outputs:

| State | `pm_clock_gate_en` | `pm_power_domain_en` | Leaving it |
| --- | --- | --- | --- |
| S1 | `CLOCK_GATE_CTRL & 0x3` — only blocks 0-1 may stay clocked | `POWER_DOMAIN_CTRL` unchanged | Any armed wake source |
| S3 | 0 — everything gated | `POWER_DOMAIN_CTRL & 0x1` — domain 0 always on | Any armed wake source |
| S5 | 0 | `POWER_DOMAIN_CTRL & 0x1` | Pulses `pm_sys_reset_req`: a wake from S5 is a **boot**, not a resume |

`ACPI_CONTROL.current_state` (bits 5:4) reports the encoding, not the
ACPI number: 0 = S0, 1 = S1, 2 = S5, 3 = S3. It reads 0 while the FSM is
in TRANSITION.

## Step 4: Wake

An armed source fires while the FSM is in S1 or S3 and the core latches
the wake request — the latch outranks the still-programmed `sleep_type`
while the FSM is in TRANSITION, which is why a button press landing
during entry does not bounce the machine back into sleep. The FSM
returns through TRANSITION to S0, the latch drops, and the walk (if
enabled) re-powers rails in reverse order.

Software then:

1. Reads `WAKE_STATUS` (0x060) to identify the source —
   `gpe_wake`, `pwrbtn_wake`, `rtc_wake`, `ext_wake` — and writes 1s to
   clear it.
2. Clears the matching status that fed the interrupt: `ACPI_STATUS` (0x004),
   and `PM1_STATUS` (0x014) for the button/RTC paths, and the GPE status
   registers for a GPE wake. `pm_interrupt` is a level — the OR of the
   enabled sticky bits — and deasserts only when every enabled source has
   been cleared.
3. If the sleep was S5, treats the wake as a boot: `RESET_STATUS` reads
   differently, and whatever the system wired to `pm_sys_reset_req` has
   reset the machine.

One corner the PM book records: a wake event in the exact cycle of the
sleep request is **not** latched as a wake. The sticky status bits and
the level interrupt still record it, the machine enters the programmed
state, and the next wake event brings it back. Software that must not
sleep through such an event checks the status registers after entry.

## Step 5: The Interrupt Path for ACPI Events

`pm_interrupt` leaves the PM block on the fabric's IRQ9 line — ACPI by
convention — and therefore reaches the slave 8259 (IR1) and IOAPIC pin 9
like any other routed source (see
[Interrupt Pin Reference](../ch03_interfaces/03_interrupt_interfaces.md)).
The SCI handler is just a legacy interrupt handler: program the controllers
during [initialization](01_initialization.md) — step 3 for the 8259s, step 4
for the IOAPIC — to deliver IRQ9, and the PM block needs no special routing.
GPE events additionally depend on
`ACPI_INT_ENABLE.gpe_int_enable` and the GPE per-source enables before
they contribute to the pin.

## What Sleep Does Not Disturb

- **Interrupt controller programming.** The 8259 pair and IOAPIC hold
  their configuration across sleep; there is no re-init in the wake path.
- **The other blocks' state.** UART FIFOs, PIT counters, RTC time, GPIO
  configuration — all of it survives, because nothing inside the
  subsystem gates them. Only a board that consumes the PM gate outputs
  can change that, and then it is the board's contract, not this book's.
- **The address map.** Every window answers the same way after wake as
  before; the subsystem performs no remap on sleep or wake.

## Related Documents

- [Initialization](01_initialization.md) - the bring-up these steps assume
- [Use Cases](02_use_cases.md) - routing an interrupt end to end (the IRQ9 path)
- [The Interrupt Fabric](../ch02_blocks/02_interrupt_fabric.md) - how IRQ9 reaches both controllers
- PM/ACPI register detail - `pm_acpi_mas` book, chapter 5
