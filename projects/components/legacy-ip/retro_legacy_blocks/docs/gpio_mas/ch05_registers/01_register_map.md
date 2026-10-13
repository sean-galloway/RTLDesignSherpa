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

# APB GPIO - Register Map

## Overview

Thirteen registers, verified against the RTL decode (`gpio_regs.sv`) and
`../../rdl/gpio/gpio_regs.rdl`. `GPIO_REGS_SIZE = 0x34`.

| Offset | Name | Access | Reset | Description |
|--------|------|--------|-------|-------------|
| 0x000 | GPIO_CONTROL | RW | 0x00000001 | Global enable + global interrupt enable |
| 0x004 | GPIO_DIRECTION | RW | 0x00000000 | Pin direction |
| 0x008 | GPIO_OUTPUT | RW | 0x00000000 | Output data |
| 0x00C | GPIO_INPUT | RO | - | Input data |
| 0x010 | GPIO_INT_ENABLE | RW | 0x00000000 | Per-pin interrupt enable |
| 0x014 | GPIO_INT_TYPE | RW | 0x00000000 | Interrupt type |
| 0x018 | GPIO_INT_POLARITY | RW | 0xFFFFFFFF | Interrupt polarity |
| 0x01C | GPIO_INT_BOTH | RW | 0x00000000 | Both-edge enable |
| 0x020 | GPIO_INT_STATUS | W1C | 0x00000000 | Latched interrupt status |
| 0x024 | GPIO_RAW_INT | RO | 0 (live) | Live (unlatched) event detector output -- reads 0 at reset only because type/polarity/sync all reset to 0; depends on pins thereafter |
| 0x028 | GPIO_OUTPUT_SET | WO | 0x00000000 | Atomic output set (reads return 0) |
| 0x02C | GPIO_OUTPUT_CLR | WO | 0x00000000 | Atomic output clear (reads return 0) |
| 0x030 | GPIO_OUTPUT_TGL | WO | 0x00000000 | Atomic output toggle (reads return 0) |

**Address decode and aliasing:** only address bits [5:0] reach the register
block (`gpio_config_regs.sv` passes `regblk_addr[5:0]`), so the 13-register
map aliases every 64 bytes across the 4KB APB window. Offsets 0x034-0x03F
within each 64-byte tile are unmapped and read as zero; no access ever raises
PSLVERR.

---

## GPIO_CONTROL (0x000)

Global control register.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 31:2 | Reserved | RO | 0 | Reserved |
| 1 | INT_ENABLE | RW | 0 | Global interrupt enable. Gates the `irq` output: `irq = INT_ENABLE && (any effective pending interrupt)`. Resets to 0, so no interrupt asserts until software sets this bit. |
| 0 | ENABLE | RW | 1 | GPIO output enable. Gates only `gpio_oe`: when 0, every pin is high-Z regardless of GPIO_DIRECTION. Output data, input synchronization, and interrupt detection are unaffected. Resets to 1 (enabled). |

---

## GPIO_DIRECTION (0x004)

Pin direction control. Each bit controls one GPIO pin.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 31:0 | DIR | RW | 0 | Direction per pin (0=input, 1=output) |

---

## GPIO_OUTPUT (0x008)

Output data register. Values driven when pin configured as output.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 31:0 | DATA | RW | 0 | Output values per pin |

**Readback:** reads return the live output latch (`r_output_data` in
`gpio_core.sv`), not merely the last value software wrote. After any atomic
operation (GPIO_OUTPUT_SET/CLR/TGL) the core writes its latch back into this
register one cycle later, so the register and the pins stay in agreement:
write 0xFF here, then 0x0F to GPIO_OUTPUT_CLR, and a read returns 0xF0. A
read-modify-write of GPIO_OUTPUT therefore mixes safely with the atomic
registers. The write itself is strobe-driven, so writing the value the
register already holds still lands, and a software write wins over a
coincident hardware write-back.

---

## GPIO_INPUT (0x00C)

Input data register. Reflects synchronized external pin values.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 31:0 | DATA | RO | - | Input values per pin |

**Note:** Value depends on external signals, not reset.

---

## GPIO_INT_ENABLE (0x010)

Interrupt enable register. Controls which pins can generate interrupts.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 31:0 | IE | RW | 0 | Interrupt enable per pin (1=enabled) |

---

## GPIO_INT_TYPE (0x014)

Interrupt type select. Chooses edge or level sensitivity.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 31:0 | TYPE | RW | 0 | Type per pin (0=edge, 1=level) |

---

## GPIO_INT_POLARITY (0x018)

Interrupt polarity select.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 31:0 | POL | RW | 0xFFFFFFFF | Polarity per pin (resets to all rising/active-high) |

For edge mode: 0=falling, 1=rising
For level mode: 0=active-low, 1=active-high

---

## GPIO_INT_BOTH (0x01C)

Both-edge interrupt enable. Only applicable in edge mode.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 31:0 | BOTH | RW | 0 | Both edges per pin (1=both edges) |

When set, GPIO_INT_POLARITY is ignored for that pin.

---

## GPIO_INT_STATUS (0x020)

Latched interrupt status register.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 31:0 | STATUS | W1C | 0 | Latched interrupt event per pin |

**Access:** Read returns current status. Write 1 clears the bit.

**Semantics (per the RTL):**

- A bit sets only when the event occurs while that pin's GPIO_INT_ENABLE bit
  is 1 (`sts_int_pending = raw & enable`, `gpio_core.sv`). Events on disabled
  pins set nothing.
- Bits latch (stay set) until written-1-to-clear, in both edge and level
  modes. In level mode the bit remains set after the input level clears.
- The `irq` output uses this register only for edge-mode pins. Level-mode
  pins drive `irq` from the live detector output, so W1C on a level pin does
  not deassert `irq` while the level persists (see Chapter 3.3).
- A W1C write that lands in the same cycle as a new hardware event is merged
  per bit, `next = (value | hw_set) & ~w1c_mask`: bits the write is not
  clearing keep the coincident event (`gpio_config_regs.sv` holds the set in
  a one-cycle deferred-set register and applies it once the write completes),
  and a bit the write IS clearing is cleared, as in any W1C register. No
  event is lost on a bit software did not ask to clear.

---

## GPIO_RAW_INT (0x024)

Live event-detector output, before per-pin enable gating and latching.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 31:0 | RAW | RO | 0 | Raw interrupt condition per pin |

Reflects the edge/level detector output combinationally; not affected by
GPIO_INT_ENABLE, GPIO_CONTROL, or W1C.

---

## GPIO_OUTPUT_SET (0x028)

Atomic output set: writing 1 to a bit sets the corresponding output pin
without a read-modify-write of GPIO_OUTPUT.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 31:0 | SET | WO | 0 | Set output pins (1=set); reads return 0 |

---

## GPIO_OUTPUT_CLR (0x02C)

Atomic output clear.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 31:0 | CLR | WO | 0 | Clear output pins (1=clear); reads return 0 |

---

## GPIO_OUTPUT_TGL (0x030)

Atomic output toggle.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 31:0 | TGL | WO | 0 | Toggle output pins (1=toggle); reads return 0 |

---

## Design Notes

### Atomic-Register Write Semantics (SET/CLR/TGL)

Every write performs the operation, driven by the register's write strobe
(`gpio_config_regs.sv`). The regblock exports `swmod` for each register; it
is a level held for the whole command-bridge transaction and it leads the
field storage by one cycle, so the wrapper takes its rising edge (one write,
one event), delays it one flop to line up with the stored mask, and gates
the mask with that one-cycle strobe to form the pulse gpio_core acts on:

```
assign w_set_wr_event = w_set_swmod & ~r_set_swmod_d;   // rising edge
r_set_stb <= w_set_wr_event;                            // align to field
assign w_output_set = r_set_stb ? GPIO_OUTPUT_SET.set_bits.value : '0;
```

SystemRDL restricts `singlepulse` to 1-bit fields, which is why the 32-bit
masks are pulsed this way rather than self-clearing.

What software can rely on:

- Writing the same mask twice performs the operation twice. A toggle loop
  writing `GPIO_OUTPUT_TGL = mask` each iteration toggles on every pass.
- Alternating SET and CLR of the same mask performs every operation; nothing
  needs to be written in between, and no software shadow of the mask is
  needed.
- The registers are write-only by design (the RDL declares sw = w): reads
  at 0x028/0x02C/0x030 return 0. The result of an operation is observable
  in GPIO_OUTPUT, which reads back the live latch.

These are the conventional set/clear/toggle semantics (fixed 2026-09-08,
issue #44).

### Address Calculation

For system address:
```
Register_Address = BASE_ADDR + WINDOW_OFFSET + Register_Offset

Where:
  BASE_ADDR = 0xFEC00000 (RLB base)
  WINDOW_OFFSET = 0x7000 (GPIO window)
  Register_Offset = value from table above

Example:
  GPIO_INPUT = 0xFEC00000 + 0x7000 + 0x00C = 0xFEC0700C
```

---

## Navigation

**Back to:** [GPIO Specification Index](../gpio_mas_index.md)
