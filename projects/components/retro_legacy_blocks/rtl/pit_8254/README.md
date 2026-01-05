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

# Intel 8254 PIT (Programmable Interval Timer) - APB Implementation

**Status:** ✅ Basic Implementation Complete (Mode 0)
**Priority:** High
**Address:** `0x4000_2000 - 0x4000_2FFF` (4KB window)

---

## Overview

APB-based implementation of Intel 8254-compatible Programmable Interval Timer with 3 independent 16-bit counters.

Follows HPET 3-layer architecture pattern with PeakRDL-generated registers.

## Features

- ✅ Intel 8254-compatible register interface
- ✅ 3 independent 16-bit counters
- ✅ Mode 0: Interrupt on terminal count (implemented)
- ⏳ Modes 1-5 (planned)
- ✅ Binary and BCD counting
- ✅ LSB/MSB/both byte access modes
- ⏳ Read-back command (planned)
- ✅ Configurable clock input
- ✅ Interrupt output array: `timer_irq[2:0]`
- ✅ APB4 slave interface
- ✅ Optional CDC (clock domain crossing)

## Architecture

![PIT 8254 Architecture](docs/assets/graphviz/pit_architecture.png)

*Figure 1: PIT 8254 module architecture showing APB interface, PeakRDL-generated registers, and 3 independent counter channels with Mode 0 implementation.*

### Module Hierarchy

```
apb_pit_8254.sv         → APB wrapper, CDC support
  ├── pit_config_regs.sv → Register wrapper, edge detection
  │     └── pit_regs.sv  → PeakRDL generated registers
  └── pit_core.sv        → 3-counter array, control decode
        └── pit_counter.sv → Single counter (mode 0)
```

## Register Map

| Address | Register        | Access | Description                           |
|---------|-----------------|--------|---------------------------------------|
| 0x000   | PIT_CONFIG      | RW     | Global config (enable, clock select)  |
| 0x004   | PIT_CONTROL     | WO     | Control word (8254-compatible)        |
| 0x008   | PIT_STATUS      | RO     | Read-back status (3×8-bit)            |
| 0x00C   | RESERVED        | RO     | Reserved                              |
| 0x010   | COUNTER0_DATA   | RW     | Counter 0 value (16-bit)              |
| 0x014   | COUNTER1_DATA   | RW     | Counter 1 value (16-bit)              |
| 0x018   | COUNTER2_DATA   | RW     | Counter 2 value (16-bit)              |

## Counter Modes

| Mode | Name                          | Status       |
|------|-------------------------------|--------------|
| 0    | Interrupt on terminal count   | ✅ Complete  |
| 1    | Hardware retriggerable one-shot | ⏳ TODO     |
| 2    | Rate generator                | ⏳ TODO      |
| 3    | Square wave generator         | ⏳ TODO      |
| 4    | Software triggered strobe     | ⏳ TODO      |
| 5    | Hardware triggered strobe     | ⏳ TODO      |

## Interrupt Outputs

Following HPET pattern:
- `timer_irq[0]` = Counter 0 OUT (system timer, IRQ0)
- `timer_irq[1]` = Counter 1 OUT (DRAM refresh or general)
- `timer_irq[2]` = Counter 2 OUT (PC speaker or general)

## Example Instantiation

```systemverilog
apb_pit_8254 #(
    .NUM_COUNTERS(3),
    .CDC_ENABLE(0)
) u_pit (
    .pclk         (apb_clk),
    .presetn      (apb_rst_n),
    .paddr        (paddr),
    .psel         (psel_pit),
    .penable      (penable),
    .pwrite       (pwrite),
    .pwdata       (pwdata),
    .prdata       (prdata_pit),
    .pready       (pready_pit),
    .pslverr      (pslverr_pit),
    .pit_clk      (timer_clk),
    .pit_rst      (timer_rst),
    .gate_in      (gate[2:0]),
    .timer_irq    (pit_irq[2:0])
);
```

## Files

- ✅ `apb_pit_8254.sv` - Top-level APB wrapper
- ✅ `pit_config_regs.sv` - Register wrapper with edge detection
- ✅ `pit_core.sv` - 3-counter array
- ✅ `pit_counter.sv` - Single counter (mode 0)
- ✅ `pit_regs.sv` - PeakRDL generated registers
- ✅ `pit_regs_pkg.sv` - PeakRDL generated package
- ✅ `peakrdl/pit_regs.rdl` - SystemRDL specification

## Development Status

- [x] SystemRDL register specification
- [x] PeakRDL register generation
- [x] Counter mode 0 logic implementation
- [x] Core PIT logic (3-counter array)
- [x] APB wrapper
- [ ] Modes 1-5 implementation
- [ ] Basic testbench
- [ ] Medium testbench
- [ ] Full testbench
- [ ] Read-back command support

## Compliance

- ✅ Reset macros (`ALWAYS_FF_RST`)
- ✅ HPET architecture pattern
- ✅ APB4 standard interface
- ✅ PeakRDL register generation

---

**Last Updated:** 2025-11-06
**Status:** Mode 0 complete, ready for testing
