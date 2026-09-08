# Digilent Nexys A7-100T Board Information

**Complete reference for Nexys A7-100T FPGA development board**

---

## Board Specifications

### FPGA Device

| Specification | Value |
|--------------|-------|
| **Device** | Xilinx Artix-7 XC7A100T-1CSG324C |
| **Package** | CSG324 (324-ball BGA) |
| **Speed Grade** | -1 (standard) |
| **Logic Cells** | 101,440 |
| **LUTs** | 63,400 |
| **Flip-Flops** | 126,800 |
| **Block RAM** | 4,860 Kb (135 blocks) |
| **DSP Slices** | 240 |
| **I/O Pins** | 210 |

### Board Resources

| Component | Specification | Quantity |
|-----------|--------------|----------|
| **Clock** | 100 MHz oscillator | 1 |
| **RAM** | 128 Mb DDR2 | 1 |
| **Flash** | 128 Mb Quad-SPI | 1 |
| **USB** | Digilent USB-JTAG | 1 |
| **Ethernet** | 10/100 Ethernet PHY | 1 |
| **Audio** | PWM audio out | 1 |
| **VGA** | 12-bit VGA port | 1 |
| **Buttons** | Push buttons | 5 |
| **Switches** | Slide switches | 16 |
| **LEDs** | Standard LEDs | 16 |
| **RGB LEDs** | Tri-color LEDs | 2 |
| **7-Segment** | 8-digit display | 1 |
| **PMOD** | 4x12-pin headers | 4 |
| **USB Host** | USB HID Host | 1 |

---

## Pin Assignments Reference

### System Clock

```tcl
## 100 MHz Clock
set_property -dict {PACKAGE_PIN E3 IOSTANDARD LVCMOS33} [get_ports CLK100MHZ]
create_clock -period 10.000 -name sys_clk_pin -waveform {0.000 5.000} [get_ports CLK100MHZ]
```

### Buttons (Active-High)

```tcl
set_property -dict {PACKAGE_PIN E16 IOSTANDARD LVCMOS33} [get_ports btnC]  # Center
set_property -dict {PACKAGE_PIN F15 IOSTANDARD LVCMOS33} [get_ports btnU]  # Up
set_property -dict {PACKAGE_PIN T16 IOSTANDARD LVCMOS33} [get_ports btnL]  # Left
set_property -dict {PACKAGE_PIN R10 IOSTANDARD LVCMOS33} [get_ports btnR]  # Right
set_property -dict {PACKAGE_PIN V10 IOSTANDARD LVCMOS33} [get_ports btnD]  # Down
set_property -dict {PACKAGE_PIN N17 IOSTANDARD LVCMOS33} [get_ports CPU_RESETN]  # CPU Reset (active-low)
```

### Slide Switches (16)

```tcl
set_property -dict {PACKAGE_PIN J15 IOSTANDARD LVCMOS33} [get_ports {sw[0]}]
set_property -dict {PACKAGE_PIN L16 IOSTANDARD LVCMOS33} [get_ports {sw[1]}]
set_property -dict {PACKAGE_PIN M13 IOSTANDARD LVCMOS33} [get_ports {sw[2]}]
set_property -dict {PACKAGE_PIN R15 IOSTANDARD LVCMOS33} [get_ports {sw[3]}]
set_property -dict {PACKAGE_PIN R17 IOSTANDARD LVCMOS33} [get_ports {sw[4]}]
set_property -dict {PACKAGE_PIN T18 IOSTANDARD LVCMOS33} [get_ports {sw[5]}]
set_property -dict {PACKAGE_PIN U18 IOSTANDARD LVCMOS33} [get_ports {sw[6]}]
set_property -dict {PACKAGE_PIN R13 IOSTANDARD LVCMOS33} [get_ports {sw[7]}]
set_property -dict {PACKAGE_PIN T8  IOSTANDARD LVCMOS18} [get_ports {sw[8]}]
set_property -dict {PACKAGE_PIN U8  IOSTANDARD LVCMOS18} [get_ports {sw[9]}]
set_property -dict {PACKAGE_PIN R16 IOSTANDARD LVCMOS33} [get_ports {sw[10]}]
set_property -dict {PACKAGE_PIN T13 IOSTANDARD LVCMOS33} [get_ports {sw[11]}]
set_property -dict {PACKAGE_PIN H6  IOSTANDARD LVCMOS33} [get_ports {sw[12]}]
set_property -dict {PACKAGE_PIN U12 IOSTANDARD LVCMOS33} [get_ports {sw[13]}]
set_property -dict {PACKAGE_PIN U11 IOSTANDARD LVCMOS33} [get_ports {sw[14]}]
set_property -dict {PACKAGE_PIN V10 IOSTANDARD LVCMOS33} [get_ports {sw[15]}]
```

### LEDs (16)

```tcl
set_property -dict {PACKAGE_PIN H17 IOSTANDARD LVCMOS33} [get_ports {led[0]}]
set_property -dict {PACKAGE_PIN K15 IOSTANDARD LVCMOS33} [get_ports {led[1]}]
set_property -dict {PACKAGE_PIN J13 IOSTANDARD LVCMOS33} [get_ports {led[2]}]
set_property -dict {PACKAGE_PIN N14 IOSTANDARD LVCMOS33} [get_ports {led[3]}]
set_property -dict {PACKAGE_PIN R18 IOSTANDARD LVCMOS33} [get_ports {led[4]}]
set_property -dict {PACKAGE_PIN V17 IOSTANDARD LVCMOS33} [get_ports {led[5]}]
set_property -dict {PACKAGE_PIN U17 IOSTANDARD LVCMOS33} [get_ports {led[6]}]
set_property -dict {PACKAGE_PIN U16 IOSTANDARD LVCMOS33} [get_ports {led[7]}]
set_property -dict {PACKAGE_PIN V16 IOSTANDARD LVCMOS33} [get_ports {led[8]}]
set_property -dict {PACKAGE_PIN T15 IOSTANDARD LVCMOS33} [get_ports {led[9]}]
set_property -dict {PACKAGE_PIN U14 IOSTANDARD LVCMOS33} [get_ports {led[10]}]
set_property -dict {PACKAGE_PIN T16 IOSTANDARD LVCMOS33} [get_ports {led[11]}]
set_property -dict {PACKAGE_PIN V15 IOSTANDARD LVCMOS33} [get_ports {led[12]}]
set_property -dict {PACKAGE_PIN V14 IOSTANDARD LVCMOS33} [get_ports {led[13]}]
set_property -dict {PACKAGE_PIN V12 IOSTANDARD LVCMOS33} [get_ports {led[14]}]
set_property -dict {PACKAGE_PIN V11 IOSTANDARD LVCMOS33} [get_ports {led[15]}]
```

### RGB LEDs (2)

```tcl
## RGB LED 16
set_property -dict {PACKAGE_PIN R12 IOSTANDARD LVCMOS33} [get_ports led16_r]
set_property -dict {PACKAGE_PIN M16 IOSTANDARD LVCMOS33} [get_ports led16_g]
set_property -dict {PACKAGE_PIN N15 IOSTANDARD LVCMOS33} [get_ports led16_b]

## RGB LED 17
set_property -dict {PACKAGE_PIN G14 IOSTANDARD LVCMOS33} [get_ports led17_r]
set_property -dict {PACKAGE_PIN R11 IOSTANDARD LVCMOS33} [get_ports led17_g]
set_property -dict {PACKAGE_PIN N16 IOSTANDARD LVCMOS33} [get_ports led17_b]
```

### 7-Segment Display (8 Digits)

**Segments (Active-Low):**
```tcl
set_property -dict {PACKAGE_PIN L3 IOSTANDARD LVCMOS33} [get_ports {seg[0]}]  # CA
set_property -dict {PACKAGE_PIN N1 IOSTANDARD LVCMOS33} [get_ports {seg[1]}]  # CB
set_property -dict {PACKAGE_PIN L5 IOSTANDARD LVCMOS33} [get_ports {seg[2]}]  # CC
set_property -dict {PACKAGE_PIN L4 IOSTANDARD LVCMOS33} [get_ports {seg[3]}]  # CD
set_property -dict {PACKAGE_PIN K3 IOSTANDARD LVCMOS33} [get_ports {seg[4]}]  # CE
set_property -dict {PACKAGE_PIN M2 IOSTANDARD LVCMOS33} [get_ports {seg[5]}]  # CF
set_property -dict {PACKAGE_PIN L6 IOSTANDARD LVCMOS33} [get_ports {seg[6]}]  # CG
set_property -dict {PACKAGE_PIN M4 IOSTANDARD LVCMOS33} [get_ports dp]        # DP
```

**Anodes (Active-Low):**
```tcl
set_property -dict {PACKAGE_PIN N6 IOSTANDARD LVCMOS33} [get_ports {an[7]}]  # AN7 (leftmost)
set_property -dict {PACKAGE_PIN M6 IOSTANDARD LVCMOS33} [get_ports {an[6]}]  # AN6
set_property -dict {PACKAGE_PIN M3 IOSTANDARD LVCMOS33} [get_ports {an[5]}]  # AN5
set_property -dict {PACKAGE_PIN N5 IOSTANDARD LVCMOS33} [get_ports {an[4]}]  # AN4
set_property -dict {PACKAGE_PIN N2 IOSTANDARD LVCMOS33} [get_ports {an[3]}]  # AN3
set_property -dict {PACKAGE_PIN N4 IOSTANDARD LVCMOS33} [get_ports {an[2]}]  # AN2
set_property -dict {PACKAGE_PIN L1 IOSTANDARD LVCMOS33} [get_ports {an[1]}]  # AN1
set_property -dict {PACKAGE_PIN M4 IOSTANDARD LVCMOS33} [get_ports {an[0]}]  # AN0 (rightmost)
```

---

## Complete Master XDC Template

See: `boards/nexys_a7_100t/master.xdc`

---

## Voltage Standards

| Bank | Voltage | Standard | Use |
|------|---------|----------|-----|
| Bank 0 | 1.8V | LVCMOS18 | Configuration |
| Bank 14 | 3.3V | LVCMOS33 | General I/O |
| Bank 15 | 3.3V | LVCMOS33 | General I/O |
| Bank 16 | 3.3V | LVCMOS33 | General I/O |
| Bank 34 | 3.3V | LVCMOS33 | DDR2 |
| Bank 35 | 1.5V | SSTL15 | DDR2 |

---

## Board Part File

**Vivado Board Part:**
```
digilentinc.com:nexys-a7-100t:part0:1.3
```

**Installation:**
- Download from [Digilent Board Files](https://github.com/Digilent/vivado-boards)
- Install to `<Vivado>/data/boards/board_files/`

---

## Power Supply

| Rail | Voltage | Current | Source |
|------|---------|---------|--------|
| VADJ | 3.3V | - | Adjustable via jumper |
| VCC | 3.3V | - | Main supply |
| VCCINT | 1.0V | - | FPGA core |
| VCCAUX | 1.8V | - | FPGA auxiliary |

**Power Input:** USB (5V) or External (7-15V DC)

---

## Configuration

**Programming Modes:**
- JTAG (via USB)
- Quad-SPI Flash (persistent)

**Bitstream Options:**
- Compressed bitstream recommended
- SPI x4 mode (fastest)
- 33 MHz configuration rate

**Standard Settings:**
```tcl
set_property CONFIG_VOLTAGE 3.3 [current_design]
set_property CFGBVS VCCO [current_design]
set_property BITSTREAM.GENERAL.COMPRESS TRUE [current_design]
set_property BITSTREAM.CONFIG.CONFIGRATE 33 [current_design]
set_property BITSTREAM.CONFIG.SPI_BUSWIDTH 4 [current_design]
```

---

## Common Pitfalls

### 1. Mixed Voltage Banks
❌ **Don't** mix 1.8V and 3.3V signals in same bank
✅ **Do** use appropriate IOSTANDARD per bank

### 2. Button Debouncing
❌ **Don't** use buttons directly in critical logic
✅ **Do** implement proper debouncing (see rtl/common/debounce.sv)

### 3. 7-Segment Display
❌ **Don't** drive all anodes simultaneously (static)
✅ **Do** multiplex anodes (time-division)

### 4. Clock Constraints
❌ **Don't** forget to constrain generated clocks
✅ **Do** use `create_generated_clock` for divided clocks

---

## Resources

**Official:**
- [Nexys A7 Reference Manual](https://reference.digilentinc.com/reference/programmable-logic/nexys-a7/reference-manual)
- [Nexys A7 Schematic](https://reference.digilentinc.com/_media/reference/programmable-logic/nexys-a7/nexys-a7-d2-sch.pdf)
- [Digilent Board Files](https://github.com/Digilent/vivado-boards)

**Community:**
- [Digilent Forum](https://forum.digilentinc.com/)
- [Xilinx Forums](https://forums.xilinx.com/)

---

## Revision History

| Version | Date | Changes |
|---------|------|---------|
| 1.0 | 2025-10-15 | Initial board info |

---

**Board:** Digilent Nexys A7-100T
**Part Number:** 410-352
**Manufacturer:** Digilent Inc.
