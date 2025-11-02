# Nexys A7 Board Support Files

This directory contains board-specific reference files for Digilent Nexys A7 FPGA development boards.

---

## Directory Structure

```
boards/
└── nexys_a7_100t/              # Nexys A7-100T (XC7A100T)
    ├── board_info.md           # Complete board specifications
    ├── master.xdc              # Master constraints template
    └── README.md               # Board-specific notes
```

---

## Supported Boards

### Nexys A7-100T

**FPGA:** Xilinx Artix-7 XC7A100T-1CSG324C

**Key Resources:**
- 63,400 LUTs
- 126,800 Flip-Flops
- 135 Block RAMs (4,860 Kb)
- 240 DSP Slices

**Peripherals:**
- 100 MHz clock
- 16 switches, 5 buttons
- 16 LEDs, 2 RGB LEDs
- 8-digit 7-segment display
- VGA connector (12-bit color)
- USB-UART
- 10/100 Ethernet
- 128 MB DDR2 SDRAM
- 4x PMOD headers

**Documentation:** See `nexys_a7_100t/board_info.md`

---

## Using Board Files

### 1. Master Constraints Template

The `master.xdc` file contains **all** pin assignments for the Nexys A7-100T board.

**Usage:**
1. Copy `master.xdc` to your project's `constraints/` directory
2. Rename to match your project (e.g., `my_project.xdc`)
3. Uncomment only the pins you need
4. Add your project-specific timing constraints

**Example:**
```tcl
## Uncomment clock
set_property -dict {PACKAGE_PIN E3 IOSTANDARD LVCMOS33} [get_ports CLK100MHZ]
create_clock -period 10.000 -name sys_clk_pin [get_ports CLK100MHZ]

## Uncomment buttons
set_property -dict {PACKAGE_PIN E16 IOSTANDARD LVCMOS33} [get_ports btnC]

## Uncomment LEDs (just led[0] and led[1])
set_property -dict {PACKAGE_PIN H17 IOSTANDARD LVCMOS33} [get_ports {led[0]}]
set_property -dict {PACKAGE_PIN K15 IOSTANDARD LVCMOS33} [get_ports {led[1]}]
```

### 2. Board Information

The `board_info.md` file provides:
- Complete pin assignments (tables)
- Voltage standards by bank
- Common pitfalls and solutions
- Resource links
- Configuration settings

**Usage:**
- Reference during design
- Copy pin assignment snippets
- Verify voltage standards
- Troubleshooting guide

---

## Quick Reference

### Common Pin Groups

| Component | Pins | File Section |
|-----------|------|--------------|
| **Clock** | E3 | Clock Signals |
| **Buttons** | E16, F15, T16, R10, V10 | Push Buttons |
| **Switches** | J15..V10 (16 total) | Slide Switches |
| **LEDs** | H17..V11 (16 total) | LEDs |
| **7-Segment** | L3..M4 (segments), N6..M4 (anodes) | 7-Segment Display |
| **VGA** | A3..B12 | VGA Connector |
| **UART** | C4, D4 | USB-UART |
| **Ethernet** | D17..G18 | Ethernet |
| **PMOD JA-JD** | C17..F3 | PMOD Headers |

### Voltage Standards

| Component | IOSTANDARD |
|-----------|-----------|
| Most I/O | LVCMOS33 |
| Switches 8-9 | LVCMOS18 |
| Configuration | See board_info.md |

### Configuration Settings

**Always include in your XDC:**
```tcl
set_property CONFIG_VOLTAGE 3.3 [current_design]
set_property CFGBVS VCCO [current_design]
set_property BITSTREAM.GENERAL.COMPRESS TRUE [current_design]
set_property BITSTREAM.CONFIG.CONFIGRATE 33 [current_design]
set_property BITSTREAM.CONFIG.SPI_BUSWIDTH 4 [current_design]
```

---

## Best Practices

### 1. Only Uncomment What You Use

❌ **Don't** uncomment entire master.xdc
```tcl
## This creates unnecessary constraints
set_property -dict {...} [get_ports {led[0]}]
set_property -dict {...} [get_ports {led[1]}]
# ... (14 more LEDs you're not using)
```

✅ **Do** uncomment only needed pins
```tcl
## Just the 2 LEDs we need
set_property -dict {...} [get_ports {led[0]}]
set_property -dict {...} [get_ports {led[1]}]
```

### 2. Match Port Names

Your RTL port names must match XDC port names:

**RTL:**
```systemverilog
module my_design (
    input  logic CLK100MHZ,  // Must match XDC
    input  logic btnC,       // Must match XDC
    output logic [1:0] led   // Must match XDC
);
```

**XDC:**
```tcl
set_property -dict {...} [get_ports CLK100MHZ]
set_property -dict {...} [get_ports btnC]
set_property -dict {...} [get_ports {led[0]}]
set_property -dict {...} [get_ports {led[1]}]
```

### 3. Debounce Buttons

All mechanical buttons require debouncing:

```systemverilog
// Use rtldesignsherpa debounce module
debounce #(
    .CLK_FREQ_MHZ(100),
    .DEBOUNCE_TIME_MS(20)
) u_debounce (
    .i_clk(CLK100MHZ),
    .i_rst_n(rst_n),
    .i_signal_raw(btnC),
    .o_signal_clean(btnC_debounced)
);
```

### 4. Constrain Clocks Properly

**System clock:**
```tcl
create_clock -period 10.000 -name sys_clk_pin [get_ports CLK100MHZ]
```

**Derived clocks:**
```tcl
create_generated_clock -name my_div_clk \
    -source [get_pins u_divider/i_clk] \
    -divide_by 1000 \
    [get_pins u_divider/o_clk_out]
```

---

## Common Issues

### Issue: "Port 'X' not found in design"

**Cause:** Port name mismatch between RTL and XDC

**Solution:** Verify port names match exactly (case-sensitive)

### Issue: "Multiple drivers for port 'X'"

**Cause:** Pin assigned multiple times in XDC

**Solution:** Remove duplicate assignments

### Issue: "Bank voltage conflict"

**Cause:** Mixing LVCMOS33 and LVCMOS18 in same bank

**Solution:** Check `board_info.md` for correct IOSTANDARD per bank

---

## Additional Resources

**Digilent:**
- [Nexys A7 Product Page](https://digilent.com/shop/nexys-a7-fpga-trainer-board-recommended-for-ece-curriculum/)
- [Reference Manual](https://reference.digilentinc.com/reference/programmable-logic/nexys-a7/reference-manual)
- [Schematic](https://reference.digilentinc.com/_media/reference/programmable-logic/nexys-a7/nexys-a7-d2-sch.pdf)

**Xilinx:**
- [Artix-7 Data Sheet](https://www.xilinx.com/support/documentation/data_sheets/ds181_Artix_7_Data_Sheet.pdf)
- [7 Series FPGAs Configuration User Guide](https://www.xilinx.com/support/documentation/user_guides/ug470_7Series_Config.pdf)

---

## Revision History

| Version | Date | Changes |
|---------|------|---------|
| 1.0 | 2025-10-15 | Initial board support |

---

**Maintainer:** RTL Design Sherpa Project
