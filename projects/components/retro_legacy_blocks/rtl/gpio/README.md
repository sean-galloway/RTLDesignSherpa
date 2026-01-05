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

# APB GPIO Controller

FPGA-friendly General Purpose I/O controller with APB interface.

## Features

- 32-bit GPIO port
- Per-bit direction control (input/output)
- 2-stage input synchronization for metastability protection
- Edge and level interrupt support
  - Rising edge, falling edge, or both edges
  - High or low level sensitive
- Per-pin interrupt enable and status
- Atomic set/clear/toggle operations
- Optional CDC for asynchronous clock domains
- W1C (Write-1-to-Clear) interrupt status

## Architecture

```
APB → apb_slave[_cdc] → CMD/RSP → peakrdl_to_cmdrsp →
    → gpio_regs (PeakRDL) → hwif → gpio_core
```

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| GPIO_WIDTH | 32 | GPIO port width |
| SYNC_STAGES | 2 | Input synchronizer stages |
| APB_ADDR_WIDTH | 16 | APB address width |
| APB_DATA_WIDTH | 16 | APB data width |
| CDC_ENABLE | 0 | 1=async clocks, 0=same clock |
| SKID_DEPTH | 2 | CDC skid buffer depth |

## Register Map

| Offset | Register | Access | Description |
|--------|----------|--------|-------------|
| 0x000 | GPIO_CONTROL | RW | Global enable, interrupt enable |
| 0x004 | GPIO_DIRECTION_LO | RW | Direction [15:0] (1=out, 0=in) |
| 0x006 | GPIO_DIRECTION_HI | RW | Direction [31:16] |
| 0x008 | GPIO_OUTPUT_LO | RW | Output data [15:0] |
| 0x00A | GPIO_OUTPUT_HI | RW | Output data [31:16] |
| 0x00C | GPIO_INPUT_LO | RO | Input data [15:0] |
| 0x00E | GPIO_INPUT_HI | RO | Input data [31:16] |
| 0x010 | GPIO_INT_ENABLE_LO | RW | Interrupt enable [15:0] |
| 0x012 | GPIO_INT_ENABLE_HI | RW | Interrupt enable [31:16] |
| 0x014 | GPIO_INT_TYPE_LO | RW | 1=level, 0=edge [15:0] |
| 0x016 | GPIO_INT_TYPE_HI | RW | 1=level, 0=edge [31:16] |
| 0x018 | GPIO_INT_POLARITY_LO | RW | 1=high/rising, 0=low/falling [15:0] |
| 0x01A | GPIO_INT_POLARITY_HI | RW | 1=high/rising, 0=low/falling [31:16] |
| 0x01C | GPIO_INT_BOTH_LO | RW | 1=both edges [15:0] |
| 0x01E | GPIO_INT_BOTH_HI | RW | 1=both edges [31:16] |
| 0x020 | GPIO_INT_STATUS_LO | RW/W1C | Interrupt status [15:0] |
| 0x022 | GPIO_INT_STATUS_HI | RW/W1C | Interrupt status [31:16] |
| 0x024 | GPIO_RAW_INT_LO | RO | Raw interrupt (pre-mask) [15:0] |
| 0x026 | GPIO_RAW_INT_HI | RO | Raw interrupt (pre-mask) [31:16] |
| 0x028 | GPIO_OUTPUT_SET_LO | WO | Atomic set [15:0] |
| 0x02A | GPIO_OUTPUT_SET_HI | WO | Atomic set [31:16] |
| 0x02C | GPIO_OUTPUT_CLR_LO | WO | Atomic clear [15:0] |
| 0x02E | GPIO_OUTPUT_CLR_HI | WO | Atomic clear [31:16] |
| 0x030 | GPIO_OUTPUT_TGL_LO | WO | Atomic toggle [15:0] |
| 0x032 | GPIO_OUTPUT_TGL_HI | WO | Atomic toggle [31:16] |

## FPGA Integration

The gpio_in/gpio_out/gpio_oe signals should be connected to IOBUF primitives at the FPGA top level:

```systemverilog
// Xilinx IOBUF instantiation example
IOBUF u_iobuf[31:0] (
    .IO    (gpio_pins),      // Bidirectional pad
    .O     (gpio_in),        // Input path (to this module)
    .I     (gpio_out),       // Output path (from this module)
    .T     (~gpio_oe)        // Tristate control (active low for IOBUF)
);
```

For Intel/Altera FPGAs:

```systemverilog
// Intel ALTBIDIR instantiation example
altbidir u_altbidir[31:0] (
    .padio     (gpio_pins),
    .datain    (gpio_out),
    .dataout   (gpio_in),
    .oe        (gpio_oe)
);
```

## Interrupt Modes

### Edge-Sensitive (INT_TYPE = 0)
- **Rising edge** (POLARITY=1, BOTH=0): Interrupt on 0→1 transition
- **Falling edge** (POLARITY=0, BOTH=0): Interrupt on 1→0 transition
- **Both edges** (BOTH=1): Interrupt on any transition

### Level-Sensitive (INT_TYPE = 1)
- **High level** (POLARITY=1): Interrupt while pin is high
- **Low level** (POLARITY=0): Interrupt while pin is low

## Atomic Operations

The SET/CLR/TGL registers provide atomic bit manipulation without read-modify-write:

```c
// Set GPIO[5] high (atomic)
write(GPIO_OUTPUT_SET_LO, 0x0020);

// Clear GPIO[5] low (atomic)
write(GPIO_OUTPUT_CLR_LO, 0x0020);

// Toggle GPIO[5] (atomic)
write(GPIO_OUTPUT_TGL_LO, 0x0020);
```

## File Structure

```
gpio/
├── peakrdl/
│   └── gpio_regs.rdl      # PeakRDL register definitions
├── filelists/
│   └── apb_gpio.f         # Simulation/synthesis filelist
├── gpio_regs_pkg.sv       # PeakRDL generated package
├── gpio_regs.sv           # PeakRDL generated registers
├── gpio_core.sv           # GPIO I/O logic and interrupts
├── gpio_config_regs.sv    # Register-to-core adapter
├── apb_gpio.sv            # APB wrapper (top level)
└── README.md              # This file
```

## Dependencies

- apb_slave.sv / apb_slave_cdc.sv
- peakrdl_to_cmdrsp.sv
- gaxi_skid_buffer.sv (for CDC)
- cdc_handshake.sv (for CDC)

## Test Plan

Tests located in: `projects/components/retro_legacy_blocks/dv/tests/test_apb_gpio.py`

| Test Level | Description |
|------------|-------------|
| basic | Register access, direction control, basic I/O |
| medium | Interrupt modes, edge detection, atomic ops |
| full | CDC configurations, stress testing, corner cases |
