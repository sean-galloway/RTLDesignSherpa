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
APB → apb4_slave[_cdc] → CMD/RSP → peakrdl_to_cmdrsp →
    → gpio_regs (PeakRDL) → hwif → gpio_core
```

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| GPIO_WIDTH | 32 | GPIO port width |
| SYNC_STAGES | 2 | Input synchronizer stages |
| CDC_ENABLE | 0 | 1=async clocks, 0=same clock |
| SKID_DEPTH | 2 | CDC skid buffer depth |

The APB port is fixed at 32-bit data / 12-bit address (localparams in
`apb4_gpio.sv`); there are no APB width parameters.

## Register Map

Thirteen 32-bit registers at word offsets 0x000-0x030. The authoritative map,
field definitions, and software caveats (atomic-register change detection,
GPIO_OUTPUT readback) live in the MAS register chapter:
`docs/gpio_mas/ch05_registers/01_register_map.md`. An earlier revision of
this README carried a 16-bit LO/HI split map that never matched the RTL.

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
│   └── gpio_regs.rdl      # PeakRDL register definitions
├── filelists/
│   └── apb4_gpio.f         # Simulation/synthesis filelist
├── gpio_regs_pkg.sv       # PeakRDL generated package
├── gpio_regs.sv           # PeakRDL generated registers
├── gpio_core.sv           # GPIO I/O logic and interrupts
├── gpio_config_regs.sv    # Register-to-core adapter
├── apb4_gpio.sv            # APB wrapper (top level)
└── README.md              # This file
```

## Dependencies

- apb4_slave.sv / apb4_slave_cdc.sv
- peakrdl_to_cmdrsp.sv
- gaxi_skid_buffer.sv (for CDC)
- cdc_handshake.sv (for CDC)

## Test Plan

Tests located in: `projects/components/retro_legacy_blocks/dv/tests/test_apb4_gpio.py`

| Test Level | Description |
|------------|-------------|
| basic | Register access, direction control, basic I/O |
| medium | Interrupt modes, edge detection, atomic ops |
| full | CDC configurations, stress testing, corner cases |
