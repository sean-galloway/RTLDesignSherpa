# Retro Legacy Blocks (RLB)

**Version:** 1.0
**Last Updated:** 2025-10-29
**Purpose:** Collection of production-quality legacy peripheral blocks

---

## Overview

This component contains production-quality implementations of legacy peripheral blocks, designed for use in systems requiring retro-compatible peripheral interfaces. The blocks are organized for easy integration with modern SoC designs.

**Current Blocks:**
- **HPET** - High Precision Event Timer (APB interface, `0x4000_0000-0x0FFF`)

**Future Blocks (Planned - RLB Address Map):**

**High Priority:**
- **8259 PIC** - Programmable Interrupt Controller (`0x4000_1000-0x1FFF`)
- **8254 PIT** - Programmable Interval Timer (`0x4000_2000-0x2FFF`)

**Medium Priority:**
- **RTC** - Real-Time Clock (`0x4000_3000-0x3FFF`)
- **SMBus** - System Management Bus Controller (`0x4000_4000-0x4FFF`)
- **PM/ACPI** - Power Management / ACPI Registers (`0x4000_5000-0x5FFF`)
- **IOAPIC** - I/O Advanced PIC (`0x4000_6000-0x6FFF`)
- GPIO - General Purpose I/O
- UART - Universal Asynchronous Receiver/Transmitter

**Low Priority:**
- SPI - Serial Peripheral Interface
- I2C - Inter-Integrated Circuit Controller
- Watchdog - Watchdog Timer
- **Interconnect** - ID/Version Registers (`0x4000_F000-0xFFFF`)

**RLB Wrapper:** Single APB slave entry point at `0x4000_0000` with 4KB window decode routing to individual blocks

---

## Directory Structure

```
retro_legacy_blocks/
├── rtl/                      # RTL organized by block
│   └── hpet/                # HPET RTL files
│       ├── apb_hpet.sv      # Top-level module
│       ├── hpet_core.sv     # Timer core logic
│       ├── hpet_config_regs.sv  # Register wrapper
│       ├── hpet_regs*.sv    # PeakRDL generated registers
│       ├── peakrdl/         # SystemRDL specifications
│       ├── filelists/       # Filelist configurations
│       └── Makefile         # Build targets
│
├── dv/                       # Design Verification
│   ├── tbclasses/           # Testbench classes (organized by block)
│   │   └── hpet/           # HPET testbench classes
│   │       ├── hpet_tb.py  # Main testbench
│   │       ├── hpet_tests_basic.py
│   │       ├── hpet_tests_medium.py
│   │       └── hpet_tests_full.py
│   ├── tests/              # Test runners (organized by block)
│   │   └── hpet/           # HPET tests
│   │       ├── test_apb_hpet.py
│   │       └── conftest.py
│   ├── components/         # Shared test components (if needed)
│   └── scoreboards/        # Shared scoreboards (if needed)
│
├── docs/                    # Documentation
│   └── hpet_spec/          # HPET specification
│
├── bin/                     # Tools and generators (block-specific)
│
├── known_issues/            # Issue tracking
│   ├── active/             # Open issues
│   └── resolved/           # Resolved issues
│
├── PRD.md                   # Product Requirements Document
├── CLAUDE.md                # AI assistant guide
├── TASKS.md                 # Task tracking
└── README.md                # This file
```

---

## Design Philosophy

### Block Organization

Each peripheral block is organized into separate subdirectories:

**RTL:**
- `rtl/{block}/` - All RTL for a specific block
- Keeps related files together
- Easy to package individual blocks
- Clear separation between different peripherals

**DV:**
- `dv/tbclasses/{block}/` - Testbench classes for each block
- `dv/tests/{block}/` - Test runners for each block
- Shared components/scoreboards at dv/ level (if truly shared across blocks)

### Why "Retro Legacy Blocks"?

- **Retro**: Implements proven architectures from older platforms
- **Legacy**: Based on time-tested peripheral interface specifications
- **Blocks**: Collection of independent peripheral blocks

This naming reflects that these are production-ready implementations of time-tested peripheral designs, not experimental or modern architectures.

---

## Current Status

### HPET (High Precision Event Timer)

**Status:** ✅ Production Ready
**Test Coverage:** 5/6 configurations at 100%, 1 at 92%
**Documentation:** Complete specification and test documentation

**Features:**
- Configurable number of timers (2, 3, or 8)
- 64-bit main counter
- One-shot and periodic timer modes
- APB4 interface
- Optional clock domain crossing (CDC)
- PeakRDL-generated register file

**See:** `docs/hpet_spec/` for complete specification

---

## Adding New Blocks

### Template Structure

When adding a new legacy block (e.g., GPIO):

1. **Create RTL directory:**
   ```bash
   mkdir -p rtl/gpio
   cd rtl/gpio
   # Add RTL files: apb_gpio.sv, gpio_core.sv, etc.
   ```

2. **Create testbench classes:**
   ```bash
   mkdir -p dv/tbclasses/gpio
   cd dv/tbclasses/gpio
   # Add: gpio_tb.py, gpio_tests_basic.py, etc.
   ```

3. **Create tests:**
   ```bash
   mkdir -p dv/tests/gpio
   cd dv/tests/gpio
   # Add: test_apb_gpio.py, conftest.py
   ```

4. **Update documentation:**
   - Add block section to PRD.md
   - Create block-specific docs in docs/gpio_spec/
   - Update this README.md

### Naming Conventions

**RTL Modules:**
- Top-level: `apb_{block}.sv`
- Core logic: `{block}_core.sv`
- Registers: `{block}_config_regs.sv`, `{block}_regs.sv`

**Testbenches:**
- Main TB: `{block}_tb.py`
- Test suites: `{block}_tests_basic.py`, `{block}_tests_medium.py`, `{block}_tests_full.py`
- Test runner: `test_apb_{block}.py`

**Imports:**
```python
# Always import from PROJECT AREA
from projects.components.retro_legacy_blocks.dv.tbclasses.{block}.{block}_tb import {Block}TB
```

---

## Integration

### Using a Block in Your Design

**Example - HPET Integration:**

```systemverilog
apb_hpet #(
    .NUM_TIMERS(3),
    .VENDOR_ID(16'h8086),
    .REVISION_ID(16'h0001),
    .CDC_ENABLE(0)  // 0=synchronous clocks, 1=async CDC
) u_hpet (
    // APB interface
    .pclk         (apb_clk),
    .presetn      (apb_rst_n),
    .paddr        (paddr),
    .psel         (psel),
    .penable      (penable),
    .pwrite       (pwrite),
    .pwdata       (pwdata),
    .prdata       (prdata),
    .pready       (pready),
    .pslverr      (pslverr),

    // HPET clock (can be async if CDC_ENABLE=1)
    .hpet_clk     (timer_clk),
    .hpet_rst_n   (timer_rst_n),

    // Interrupts
    .timer_irq    (timer_irq[2:0])  // 3 timers
);
```

### Testing a Block

```bash
# Run all tests for a block
pytest projects/components/retro_legacy_blocks/dv/tests/hpet/ -v

# Run specific test level
pytest projects/components/retro_legacy_blocks/dv/tests/hpet/ -v -k "basic"

# With waveforms
WAVES=1 pytest projects/components/retro_legacy_blocks/dv/tests/hpet/ -v
```

---

## References

### External Documentation

**Peripheral Specifications:**
- ACPI HPET Specification 1.0a
- Intel 8254 Programmable Interval Timer Datasheet
- Intel 8259A Programmable Interrupt Controller Datasheet
- SMBus Specification Version 2.0
- I2C Specification (NXP)
- 16550 UART Datasheet

### Repository Documentation

- `/CLAUDE.md` - Repository AI guide
- `/PRD.md` - Master requirements
- `projects/components/retro_legacy_blocks/PRD.md` - Component requirements
- `projects/components/retro_legacy_blocks/CLAUDE.md` - Component AI guide

---

## Quick Commands

```bash
# Run all HPET tests
pytest projects/components/retro_legacy_blocks/dv/tests/hpet/ -v

# Lint HPET RTL
verilator --lint-only projects/components/retro_legacy_blocks/rtl/hpet/apb_hpet.sv

# Generate HPET specification PDF
cd projects/components/retro_legacy_blocks/docs
./generate_pdf.sh

# View HPET documentation
cat projects/components/retro_legacy_blocks/PRD.md
```

---

## Roadmap

### Near-Term (Next 6 Months) - Q1-Q2 2026

**High Priority Core Peripherals:**
- [ ] 8259 PIC - Programmable Interrupt Controller
- [ ] 8254 PIT - Programmable Interval Timer
- [ ] RTC - Real-Time Clock

**Medium Priority Peripherals:**
- [ ] GPIO Controller
- [ ] SMBus Controller
- [ ] PM/ACPI Controller

### Mid-Term (6-12 Months) - Q3-Q4 2026

- [ ] UART 16550-compatible
- [ ] IOAPIC - I/O Advanced PIC
- [ ] SPI Controller
- [ ] I2C Controller
- [ ] Watchdog Timer

### Long-Term (12+ Months) - 2027

- [ ] Interconnect ID/Version Registers
- [ ] Top-level RLB wrapper with all blocks
- [ ] System-level integration example
- [ ] Performance characterization
- [ ] FPGA reference designs

---

**Version:** 1.0
**Maintained By:** RTL Design Sherpa Project
**Last Review:** 2025-10-29
