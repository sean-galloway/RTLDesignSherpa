# HPET WaveDrom Diagrams

## Overview

This directory contains WaveDrom diagrams for HPET documentation.

### Directory Structure

```
wavedrom/
  ├── README.md              # This file
  ├── hpet_registers.json    # Register bit-field layouts
  ├── hpet_registers.html    # HTML viewer for registers
  └── timing/                # Timing diagrams
      ├── README.md          # Timing diagram documentation
      ├── hpet_config_write.json
      ├── hpet_counter_read.json
      ├── hpet_timer_fire_oneshot.json
      ├── hpet_timer_fire_periodic.json
      ├── hpet_interrupt_clear.json
      ├── hpet_timer_setup.json
      └── hpet_cdc_crossing.json
```

### Diagram Types

#### Register Layouts (this directory)
- **hpet_registers.json** - Complete register bit-field definitions
- **hpet_registers.html** - Standalone HTML viewer for all registers

#### Timing Diagrams (timing/ subdirectory)
- **hpet_config_write.json** - APB write to enable HPET
- **hpet_counter_read.json** - APB read of main counter
- **hpet_timer_fire_oneshot.json** - One-shot timer fire event
- **hpet_timer_fire_periodic.json** - Periodic timer operation
- **hpet_interrupt_clear.json** - W1C interrupt clearing
- **hpet_timer_setup.json** - Timer configuration sequence
- **hpet_cdc_crossing.json** - Clock domain crossing

---

## Functional Description

### Register Descriptions

#### Global Registers (0x000 - 0x014)

| Offset | Register | Access | Description |
|--------|----------|--------|-------------|
| 0x000 | HPET_ID | RO | Identification and capabilities |
| 0x004 | HPET_CONFIG | RW | Global enable |
| 0x008 | HPET_STATUS | RW (W1C) | Timer interrupt status |
| 0x00C | RESERVED | RO | Reads 0 |
| 0x010 | HPET_COUNTER_LO | RW | Main counter [31:0] |
| 0x014 | HPET_COUNTER_HI | RW | Main counter [63:32] |

#### Per-Timer Registers (0x100 + i*0x20)

Each timer has 4 registers with 0x20 byte stride:

| Offset | Register | Access | Description |
|--------|----------|--------|-------------|
| +0x00 | TIMER_CONFIG | RW | Enable, interrupt, mode |
| +0x04 | TIMER_COMPARATOR_LO | RW | Comparator [31:0] |
| +0x08 | TIMER_COMPARATOR_HI | RW | Comparator [63:32] |
| +0x0C | Reserved | - | Reserved |

**Examples:**
- Timer 0: Base = 0x100
- Timer 1: Base = 0x120 (0x100 + 1*0x20)
- Timer 2: Base = 0x140 (0x100 + 2*0x20)
- Timer 7: Base = 0x1E0 (0x100 + 7*0x20)

### Key Register Fields

#### HPET_ID (0x000) - Read Only
- **bits[4:0]**: Reserved
- **bit[5]**: leg_rt_cap (reads 1; feature not implemented)
- **bit[6]**: Reserved
- **bit[7]**: count_size_cap (1 = 64-bit counter)
- **bits[12:8]**: num_tim_cap - Number of timers minus 1
- **bits[15:13]**: Reserved
- **bits[23:16]**: rev_id (fixed 0x01)
- **bits[31:24]**: vendor_id (fixed 0x01)

#### HPET_CONFIG (0x004)
- **bit[0]**: hpet_enable - Enable HPET globally
- **bit[1]**: legacy_replacement - stored, no hardware effect
- **bits[31:2]**: Reserved

#### HPET_STATUS (0x008) - Write 1 to Clear
- **bit[i]**: Timer[i] interrupt status (fixed 8-bit field)
- Write 1 to clear the interrupt flag

#### TIMER_CONFIG (0x100 + i*0x20)
- **bits[1:0]**: Reserved
- **bit[2]**: timer_enable - Enable timer
- **bit[3]**: timer_int_enable - Enable interrupt generation
- **bit[4]**: timer_type - 0=One-shot, 1=Periodic
- **bit[5]**: timer_size - 0=32-bit, 1=64-bit compare
- **bit[6]**: timer_value_set - stored, no hardware effect
- **bits[31:7]**: Reserved

---

## Usage Example

### Viewing the Diagrams

#### Option 1: Open HTML Viewer (Easiest)

```bash
# Open in your browser
firefox hpet_registers.html
# or
google-chrome hpet_registers.html
```

#### Option 2: Online WaveDrom Editor

1. Go to https://wavedrom.com/editor.html
2. Copy a register diagram from `hpet_registers.json`
3. Paste into the editor
4. View the rendered diagram

#### Option 3: Command Line (wavedrom-cli)

```bash
# Install wavedrom-cli
npm install -g wavedrom-cli

# Render a specific register
wavedrom-cli -i hpet_config.json -o hpet_config.svg
```

### Usage in Documentation

To embed these diagrams in markdown documentation:

```markdown
### HPET_CONFIG Register (0x004)

\`\`\`wavedrom
{
  "reg": [
    {"bits": 1, "name": "hpet_enable", "attr": "Enable HPET"},
    {"bits": 1, "name": "legacy_replacement", "attr": "Stored, no HW effect"},
    {"bits": 30, "name": "reserved", "attr": "Reserved", "type": 1}
  ],
  "config": {"hspace": 800, "bits": 32, "lanes": 1}
}
\`\`\`
```

### Updating Diagrams

To modify register layouts:

1. Edit `hpet_registers.json`
2. Update the corresponding "diagram" object
3. Refresh `hpet_registers.html` in browser to see changes
4. Commit updated JSON to repository

---

## References

- **WaveDrom Documentation**: https://wavedrom.com/
- **HPET PRD**: `../../PRD.md`
- **PeakRDL Source**: `../../../../rtl/hpet/peakrdl/hpet_regs.rdl`
