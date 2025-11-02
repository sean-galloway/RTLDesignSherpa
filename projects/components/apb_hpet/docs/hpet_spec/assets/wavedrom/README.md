# HPET Register Layouts - WaveDrom Diagrams

This directory contains WaveDrom register layout diagrams for all HPET registers.

## Files

- **hpet_registers.json** - Complete register definitions in WaveDrom format
- **hpet_registers.html** - Standalone HTML viewer for all registers

## Viewing the Diagrams

### Option 1: Open HTML Viewer (Easiest)

```bash
# Open in your browser
firefox hpet_registers.html
# or
google-chrome hpet_registers.html
```

### Option 2: Online WaveDrom Editor

1. Go to https://wavedrom.com/editor.html
2. Copy a register diagram from `hpet_registers.json`
3. Paste into the editor
4. View the rendered diagram

### Option 3: Command Line (wavedrom-cli)

```bash
# Install wavedrom-cli
npm install -g wavedrom-cli

# Render a specific register
wavedrom-cli -i hpet_config.json -o hpet_config.svg
```

## Register Descriptions

### Global Registers (0x000 - 0x014)

| Offset | Register | Access | Description |
|--------|----------|--------|-------------|
| 0x000 | HPET_CONFIG | RW | Global enable, legacy routing |
| 0x004 | HPET_STATUS | RW (W1C) | Timer interrupt status |
| 0x008 | HPET_COUNTER_LO | RW | Main counter [31:0] |
| 0x00C | HPET_COUNTER_HI | RW | Main counter [63:32] |
| 0x010 | HPET_CAPABILITIES | RO | Hardware capabilities |

### Per-Timer Registers (0x100 + i*0x20)

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

## Key Register Fields

### HPET_CONFIG (0x000)
- **bit[0]**: enable - Enable HPET globally
- **bit[1]**: legacy - Legacy interrupt routing
- **bits[31:2]**: Reserved

### HPET_STATUS (0x004) - Write 1 to Clear
- **bit[i]**: Timer[i] interrupt status
- Write 1 to clear the interrupt flag

### HPET_CAPABILITIES (0x010) - Read Only
- **bits[4:0]**: num_timers - Number of timers (2, 3, or 8)
- **bits[15:5]**: Reserved
- **bits[31:16]**: vendor_id - Vendor identification

### TIMER_CONFIG (0x100 + i*0x20)
- **bit[0]**: enable - Enable timer
- **bit[1]**: int_enable - Enable interrupt generation
- **bit[2]**: type - 0=One-shot, 1=Periodic
- **bit[3]**: size - Reserved
- **bits[31:4]**: Reserved

## Usage in Documentation

To embed these diagrams in markdown documentation:

```markdown
### HPET_CONFIG Register (0x000)

\`\`\`wavedrom
{
  "reg": [
    {"bits": 1, "name": "enable", "attr": "Enable HPET"},
    {"bits": 1, "name": "legacy", "attr": "Legacy routing"},
    {"bits": 30, "name": "reserved", "attr": "Reserved", "type": 1}
  ],
  "config": {"hspace": 800, "bits": 32, "lanes": 1}
}
\`\`\`
```

## Updating Diagrams

To modify register layouts:

1. Edit `hpet_registers.json`
2. Update the corresponding "diagram" object
3. Refresh `hpet_registers.html` in browser to see changes
4. Commit updated JSON to repository

## References

- **WaveDrom Documentation**: https://wavedrom.com/
- **HPET PRD**: `../../PRD.md`
- **PeakRDL Source**: `../../../rtl/peakrdl/hpet_regs.rdl`
