# PeakRDL Register Generation for 8259 PIC

This directory contains the SystemRDL specification for the 8259 PIC registers and instructions for generating the RTL.

## Register Specification

**File:** `pic_8259_regs.rdl`

Defines the complete register map for the APB 8259 PIC including:
- Global configuration register
- Initialization Command Words (ICW1-4)
- Operation Command Words (OCW1-3)
- Interrupt Request Register (IRR)
- In-Service Register (ISR)
- Status register

## Generation Command

```bash
# From repository root with venv activated
source venv/bin/activate
cd projects/components/retro_legacy_blocks/rtl/pic_8259/peakrdl
peakrdl regblock pic_8259_regs.rdl --cpuif passthrough -o ../
```

## Generated Files

The command generates two files in the parent directory:

1. **pic_8259_regs.sv** - Register implementation with CPU interface
2. **pic_8259_regs_pkg.sv** - Package with struct definitions

## Register Map

| Address | Register | Access | Description |
|---------|----------|--------|-------------|
| 0x000 | PIC_CONFIG | RW | Global configuration |
| 0x004 | PIC_ICW1 | WO | Initialization Command Word 1 |
| 0x008 | PIC_ICW2 | WO | Initialization Command Word 2 |
| 0x00C | PIC_ICW3 | WO | Initialization Command Word 3 |
| 0x010 | PIC_ICW4 | WO | Initialization Command Word 4 |
| 0x014 | PIC_OCW1 | RW | Operation Command Word 1 (IMR) |
| 0x018 | PIC_OCW2 | WO | Operation Command Word 2 (EOI) |
| 0x01C | PIC_OCW3 | WO | Operation Command Word 3 (special modes) |
| 0x020 | PIC_IRR | RO | Interrupt Request Register |
| 0x024 | PIC_ISR | RO | In-Service Register |
| 0x028 | PIC_STATUS | RO | Status register |

## Notes

- Uses `passthrough` CPU interface (like HPET and PIT 8254)
- 32-bit register width with 8-bit ICW/OCW fields
- ICW registers are write-only, hardware-readable (`sw = w`, `hw = r`)
- OCW1 (IMR) is bidirectional (`sw = rw`, `hw = rw`) for read-modify-write
- IRR/ISR/STATUS registers use `hw = w` for hardware updates
- init_mode field in PIC_CONFIG is bidirectional (`sw = rw`, `hw = rw`) for auto-clear

## 8259A Compatibility

This implementation follows the Intel 8259A architecture with these enhancements:
- Separate address-mapped registers instead of cramped I/O port space
- Explicit ICW/OCW registers vs address-based command sequencing
- Explicit IRR/ISR read registers vs OCW3 read commands
- Status register for diagnostics
