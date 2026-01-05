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

# PeakRDL Register Generation for 8254 PIT

This directory contains the SystemRDL specification for the 8254 PIT registers and instructions for generating the RTL.

## Register Specification

**File:** `pit_regs.rdl`

Defines the complete register map for the APB 8254 PIT including:
- Global configuration register
- Control word register (8254-compatible)
- Status register (read-back)
- Three counter data registers

## Generation Command

```bash
# From repository root with venv activated
source venv/bin/activate
cd projects/components/retro_legacy_blocks/rtl/pit_8254/peakrdl
peakrdl regblock pit_regs.rdl --cpuif passthrough -o ../
```

## Generated Files

The command generates two files in the parent directory:

1. **pit_regs.sv** - Register implementation with CPU interface
2. **pit_regs_pkg.sv** - Package with struct definitions

## Register Map

| Address | Register | Access | Description |
|---------|----------|--------|-------------|
| 0x000 | PIT_CONFIG | RW | Global configuration |
| 0x004 | PIT_CONTROL | WO | Control word (8254-compatible) |
| 0x008 | PIT_STATUS | RO | Read-back status |
| 0x00C | RESERVED | RO | Reserved |
| 0x010 | COUNTER0_DATA | RW | Counter 0 value (16-bit) |
| 0x014 | COUNTER1_DATA | RW | Counter 1 value (16-bit) |
| 0x018 | COUNTER2_DATA | RW | Counter 2 value (16-bit) |

## Notes

- Uses `passthrough` CPU interface (like HPET)
- 32-bit register width with 16-bit counter fields
- Control word captures exact written value (not accumulative)
- Control word fields are write-only, hardware-readable (`sw = w`, `hw = r`)
- Status register uses `hw = w` for hardware updates
- Counter data registers are bidirectional (`sw = rw`, `hw = rw`)
