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
- Interrupt acknowledge register (PIC_INTA, 0x02C) - read-only and
  side-effecting: reading it performs the acknowledge

## Generation Command

Use the repository wrapper, NOT `peakrdl regblock` directly: the wrapper emits
the RTL, the docs and the RegisterMap export in lockstep, and a raw
`peakrdl regblock` leaves `pic_8259_regmap.py` behind (handbook:
[[feedback_peakrdl_generate_bin]]).

```bash
source env_python
cd projects/components/retro_legacy_blocks/rtl/pic_8259/peakrdl

# 1. RTL + package, copied into the block directory the filelist reads from
python3 $REPO_ROOT/bin/peakrdl_generate.py pic_8259_regs.rdl --copy-rtl .. --no-html

# 2. RegisterMap export, under the name pic_8259_helper.py imports
python3 $REPO_ROOT/bin/peakrdl_generate.py pic_8259_regs.rdl --docs-only \
        --no-html --no-markdown --regmap --regmap-output ../pic_8259_regmap.py

# 3. Delete the scratch output directory - nothing consumes it, and an
#    orphaned second copy of generated output is a live trap
rm -rf generated
```

## Generated Files

Three files, all in the parent directory:

1. **pic_8259_regs.sv** - Register implementation with CPU interface
2. **pic_8259_regs_pkg.sv** - Package with struct definitions
3. **pic_8259_regmap.py** - RegisterMap export (by-name register access in DV)

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
| 0x02C | PIC_INTA | RO | Interrupt acknowledge BY READ - reading it acknowledges |

Nothing else in the 4 KB window is decoded; `pic_8259_config_regs.sv` drops
every other address with PSLVERR.

## Notes

- Uses `passthrough` CPU interface (like HPET and PIT 8254)
- 32-bit register width with 8-bit ICW/OCW fields
- ICW registers are write-only, hardware-readable (`sw = w`, `hw = r`)
- OCW1 (IMR) is `sw = rw`, `hw = r`: the regblock field is the ONE copy of
  the mask, so a read-after-write can never see a stale hardware mirror
- IRR/ISR/STATUS registers use `hw = w` for hardware updates
- init_mode in PIC_CONFIG is `sw = rw`, `hw = r`, `hwclr`, `precedence = hw`:
  the auto-clear after ICW4 is a hardware clear that beats a coincident
  software write, which a `hw = rw` write-back mirror could not do
- PIC_INTA's fields are `sw = r`, `hw = w` with NO storage, so the readback is
  combinational from `hwif_in.*.next` - that is what makes the value returned
  the PRE-acknowledge one. `vector` carries `swacc`, the acknowledge strobe

## 8259A Compatibility

This implementation follows the Intel 8259A architecture with these enhancements:
- Separate address-mapped registers instead of cramped I/O port space
- Explicit ICW/OCW registers vs address-based command sequencing
- Explicit IRR/ISR read registers vs OCW3 read commands
- Status register for diagnostics
