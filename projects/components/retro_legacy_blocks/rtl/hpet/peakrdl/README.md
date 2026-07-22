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

# HPET PeakRDL Integration

This directory contains the PeakRDL register definition and documentation generation for the HPET configuration registers.

## Directory Structure

```
peakrdl/
├── hpet_regs.rdl           # SystemRDL register definition (source of truth)
└── README.md               # This file
```

Generation is done with the shared `bin/peakrdl_generate.py` tool (outputs land in a
local `generated/` directory, which is not checked in; the generated RTL is copied to
`../hpet_regs.sv` and `../hpet_regs_pkg.sv`).

## SystemRDL File

**`hpet_regs.rdl`** defines:
- Global registers (HPET_ID, HPET_CONFIG, HPET_STATUS)
- Main counter registers (64-bit split into LO/HI)
- Parameterizable timer registers (2-8 timers)
- All register fields with access properties

## Current Approach: Documentation Generation Only

Due to version compatibility issues between systemrdl-compiler and peakrdl-regblock, we currently use PeakRDL for **documentation generation only**. The generated documentation serves as the single source of truth for register definitions.

**HPET uses a custom cmd/rsp valid/ready interface:**

**Command Interface:**
- `cmd_valid`, `cmd_ready`
- `cmd_pwrite` (write enable)
- `cmd_paddr[11:0]` (12-bit address)
- `cmd_pwdata[31:0]` (write data)
- `cmd_pstrb[3:0]` (byte strobe)

**Response Interface:**
- `rsp_valid`, `rsp_ready`
- `rsp_prdata[31:0]` (read data)
- `rsp_pslverr` (error flag)

The existing RTL implementation (`../hpet_config_regs.sv`) already implements this interface.

## Usage

### 1. Generate RTL and Documentation

```bash
cd projects/components/retro_legacy_blocks/rtl/hpet/peakrdl
python ../../../../../../bin/peakrdl_generate.py hpet_regs.rdl --copy-rtl ..
```

This creates:
- **`../hpet_regs.sv`** - Main register block module (copied next to the other HPET RTL)
- **`../hpet_regs_pkg.sv`** - Hardware interface package
- **`generated/docs/`** - HTML/Markdown register documentation (regenerated on demand, not checked in)

### 2. Use the Wrapper

The `../hpet_config_regs.sv` module wraps the PeakRDL-generated register block and provides the cmd/rsp valid/ready interface:

```systemverilog
hpet_config_regs #(
    .VENDOR_ID(1),
    .REVISION_ID(1),
    .NUM_TIMERS(2)
) u_hpet_regs (
    .aclk(clk),
    .aresetn(rst_n),

    // Command interface (matches existing HPET design)
    .cmd_valid(cmd_valid),
    .cmd_ready(cmd_ready),
    .cmd_pwrite(cmd_pwrite),
    .cmd_paddr(cmd_paddr),      // 12-bit address
    .cmd_pwdata(cmd_pwdata),
    .cmd_pstrb(cmd_pstrb),

    // Response interface
    .rsp_valid(rsp_valid),
    .rsp_ready(rsp_ready),
    .rsp_prdata(rsp_prdata),
    .rsp_pslverr(rsp_pslverr),

    // Hardware interface (connect to HPET core)
    .hwif_in(hwif_in),
    .hwif_out(hwif_out)
);
```

### 3. Review Documentation

Open the HTML file in a browser to view the complete register specification with:
- Register addresses and field layouts
- Access properties (RO, RW, RW1C)
- Reset values
- Field descriptions

## Register Map

| Address | Register | Access | Description |
|---------|----------|--------|-------------|
| 0x000 | HPET_ID | RO | Vendor, revision, capabilities |
| 0x004 | HPET_CONFIG | RW | Enable, legacy mode |
| 0x008 | HPET_STATUS | RW1C | Timer interrupt status |
| 0x010 | HPET_COUNTER_LO | RW | Counter low 32 bits |
| 0x014 | HPET_COUNTER_HI | RW | Counter high 32 bits |
| 0x100+32n | TIMER[n]_CONFIG | RW | Timer n configuration |
| 0x104+32n | TIMER[n]_COMP_LO | RW | Timer n comparator low |
| 0x108+32n | TIMER[n]_COMP_HI | RW | Timer n comparator high |

## Parameters

- `VENDOR_ID` (default: 1) - Vendor identifier
- `REVISION_ID` (default: 1) - Revision identifier
- `NUM_TIMERS` (default: 2, range: 2-8) - Number of timers

## Benefits of SystemRDL Approach

1. **Single Source of Truth**: Register definitions maintained in one place (`hpet_regs.rdl`)
2. **Documentation**: Automatically generated HTML/Markdown stays in sync with definitions
3. **Validation**: SystemRDL compiler catches definition errors
4. **Future Expansion**: Easy to add new registers or timers by editing `.rdl` file
5. **Parameterization**: `VENDOR_ID`, `REVISION_ID`, `NUM_TIMERS` are compile-time parameters

## Future Enhancements

1. Upgrade systemrdl-compiler/peakrdl-regblock for automatic RTL generation
2. Generate C/C++ headers for software development
3. Create UVM register models for verification
4. Export to IP-XACT format for third-party tools
