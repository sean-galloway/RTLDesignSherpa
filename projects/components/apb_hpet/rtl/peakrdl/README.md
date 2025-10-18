# HPET PeakRDL Integration

This directory contains the PeakRDL register definition and documentation generation for the HPET configuration registers.

## Directory Structure

```
peakrdl/
├── hpet_regs.rdl           # SystemRDL register definition (source of truth)
├── generate.py             # Documentation generation script
├── generated/              # Auto-generated outputs
│   └── docs/              # Generated documentation (HTML/Markdown)
└── README.md              # This file
```

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
cd rtl/amba/components/hpet/peakrdl
python generate.py
```

This creates:
- **`generated/rtl/hpet_regs.sv/`** - SystemVerilog register block
  - `hpet_regs.sv` - Main register block module
  - `hpet_regs_pkg.sv` - Hardware interface package
- **`generated/docs/hpet_regs.html`** - Interactive HTML documentation
- **`generated/docs/hpet_regs.md`** - Markdown reference

### 2. Use the Wrapper

The `hpet_regs_wrapper.sv` module wraps the PeakRDL-generated register block and provides the cmd/rsp valid/ready interface:

```systemverilog
hpet_regs_wrapper #(
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
