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

# STREAM Register Definitions

**Purpose:** PeakRDL register files and generated RTL for STREAM configuration

> Status (2026-07-22): the "Future" phases below are DONE. The register source lives at
> `../rtl/macro/stream_regs.rdl` (+ `stream_mon_regs.rdl`), generated outputs are in
> `generated/`, and the config block is `../rtl/top/stream_config_block.sv`.
> Regenerate only via `bin/peakrdl_generate.py`. The HPET reference now lives in
> `projects/components/retro_legacy_blocks/`.

---

## Directory Structure

```
regs/
├── README.md                 # This file
├── stream_regs.rdl           # Register definition (to be created)
└── generated/                # PeakRDL-generated outputs (to be created)
    ├── rtl/
    │   ├── stream_regs.sv
    │   └── stream_regs_pkg.sv
    └── docs/
        └── stream_regs.html
```

---

## Register Generation Workflow

### Phase 1: Define Register Map (Future)

Create `stream_regs.rdl` following the same pattern as `apb_hpet`.

### Phase 2: PeakRDL-Generated Registers (Future)

Following the same pattern as the HPET block in `projects/components/retro_legacy_blocks/`:

1. **Define Register Map** (`stream_regs.rdl`)
   ```systemverilog
   addrmap stream_regs {
       name = "STREAM Configuration Registers";

       // Global control
       reg {
           field { sw=rw; hw=r; } enable;
           field { sw=rw; hw=r; } reset;
       } GLOBAL_CTRL @ 0x00;

       // Channel registers (8 channels × 16 bytes)
       regfile channel_regs {
           reg { ... } CH_CTRL;
           reg { ... } CH_STATUS;
           reg { ... } CH_RD_BURST;
           reg { ... } CH_WR_BURST;
       };

       channel_regs CH[8] @ 0x10 += 0x10;
   };
   ```

2. **Generate RTL**
   ```bash
   cd projects/components/dmas/stream/regs
   ../../bin/peakrdl_generate.py stream_regs.rdl --copy-rtl ../rtl/macro
   ```

3. **Create APB Config Wrapper**
   - Instantiate generated register block (similar to `apb_hpet.sv`)
   - Add `apb4_slave_cdc` wrapper if clock domain crossing needed
   - Wire register outputs to STREAM control signals

---

## Register Map (Planned)

### Global Registers

| Address | Name | Access | Description |
|---------|------|--------|-------------|
| 0x00 | GLOBAL_CTRL | RW | Global enable, reset |
| 0x04 | GLOBAL_STATUS | RO | Global status, channel idle/error |
| 0x08 | GLOBAL_CONFIG | RW | Global configuration |
| 0x0C | Reserved | - | - |

### Channel Registers (8 × 0x10 bytes)

Each channel (0-7) has a 16-byte register block starting at `0x10 + (channel_id × 0x10)`:

| Offset | Name | Access | Description |
|--------|------|--------|-------------|
| +0x00 | CHx_CTRL | WO | Descriptor address (write to kick off) |
| +0x04 | CHx_STATUS | RO | Channel status, idle, error |
| +0x08 | CHx_RD_BURST | RW | Read burst length (for engine config) |
| +0x0C | CHx_WR_BURST | RW | Write burst length (for engine config) |

**Example:**
- Channel 0 registers: 0x10, 0x14, 0x18, 0x1C
- Channel 1 registers: 0x20, 0x24, 0x28, 0x2C
- Channel 7 registers: 0x80, 0x84, 0x88, 0x8C

---

## Integration Pattern

### PeakRDL-Generated Implementation (Future):

```systemverilog
// Actual implementation: rtl/top/stream_config_block.sv
module apb_config (
    // APB interface
    input  logic [ADDR_WIDTH-1:0] paddr,
    // ...
);
    // Instantiate PeakRDL-generated registers
    stream_regs u_regs (
        .pclk    (pclk),
        .presetn (presetn),
        .paddr   (paddr),
        .psel    (psel),
        // ... APB signals

        // Register field outputs
        .global_ctrl_enable (ch_enable_internal),
        .ch0_ctrl_desc_addr (ch_desc_addr[0]),
        .ch0_rd_burst       (ch_read_burst_len[0]),
        // ... generated field outputs
    );

    // Optional: Add CDC wrapper if crossing clock domains
    // (like HPET's apb4_slave_cdc)
endmodule
```

---

## Reference Examples

**HPET PeakRDL Implementation (now in retro_legacy_blocks):**
- `projects/components/retro_legacy_blocks/rtl/hpet/peakrdl/hpet_regs.rdl` - Register definition
- `projects/components/retro_legacy_blocks/rtl/hpet/` - Generated register RTL (`hpet_regs.sv`, `hpet_regs_pkg.sv`)
- `projects/components/retro_legacy_blocks/rtl/hpet/apb_hpet.sv` - Wrapper with CDC

**HPET Generation Command:**
```bash
../../bin/peakrdl_generate.py hpet_regs.rdl --copy-rtl ..
```

---

## Status

- ⏳ **Phase 1:** Manual `apb_config.sv` (placeholder)
- ⏳ **Phase 2:** Create `stream_regs.rdl` (deferred to after Phase 2 RTL implementation)
- ⏳ **Phase 3:** Generate register RTL with PeakRDL
- ⏳ **Phase 4:** Update `apb_config.sv` wrapper to use generated registers

**Note:** Per user feedback, "The apb config will be the last thing done. They will have configs done along the lines of how they are done for the hpet."

---

**Last Updated:** 2026-07-22
**Related Documentation:**
- `../docs/stream_mas/` - STREAM MAS (register chapter supersedes the old ARCHITECTURAL_NOTES.md)
- `../PRD.md` Section 3.1 - APB Configuration Interface
- `../../../retro_legacy_blocks/rtl/hpet/peakrdl/README.md` - HPET PeakRDL example
