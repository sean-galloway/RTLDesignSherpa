# PeakRDL Register Generation for STREAM

## Status

- ✅ Register definition created: `stream_regs.rdl`
- ✅ RTL generated with passthrough CPU interface (matching HPET pattern)

## Installation

If PeakRDL is not installed:

```bash
# Install PeakRDL and regblock generator
pip3 install peakrdl peakrdl-regblock

# Or in virtual environment
python3 -m pip install peakrdl peakrdl-regblock
```

## RTL Generation

**IMPORTANT: Use passthrough interface (not apb4) to match HPET architecture:**

```bash
cd /mnt/data/github/rtldesignsherpa/projects/components/stream/rtl/macro

# Generate with passthrough CPU interface
peakrdl regblock stream_regs.rdl --cpuif passthrough -o ../../regs/generated/rtl/

# Generated files:
#   ../../regs/generated/rtl/stream_regs.sv      - Register file RTL
#   ../../regs/generated/rtl/stream_regs_pkg.sv  - Register package
```

**Why passthrough interface?**
- Matches proven HPET architecture pattern
- Compatible with `peakrdl_to_cmdrsp` adapter
- Cleaner separation between APB protocol and register logic
- Discrete signals easier to route than SystemVerilog interfaces

## Generated Interface

The PeakRDL-generated register block has a passthrough CPU interface:

```systemverilog
module stream_regs (
    // Clock and reset
    input  logic        clk,
    input  logic        rst,

    // Passthrough CPU interface (discrete signals)
    input  logic        s_cpuif_req,
    input  logic        s_cpuif_req_is_wr,
    input  logic [9:0]  s_cpuif_addr,
    input  logic [31:0] s_cpuif_wr_data,
    input  logic [31:0] s_cpuif_wr_biten,
    output logic        s_cpuif_req_stall_wr,
    output logic        s_cpuif_req_stall_rd,
    output logic        s_cpuif_rd_ack,
    output logic        s_cpuif_rd_err,
    output logic [31:0] s_cpuif_rd_data,
    output logic        s_cpuif_wr_ack,
    output logic        s_cpuif_wr_err,

    // Hardware interface (register access)
    input  stream_regs_pkg::stream_regs__in_t  hwif_in,
    output stream_regs_pkg::stream_regs__out_t hwif_out
);
```

## Wrapper Integration Architecture

Following HPET pattern, the integration requires three components:

**1. APB → CMD/RSP converter** (existing utility):
- Module: `projects/components/converters/rtl/peakrdl_to_cmdrsp.sv`
- Converts APB4 protocol to CMD/RSP handshake
- Part of common infrastructure

**2. stream_regs** (PeakRDL-generated):
- Module: `projects/components/stream/regs/generated/rtl/stream_regs.sv`
- Passthrough CPU interface
- Hardware interface for register access

**3. stream_config_block** (wrapper):
- Module: `projects/components/stream/rtl/top/stream_config_block.sv`
- Extracts hwif fields and maps to STREAM core config signals
- Combines CDC if needed

### Integration Example (matching HPET pattern)

```systemverilog
// In stream_top_ch8.sv or wrapper module

// CMD/RSP adapter
peakrdl_to_cmdrsp #(
    .ADDR_WIDTH(12),
    .DATA_WIDTH(32)
) u_peakrdl_adapter (
    .aclk       (aclk),
    .aresetn    (aresetn),
    // CMD/RSP input (from stream_apb_router)
    .cmd_valid  (regs_cmd_valid),
    .cmd_ready  (regs_cmd_ready),
    .cmd_pwrite (regs_cmd_pwrite),
    .cmd_paddr  (regs_cmd_paddr),
    .cmd_pwdata (regs_cmd_pwdata),
    .rsp_valid  (regs_rsp_valid),
    .rsp_ready  (regs_rsp_ready),
    .rsp_prdata (regs_rsp_prdata),
    .rsp_pslverr(regs_rsp_pslverr),
    // Passthrough interface (to stream_regs)
    .regblk_req        (regblk_req),
    .regblk_req_is_wr  (regblk_req_is_wr),
    .regblk_addr       (regblk_addr),
    .regblk_wr_data    (regblk_wr_data),
    .regblk_wr_biten   (regblk_wr_biten),
    .regblk_req_stall_wr(regblk_req_stall_wr),
    .regblk_req_stall_rd(regblk_req_stall_rd),
    .regblk_rd_ack     (regblk_rd_ack),
    .regblk_rd_err     (regblk_rd_err),
    .regblk_rd_data    (regblk_rd_data),
    .regblk_wr_ack     (regblk_wr_ack),
    .regblk_wr_err     (regblk_wr_err)
);

// PeakRDL register block
stream_regs u_stream_regs (
    .clk    (aclk),
    .rst    (~aresetn),  // Active-high reset
    // Passthrough CPU interface
    .s_cpuif_req        (regblk_req),
    .s_cpuif_req_is_wr  (regblk_req_is_wr),
    .s_cpuif_addr       (regblk_addr[9:0]),
    .s_cpuif_wr_data    (regblk_wr_data),
    .s_cpuif_wr_biten   (regblk_wr_biten),
    .s_cpuif_req_stall_wr(regblk_req_stall_wr),
    .s_cpuif_req_stall_rd(regblk_req_stall_rd),
    .s_cpuif_rd_ack     (regblk_rd_ack),
    .s_cpuif_rd_err     (regblk_rd_err),
    .s_cpuif_rd_data    (regblk_rd_data),
    .s_cpuif_wr_ack     (regblk_wr_ack),
    .s_cpuif_wr_err     (regblk_wr_err),
    // Hardware interface
    .hwif_in            (hwif_in),
    .hwif_out           (hwif_out)
);

// Config block (extracts hwif and maps to core)
stream_config_block u_config (
    .clk     (aclk),
    .rst_n   (aresetn),
    // From hwif
    .hwif_out(hwif_out),
    .hwif_in (hwif_in),
    // To stream_core
    .cfg_channel_enable(cfg_channel_enable),
    // ... all config signals
);
```

## Next Steps

1. ✅ PeakRDL registers generated with passthrough interface
2. ⏳ Create stream_config_block wrapper (extract hwif to config signals)
3. ⏳ Integrate into stream_top_ch8.sv following HPET pattern
4. ⏳ Test register access via APB interface

## Reference Implementation

**See:** `projects/components/retro_legacy_blocks/rtl/hpet/hpet_config_regs.sv` for complete working example of this integration pattern.
