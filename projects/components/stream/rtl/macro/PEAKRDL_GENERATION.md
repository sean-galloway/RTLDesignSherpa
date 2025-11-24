# PeakRDL Register Generation for STREAM

## Status

- ✅ Register definition created: `stream_regs_v2.rdl`
- ⏳ RTL generation pending (requires PeakRDL tool installation)

## Installation

If PeakRDL is not installed:

```bash
# Install PeakRDL and regblock generator
pip3 install peakrdl peakrdl-regblock

# Or in virtual environment
python3 -m pip install peakrdl peakrdl-regblock
```

## RTL Generation

Once PeakRDL is installed, generate the register block RTL:

```bash
cd /mnt/data/github/rtldesignsherpa/projects/components/stream/rtl/macro

# Generate APB4 register block
peakrdl regblock stream_regs_v2.rdl --cpuif apb4 -o generated_rtl/

# Generated files:
#   generated_rtl/stream_regs_v2_regs.sv    - Register file RTL
#   generated_rtl/stream_regs_v2_regs_pkg.sv - Register package
```

## Generated Interface

The PeakRDL-generated register block will have an APB4 interface:

```systemverilog
module stream_regs_v2 (
    // Clock and reset
    input  logic        pclk,
    input  logic        presetn,

    // APB4 interface
    input  logic [31:0] paddr,
    input  logic        psel,
    input  logic        penable,
    input  logic        pwrite,
    input  logic [31:0] pwdata,
    input  logic [3:0]  pstrb,
    output logic [31:0] prdata,
    output logic        pready,
    output logic        pslverr,

    // Register outputs (to stream_config_block.sv)
    output logic        GLOBAL_CTRL_GLOBAL_EN,
    output logic        GLOBAL_CTRL_GLOBAL_RST,
    output logic [7:0]  CHANNEL_ENABLE_CH_EN,
    output logic [7:0]  CHANNEL_RESET_CH_RST,
    // ... (all other register fields)

    // Register inputs (from stream_core.sv status)
    input logic         GLOBAL_STATUS_SYSTEM_IDLE,
    input logic [7:0]   CHANNEL_IDLE_CH_IDLE,
    input logic [7:0]   DESC_ENGINE_IDLE_DESC_IDLE,
    input logic [7:0]   SCHEDULER_IDLE_SCHED_IDLE,
    // ... (all other status fields)
);
```

## Wrapper Integration

The generated register block will be instantiated in `stream_top_chX.sv` wrappers:

```systemverilog
// PeakRDL register block
stream_regs_v2 u_regs (
    .pclk    (pclk),
    .presetn (presetn),
    .paddr   (paddr),
    .psel    (psel),
    // ... APB signals

    // Register outputs
    .GLOBAL_CTRL_GLOBAL_EN(...),
    // ... all register fields
);

// Config block (maps PeakRDL outputs to stream_core inputs)
stream_config_block u_config (
    .clk     (aclk),
    .rst_n   (aresetn),

    // From PeakRDL registers
    .reg_global_enable(GLOBAL_CTRL_GLOBAL_EN),
    // ... all register fields

    // To stream_core
    .cfg_channel_enable(...),
    // ... all config signals
);
```

## Next Steps

1. Install PeakRDL tools (see Installation section above)
2. Generate RTL from `stream_regs_v2.rdl`
3. Integrate generated RTL into `stream_top_chX.sv` wrappers
4. Test register access via APB interface

## Alternative: Manual Register File

If PeakRDL is not available, a manual register file can be created following the same register map defined in `stream_regs_v2.rdl`. This would require:

1. APB4 slave interface logic
2. Register address decode (using register addresses from .rdl file)
3. Read/write logic for each register
4. Field extraction and output assignment

However, using PeakRDL is strongly recommended for consistency, maintainability, and automatic documentation generation.
