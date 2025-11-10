# Claude Code Guide: Projects/Components

**Version:** 1.0
**Last Updated:** 2025-10-24
**Purpose:** AI-specific guidance for working with projects/components area

---

## Quick Context

**What:** High-performance RTL components for custom accelerators and systems
**Status:** Active development - STREAM, RAPIDS, Bridge, APB HPET production blocks
**Your Role:** Help users develop new components following repository standards

**Key Projects:**
- **STREAM** - Streaming datapath engine with AXI and SRAM control
- **RAPIDS** - Rapid AXI Programmable In-band Descriptor System
- **Bridge** - Protocol bridges and converters
- **APB HPET** - APB High Precision Event Timer

**Complete Documentation:** See individual project CLAUDE.md and PRD.md files in each component directory

---

## 📖 Global Requirements Reference

**IMPORTANT: Check `/GLOBAL_REQUIREMENTS.md` for all mandatory requirements**

This file contains project-area-specific standards. For the complete list of mandatory requirements across the entire repository:
- **See:** `/GLOBAL_REQUIREMENTS.md` - Consolidated mandatory requirements
- **Priorities:** P0 (critical), P1 (high), P2 (standard), P3 (project-specific)
- **Compliance:** All P0 requirements are enforced - PRs will be rejected if violated

This CLAUDE.md focuses on projects/components/ specifics. Also review:
- Root `/CLAUDE.md` - Repository-wide guidance
- `bin/CocoTBFramework/CLAUDE.md` - Framework patterns
- `projects/components/{name}/CLAUDE.md` - Component-specific guidance

---

## Critical Standards for This Area

### Rule #0: Reset Handling Standards (MANDATORY)

**📖 See:** `/GLOBAL_REQUIREMENTS.md` Section 1.1 for complete requirement

**Projects/Components-Specific Context:**

This area is the PRIMARY enforcement zone for reset macro usage. Unlike rtl/common/ and rtl/amba/ (already compliant), projects/components/ is actively converting to reset macros.

**Quick Reference:**
```systemverilog
`include "reset_defs.svh"

`ALWAYS_FF_RST(clk, rst_n,
    if (`RST_ASSERTED(rst_n)) begin
        r_state <= IDLE;
    end else begin
        r_state <= w_next_state;
    end
)
```

**Conversion Tool for Bulk Updates:**
```bash
# Convert existing files (writes to UPDATED/ directory)
python3 bin/update_resets.py projects/components/{component}/rtl/

# Review differences
diff -u original.sv UPDATED/original.sv

# Copy back after review
cp UPDATED/*.sv projects/components/{component}/rtl/
```

**Historical Context:**
- APB HPET: Converted after initial development
- STREAM/RAPIDS: Converting as features are added
- New components: MUST use macros from day one

**Macro Definitions:** See `rtl/amba/includes/reset_defs.svh`

---

### Rule #1: FPGA Synthesis Attributes (MANDATORY)

**📖 See:** `/GLOBAL_REQUIREMENTS.md` Section 1.2 for complete requirement

**Projects/Components-Specific Examples:**

```systemverilog
// Standard pattern for SRAM buffers (common in datapaths)
`ifdef XILINX
    (* ram_style = "auto" *)
`elsif INTEL
    /* synthesis ramstyle = "AUTO" */
`endif
logic [DATA_WIDTH-1:0] sram_buffer [DEPTH];

// Small FIFOs - prefer distributed RAM
`ifdef XILINX
    (* ram_style = "distributed" *)
`elsif INTEL
    /* synthesis ramstyle = "MLAB" */
`endif
logic [31:0] small_fifo [16];

// DSP inference for datapath multipliers
`ifdef XILINX
    (* use_dsp = "yes" *)
`endif
logic [31:0] scaled_data = coefficient * input_data;
```

**See Examples In:**
- `projects/components/stream/rtl/stream_fub/simple_sram.sv` - SRAM with attributes
- `projects/components/rapids/rtl/rapids_fub/descriptor_engine.sv` - FIFO with attributes

---

### Rule #2: Array Syntax Standards (MANDATORY)

**📖 See:** `/GLOBAL_REQUIREMENTS.md` Section 1.3 for complete requirement

**Quick Reference:** Use `[DEPTH]` not `[0:DEPTH-1]`

```systemverilog
// ✅ CORRECT
logic [DATA_WIDTH-1:0] mem [DEPTH];

// ❌ WRONG
logic [DATA_WIDTH-1:0] mem [0:DEPTH-1];
```

---

### Rule #3: SRAM Module Standards (MANDATORY)

**📖 See:** `/GLOBAL_REQUIREMENTS.md` Section 1.4 for complete requirement

**Projects/Components-Specific Pattern:**

STREAM and RAPIDS use large SRAM buffers extensively. Here's the standard pattern:

```systemverilog
// SRAM module - NO reset port
module simple_sram #(
    parameter int DATA_WIDTH = 512,  // Datapath width
    parameter int DEPTH = 4096       // Buffer depth
) (
    input  logic clk,
    // NO rst_n port!
    input  logic wr_en,
    input  logic [$clog2(DEPTH)-1:0] wr_addr,
    input  logic [DATA_WIDTH-1:0] wr_data,
    input  logic rd_en,
    input  logic [$clog2(DEPTH)-1:0] rd_addr,
    output logic [DATA_WIDTH-1:0] rd_data
);
    `ifdef XILINX
        (* ram_style = "auto" *)
    `elsif INTEL
        /* synthesis ramstyle = "AUTO" */
    `endif
    logic [DATA_WIDTH-1:0] mem [DEPTH] = '{default:0};

    always_ff @(posedge clk) if (wr_en) mem[wr_addr] <= wr_data;
    always_ff @(posedge clk) if (rd_en) rd_data <= mem[rd_addr];
endmodule
```

**See:** `projects/components/stream/rtl/stream_fub/simple_sram.sv`

---

### Rule #4: TB Location (MANDATORY)

**📖 See:** `/GLOBAL_REQUIREMENTS.md` Section 2.1 for complete requirement

**Projects/Components-Specific Import Pattern:**

```python
# Standard path setup for project tests
import os, sys
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../../..'))
sys.path.insert(0, repo_root)

# Import from PROJECT AREA (not framework!)
from projects.components.stream.dv.tbclasses.scheduler_tb import SchedulerTB

# Shared utilities from framework
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.axi4.axi4_master import AXI4Master
```

**Examples:**
- `projects/components/rapids/dv/tbclasses/` - RAPIDS TBs
- `projects/components/stream/dv/tbclasses/` - STREAM TBs

---

## Common Patterns for New Components

### Pattern 1: Streaming Pipeline Module

**Use Case:** AXI read/write engines, data movers, streaming datapaths

**Key Features:**
- NO FSM! Streaming pipelines for max performance
- Valid/ready handshaking throughout
- Backpressure handling
- Reset macro usage

**Template:**
```systemverilog
`timescale 1ns / 1ps

`include "stream_imports.svh"
`include "reset_defs.svh"

module streaming_engine #(
    parameter int DATA_WIDTH = 512,
    parameter int ADDR_WIDTH = 64
) (
    input  logic                    clk,
    input  logic                    rst_n,

    // Input stream
    input  logic                    s_valid,
    output logic                    s_ready,
    input  logic [DATA_WIDTH-1:0]   s_data,

    // Output stream
    output logic                    m_valid,
    input  logic                    m_ready,
    output logic [DATA_WIDTH-1:0]   m_data
);

    // Pipeline registers
    logic r_valid;
    logic [DATA_WIDTH-1:0] r_data;

    // Streaming logic
    assign s_ready = !r_valid || m_ready;
    assign m_valid = r_valid;
    assign m_data = r_data;

    // Pipeline stage with reset
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_valid <= 1'b0;
            r_data <= '0;
        end else begin
            if (s_ready) begin
                r_valid <= s_valid;
                if (s_valid) begin
                    r_data <= s_data;
                end
            end
        end
    )

endmodule : streaming_engine
```

**See also:**
- `projects/components/stream/rtl/stream_fub/axi_read_engine.sv`
- `projects/components/stream/rtl/stream_fub/axi_write_engine.sv`

---

### Pattern 2: Descriptor-Driven Engine

**Use Case:** Descriptor engines, schedulers, control paths

**Key Features:**
- Descriptor fetch and processing
- State machine with reset macros
- Configuration registers
- Completion reporting

**Template:**
```systemverilog
`timescale 1ns / 1ps

`include "reset_defs.svh"

module descriptor_engine #(
    parameter int ADDR_WIDTH = 64,
    parameter int DESC_WIDTH = 256
) (
    input  logic                    clk,
    input  logic                    rst_n,

    // Descriptor input
    input  logic                    desc_valid,
    output logic                    desc_ready,
    input  logic [DESC_WIDTH-1:0]   desc_data,

    // Completion output
    output logic                    done_strobe,
    output logic [31:0]             result_data
);

    // State machine
    typedef enum logic [2:0] {
        IDLE        = 3'b000,
        FETCH_DESC  = 3'b001,
        PROCESS     = 3'b010,
        COMPLETE    = 3'b011
    } state_t;

    state_t r_state, w_next_state;

    // Descriptor storage
    logic [DESC_WIDTH-1:0] r_desc;
    logic [31:0] r_result;

    // State register
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_state <= IDLE;
        end else begin
            r_state <= w_next_state;
        end
    )

    // Next state logic
    always_comb begin
        w_next_state = r_state;
        case (r_state)
            IDLE:       if (desc_valid) w_next_state = FETCH_DESC;
            FETCH_DESC: w_next_state = PROCESS;
            PROCESS:    w_next_state = COMPLETE;
            COMPLETE:   w_next_state = IDLE;
            default:    w_next_state = IDLE;
        endcase
    end

    // Descriptor and result registers
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_desc <= '0;
            r_result <= '0;
        end else begin
            if (r_state == IDLE && desc_valid) begin
                r_desc <= desc_data;
            end
            if (r_state == PROCESS) begin
                r_result <= process_descriptor(r_desc);
            end
        end
    )

    // Output assignments
    assign desc_ready = (r_state == IDLE);
    assign done_strobe = (r_state == COMPLETE);
    assign result_data = r_result;

    // Processing function
    function automatic [31:0] process_descriptor(input [DESC_WIDTH-1:0] desc);
        // Descriptor processing logic
        return desc[31:0];  // Example
    endfunction

endmodule : descriptor_engine
```

**See also:**
- `projects/components/stream/rtl/stream_fub/descriptor_engine.sv`
- `projects/components/rapids/rtl/rapids_fub/descriptor_engine.sv`

---

### Pattern 3: SRAM Buffer with Controller

**Use Case:** Data buffering, temporary storage, packet buffers

**Key Features:**
- SRAM has no reset
- Controller manages pointers with reset
- FPGA memory attributes
- Full/empty flags

**Template:**
```systemverilog
`timescale 1ns / 1ps

`include "reset_defs.svh"

module sram_buffer #(
    parameter int DATA_WIDTH = 512,
    parameter int DEPTH = 4096
) (
    input  logic                        clk,
    input  logic                        rst_n,

    // Write interface
    input  logic                        wr_valid,
    output logic                        wr_ready,
    input  logic [DATA_WIDTH-1:0]       wr_data,

    // Read interface
    output logic                        rd_valid,
    input  logic                        rd_ready,
    output logic [DATA_WIDTH-1:0]       rd_data,

    // Status
    output logic                        full,
    output logic                        empty
);

    localparam int ADDR_WIDTH = $clog2(DEPTH);

    // Pointers and counters
    logic [ADDR_WIDTH-1:0] r_wr_ptr;
    logic [ADDR_WIDTH-1:0] r_rd_ptr;
    logic [ADDR_WIDTH:0] r_count;  // Extra bit for full detection

    // SRAM interface
    logic sram_wr_en;
    logic [ADDR_WIDTH-1:0] sram_wr_addr;
    logic [DATA_WIDTH-1:0] sram_wr_data;
    logic sram_rd_en;
    logic [ADDR_WIDTH-1:0] sram_rd_addr;
    logic [DATA_WIDTH-1:0] sram_rd_data;

    // Control logic with reset
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_wr_ptr <= '0;
            r_rd_ptr <= '0;
            r_count <= '0;
        end else begin
            // Write pointer
            if (wr_valid && wr_ready) begin
                r_wr_ptr <= r_wr_ptr + 1'b1;
            end

            // Read pointer
            if (rd_valid && rd_ready) begin
                r_rd_ptr <= r_rd_ptr + 1'b1;
            end

            // Count
            case ({wr_valid && wr_ready, rd_valid && rd_ready})
                2'b10: r_count <= r_count + 1'b1;  // Write only
                2'b01: r_count <= r_count - 1'b1;  // Read only
                default: r_count <= r_count;       // Both or neither
            endcase
        end
    )

    // Status flags
    assign full = (r_count == DEPTH);
    assign empty = (r_count == 0);
    assign wr_ready = !full;
    assign rd_valid = !empty;

    // SRAM control
    assign sram_wr_en = wr_valid && wr_ready;
    assign sram_wr_addr = r_wr_ptr;
    assign sram_wr_data = wr_data;
    assign sram_rd_en = !empty;
    assign sram_rd_addr = r_rd_ptr;
    assign rd_data = sram_rd_data;

    // SRAM instance (NO reset!)
    simple_sram #(
        .DATA_WIDTH(DATA_WIDTH),
        .DEPTH(DEPTH)
    ) u_sram (
        .clk      (clk),
        .wr_en    (sram_wr_en),
        .wr_addr  (sram_wr_addr),
        .wr_data  (sram_wr_data),
        .rd_en    (sram_rd_en),
        .rd_addr  (sram_rd_addr),
        .rd_data  (sram_rd_data)
    );

endmodule : sram_buffer
```

**See also:**
- `projects/components/stream/rtl/stream_fub/sram_controller.sv`
- `projects/components/stream/rtl/stream_fub/simple_sram.sv`

---

## Anti-Patterns to Avoid

### Anti-Pattern 1: Direct always_ff Without Reset Macros

```systemverilog
// WRONG: Manual reset handling
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        r_state <= IDLE;
    end else begin
        r_state <= w_next_state;
    end
end

// CORRECT: Use reset macros
`ALWAYS_FF_RST(clk, rst_n,
    if (`RST_ASSERTED(rst_n)) begin
        r_state <= IDLE;
    end else begin
        r_state <= w_next_state;
    end
)
```

### Anti-Pattern 2: Memory Without FPGA Attributes

```systemverilog
// WRONG: No synthesis hints
logic [511:0] mem [4096];

// CORRECT: FPGA attributes
`ifdef XILINX
    (* ram_style = "auto" *)
`elsif INTEL
    /* synthesis ramstyle = "AUTO" */
`endif
logic [511:0] mem [4096];
```

### Anti-Pattern 3: SRAM With Reset Port

```systemverilog
// WRONG: SRAM should not have reset
module simple_sram #(...) (
    input logic clk,
    input logic rst_n,  // DON'T DO THIS!
    // ...
);

// CORRECT: SRAM has no reset
module simple_sram #(...) (
    input logic clk,
    // No rst_n port
    // ...
);
```

### Anti-Pattern 4: Old Array Syntax

```systemverilog
// WRONG: Old-style array declaration
logic [31:0] mem [0:DEPTH-1];

// CORRECT: Modern syntax
logic [31:0] mem [DEPTH];
```

---

## Tools and Automation

### Reset Macro Conversion Script

**Script:** `bin/update_resets.py`

**Purpose:** Automatically convert manual `always_ff` blocks to reset macros

**Usage:**
```bash
# Dry-run to see what would change
python3 bin/update_resets.py projects/components/stream/rtl/ --dry-run

# Convert files (writes to UPDATED/ directory)
python3 bin/update_resets.py projects/components/stream/rtl/

# Review changes
diff -u projects/components/stream/rtl/scheduler.sv UPDATED/scheduler.sv

# Copy corrected files back
cp UPDATED/*.sv projects/components/stream/rtl/
```

**What it does:**
1. Finds all `always_ff @(posedge clk or negedge rst)` patterns
2. Converts to `ALWAYS_FF_RST(clk, rst, ...)` macro
3. Converts `if (!rst)` to `if (RST_ASSERTED(rst))`
4. Adds `include "reset_defs.svh"` if missing
5. Preserves formatting and comments

**See also:** `bin/update_resets.py` source for implementation details

---

## Quick Commands

```bash
# Convert reset patterns to macros
python3 bin/update_resets.py projects/components/{component}/rtl/ --dry-run
python3 bin/update_resets.py projects/components/{component}/rtl/
cp UPDATED/*.sv projects/components/{component}/rtl/

# Run tests for a component
pytest projects/components/{component}/dv/tests/ -v

# Lint RTL
verilator --lint-only projects/components/{component}/rtl/*.sv

# Check for FPGA attributes
grep -r "ram_style\|ramstyle" projects/components/{component}/

# Find modules needing reset macro updates
grep -r "always_ff.*negedge" projects/components/{component}/

# View component documentation
cat projects/components/{component}/PRD.md
cat projects/components/{component}/CLAUDE.md
```

---

## Component-Specific Guides

Each component has its own CLAUDE.md and PRD.md files with detailed guidance:

### STREAM Component
- **Location:** `projects/components/stream/`
- **CLAUDE.md:** `projects/components/stream/CLAUDE.md`
- **PRD.md:** `projects/components/stream/PRD.md`
- **Focus:** Streaming datapath engines, AXI masters, SRAM control

### RAPIDS Component
- **Location:** `projects/components/rapids/`
- **CLAUDE.md:** `projects/components/rapids/CLAUDE.md`
- **PRD.md:** `projects/components/rapids/PRD.md`
- **Focus:** Descriptor-driven accelerators, scheduler groups

### APB HPET Component
- **Location:** `projects/components/apb_hpet/`
- **CLAUDE.md:** `projects/components/apb_hpet/CLAUDE.md`
- **PRD.md:** `projects/components/apb_hpet/PRD.md`
- **Focus:** APB peripherals, timers, register management

### Bridge Component
- **Location:** `projects/components/bridge/`
- **Focus:** Protocol converters, clock domain crossing

---

## Remember

1. Reset Macros - ALWAYS use `ALWAYS_FF_RST` from reset_defs.svh
2. FPGA Attributes - Add synthesis hints for all memory arrays
3. Array Syntax - Use `[DEPTH]` instead of `[0:DEPTH-1]`
4. SRAM Modules - NO reset ports on SRAM memories
5. Testbench Location - Project-specific TB classes in project dv/ area
6. Conversion Tool - Use bin/update_resets.py for bulk updates
7. No Emojis - Keep technical documentation plain text

---

**Version:** 1.0
**Last Updated:** 2025-10-24
**Maintained By:** RTL Design Sherpa Project
