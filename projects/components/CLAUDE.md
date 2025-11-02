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

## Critical Standards for This Area

### Rule #0: Reset Handling Standards

**MANDATORY: All new RTL MUST use standardized reset macros from `rtl/amba/includes/reset_defs.svh`**

**Why This Matters:**
- Consistent reset handling across all modules
- FPGA-friendly asynchronous reset with synchronous release
- Easy modification of reset polarity via single macro
- Better synthesis and timing closure

**Include in All New RTL Files:**
```systemverilog
`include "reset_defs.svh"
```

**Standard Pattern - Use `ALWAYS_FF_RST` Macro:**
```systemverilog
// OLD PATTERN (DO NOT USE):
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        r_state <= IDLE;
        r_counter <= '0;
    end else begin
        r_state <= w_next_state;
        r_counter <= r_counter + 1'b1;
    end
end

// NEW PATTERN (REQUIRED):
`ALWAYS_FF_RST(clk, rst_n,
    if (`RST_ASSERTED(rst_n)) begin
        r_state <= IDLE;
        r_counter <= '0;
    end else begin
        r_state <= w_next_state;
        r_counter <= r_counter + 1'b1;
    end
)
```

**Macro Definitions:**
- `ALWAYS_FF_RST(clk, rst, ...)` - Always block with async reset
- `RST_ASSERTED(rst)` - Test if reset is asserted (handles polarity)
- `RST_RELEASED(rst)` - Test if reset is released

**Reset Signal Naming Conventions:**
- `rst_n` - Active-low reset (most common in projects/components)
- `aresetn` - Active-low asynchronous reset (AMBA protocol standard)
- Use actual signal name in macro, NOT a sync_ prefix

**Conversion Tool:**
```bash
# Convert existing always_ff blocks to reset macros
python3 bin/update_resets.py projects/components/{component}/rtl/

# Files written to UPDATED/ directory, review before copying back
```

**⚠️ THIS IS A HARD REQUIREMENT - NO EXCEPTIONS ⚠️**

This is NOT a suggestion or guideline - it is a MANDATORY requirement for ALL RTL in projects/components/:

1. **ALL new RTL files** MUST use reset macros from the day they are created
2. **ALL existing RTL files** MUST be converted to use reset macros before any new features are added
3. **PRs will be REJECTED** if they contain manual `always_ff @(posedge clk or negedge rst_n)` patterns
4. **Use the conversion tool** - It is tested, reliable, and maintains functional equivalence

**Why This is Non-Negotiable:**
- Enables FPGA inference of proper reset resources (critical for timing closure)
- Ensures consistent synthesis across Xilinx, Intel, and ASIC flows
- Allows single-point reset polarity changes for IP reuse
- Prevents subtle reset-related bugs (metastability, incomplete resets)

**Historical Context:**
- APB HPET was developed before reset macro standardization (now converted)
- All rtl/common/ and rtl/amba/ modules use reset macros (100% compliance)
- projects/components/ must match repository standards

**See also:** `rtl/amba/includes/reset_defs.svh` for complete macro definitions

---

### Rule #1: FPGA Synthesis Attributes

**MANDATORY: Add FPGA synthesis hints for all memory arrays**

**Why This Matters:**
- FPGA tools infer better memory architectures (block RAM vs distributed RAM)
- Prevents logic explosion for large memories
- Enables vendor-specific optimizations
- Cross-vendor compatibility (Xilinx, Intel/Altera)

**Standard Pattern for Memory Arrays:**
```systemverilog
// CORRECT: FPGA-friendly memory with synthesis hints
`ifdef XILINX
    (* ram_style = "auto" *)  // Let Xilinx decide block vs distributed
`elsif INTEL
    /* synthesis ramstyle = "AUTO" */  // Let Intel Quartus decide
`endif
logic [DATA_WIDTH-1:0] mem [DEPTH];  // Use [DEPTH], not [0:DEPTH-1]

// For small memories that MUST be distributed RAM:
`ifdef XILINX
    (* ram_style = "distributed" *)
`elsif INTEL
    /* synthesis ramstyle = "MLAB" */
`endif
logic [DATA_WIDTH-1:0] small_mem [16];

// For large memories that MUST be block RAM:
`ifdef XILINX
    (* ram_style = "block" *)
`elsif INTEL
    /* synthesis ramstyle = "M20K" */
`endif
logic [DATA_WIDTH-1:0] large_mem [4096];
```

**Available Xilinx Attributes:**
- `ram_style = "auto"` - Let tool decide (recommended default)
- `ram_style = "block"` - Force block RAM (BRAM/URAM)
- `ram_style = "distributed"` - Force distributed RAM (LUT RAM)
- `ram_style = "ultra"` - Force UltraRAM (Ultrascale+ only)

**Available Intel Attributes:**
- `ramstyle = "AUTO"` - Let tool decide (recommended default)
- `ramstyle = "M20K"` - Force M20K block RAM
- `ramstyle = "MLAB"` - Force MLAB distributed RAM
- `ramstyle = "logic"` - Force logic (registers)

**Other Useful FPGA Attributes:**
```systemverilog
// DSP inference control
`ifdef XILINX
    (* use_dsp = "yes" *)  // Force DSP48 usage for multiply
`endif
logic [31:0] product = a * b;

// Shift register inference
`ifdef XILINX
    (* shreg_extract = "no" *)  // Prevent SRL inference
`endif
logic [7:0] pipe_stage;
```

**See also:**
- `rtl/common/fifo_sync.sv` - Example with FPGA attributes
- `projects/components/stream/rtl/stream_fub/simple_sram.sv` - Memory with attributes

---

### Rule #2: Array Syntax Standards

**MANDATORY: Use unpacked array syntax `[DEPTH]` instead of `[0:DEPTH-1]`**

**Why This Matters:**
- Iverilog compatibility (some versions require this syntax)
- Cleaner, more readable code
- Consistent with SystemVerilog best practices
- Avoids off-by-one errors in indexing

**Standard Pattern:**
```systemverilog
// WRONG (old style):
logic [DATA_WIDTH-1:0] mem [0:DEPTH-1];

// CORRECT (use this):
logic [DATA_WIDTH-1:0] mem [DEPTH];
```

**Memory Initialization:**
```systemverilog
// Initialize all elements to zero
logic [DATA_WIDTH-1:0] mem [DEPTH] = '{default:0};

// Initialize with specific values
logic [7:0] lut [16] = '{
    8'h00, 8'h01, 8'h02, 8'h03,
    8'h04, 8'h05, 8'h06, 8'h07,
    8'h08, 8'h09, 8'h0A, 8'h0B,
    8'h0C, 8'h0D, 8'h0E, 8'h0F
};
```

---

### Rule #3: SRAM and Memory Module Standards

**SRAM Modules DO NOT Have Reset Ports**

**Why This Matters:**
- Real SRAM chips don't have reset pins
- FPGA block RAM doesn't reset contents
- Resetting large memories wastes silicon area and power
- Initialize via writes during system initialization

**Correct SRAM Module Interface:**
```systemverilog
module simple_sram #(
    parameter int DATA_WIDTH = 32,
    parameter int DEPTH = 1024
) (
    input  logic                        clk,
    // NO rst_n port!

    // Write port
    input  logic                        wr_en,
    input  logic [$clog2(DEPTH)-1:0]    wr_addr,
    input  logic [DATA_WIDTH-1:0]       wr_data,

    // Read port
    input  logic                        rd_en,
    input  logic [$clog2(DEPTH)-1:0]    rd_addr,
    output logic [DATA_WIDTH-1:0]       rd_data
);

    // Memory array with FPGA hints
    `ifdef XILINX
        (* ram_style = "auto" *)
    `elsif INTEL
        /* synthesis ramstyle = "AUTO" */
    `endif
    logic [DATA_WIDTH-1:0] mem [DEPTH] = '{default:0};

    // Write logic (no reset)
    always_ff @(posedge clk) begin
        if (wr_en) begin
            mem[wr_addr] <= wr_data;
        end
    end

    // Read logic (no reset, optional output register)
    always_ff @(posedge clk) begin
        if (rd_en) begin
            rd_data <= mem[rd_addr];
        end
    end

endmodule : simple_sram
```

**SRAM Controller Initialization Pattern:**
```systemverilog
// SRAM controller with reset, but SRAM itself has no reset
module sram_controller #(
    parameter int SRAM_DEPTH = 4096
) (
    input  logic        clk,
    input  logic        rst_n,  // Controller has reset
    // ... other ports
);

    // Controller state machine with reset
    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_state <= IDLE;
            r_wr_ptr <= '0;
            r_rd_ptr <= '0;
        end else begin
            // State machine logic
        end
    )

    // SRAM instance - NO reset port
    simple_sram #(
        .DATA_WIDTH(512),
        .DEPTH(SRAM_DEPTH)
    ) u_sram (
        .clk      (clk),
        // No .rst_n connection!
        .wr_en    (sram_wr_en),
        .wr_addr  (r_wr_ptr),
        .wr_data  (sram_wr_data),
        .rd_en    (sram_rd_en),
        .rd_addr  (r_rd_ptr),
        .rd_data  (sram_rd_data)
    );

endmodule : sram_controller
```

**See also:**
- `projects/components/stream/rtl/stream_fub/simple_sram.sv` - Example SRAM
- `projects/components/stream/rtl/stream_fub/sram_controller.sv` - Example controller

---

### Rule #4: Testbench Architecture - Project-Specific TB Classes

**MANDATORY: Project-specific testbench classes MUST be in project dv/ area**

**Why This Matters:**
- Easy discovery - All project code in one place
- Clear ownership - Each project owns their dv/ area
- No confusion - Never wonder where TB classes live
- Framework stays clean - Only truly shared code in framework

**Directory Structure:**
```
projects/components/{project}/
├── rtl/                    # RTL source
├── dv/                     # Design Verification
│   ├── tbclasses/          # PROJECT-SPECIFIC TB classes HERE
│   │   ├── {module}_tb.py
│   │   └── {feature}_tb.py
│   ├── components/         # PROJECT-SPECIFIC BFM extensions (if needed)
│   └── tests/              # Test runners
│       ├── conftest.py
│       └── test_*.py
└── docs/                   # Documentation
```

**Correct Import Pattern:**
```python
# Add repo root to Python path
import os, sys
repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../../../..'))
sys.path.insert(0, repo_root)

# Import PROJECT-SPECIFIC TB classes from project area
from projects.components.stream.dv.tbclasses.scheduler_tb import SchedulerTB
from projects.components.rapids.dv.tbclasses.descriptor_engine_tb import DescriptorEngineTB

# Shared framework utilities still come from framework
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.axi4.axi4_master import AXI4Master
```

**Decision Tree:**
```
Is this testbench code specific to ONE project?
├─ YES → projects/components/{project}/dv/tbclasses/
│
└─ NO → Is it reusable across MULTIPLE projects?
   ├─ YES → bin/CocoTBFramework/
   └─ UNSURE → Default to project area
```

**See also:**
- Root `/CLAUDE.md` Section "Organizational Requirements" for complete details
- `projects/components/rapids/dv/tbclasses/` - RAPIDS examples
- `projects/components/stream/dv/tbclasses/` - STREAM examples

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
