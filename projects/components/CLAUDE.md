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

# Claude Code Guide: Projects/Components

**Version:** 1.0
**Last Updated:** 2025-10-24
**Purpose:** AI-specific guidance for working with projects/components area

---

## Quick Context

**What:** High-performance RTL components for custom accelerators and systems
**Status:** Active development - STREAM, RAPIDS, Bridge, Retro Legacy Blocks production blocks
**Your Role:** Help users develop new components following repository standards

**Key Projects:**
- **STREAM** - Streaming datapath engine with AXI and SRAM control (`dmas/stream/`)
- **RAPIDS** - Rapid AXI Programmable In-band Descriptor System (`dmas/rapids/`)
- **Bridge** - Protocol bridges and converters
- **Retro Legacy Blocks** - Legacy PC peripherals (HPET, PIT 8254, PIC 8259, RTC, ...) in `retro_legacy_blocks/` (absorbed the old apb4_hpet component)

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
- `bin/TBClasses/` - Shared TB framework (full CocoTBFramework lives in the separate RTLDesignSherpa-DV repo, editable-installed)
- `projects/components/{name}/CLAUDE.md` - Component-specific guidance

---

## Critical Standards for This Area

### Rule #0: Reset Handling Standards (MANDATORY)

**See:** `/GLOBAL_REQUIREMENTS.md` Section 1.1

This area is the primary enforcement zone -- `rtl/common/` and `rtl/amba/` are
already converted, so a new hand-written reset block lands here or nowhere.

```systemverilog
`include "reset_defs.svh"

`ALWAYS_FF_RST(clk, rst_n,
    if (`RST_ASSERTED(rst_n)) r_state <= IDLE;
    else                      r_state <= w_next_state;
)
```

Macros: `rtl/amba/includes/reset_defs.svh`. Bulk conversion:
`bin/update_resets.py`, documented once under Tools and Automation below.
Rationale: `vault/handbook/design/reset-and-clocking.md`.

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
- `rtl/amba/gaxi/gaxi_fifo_sync.sv` - FIFO memory with ram_style attributes (instantiated by STREAM's `sram_controller_unit.sv`)
- `rtl/common/fifo_sync.sv` - Common FIFO with attributes
- `rtl/amba/shared/sdpram_core.sv` - SRAM core with attributes

(The old `simple_sram.sv` example was removed; STREAM/RAPIDS buffers now use these shared FIFO/SRAM primitives.)

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

**See:** `/GLOBAL_REQUIREMENTS.md` Section 1.4

An SRAM primitive carries no reset port -- and you should not be writing one.
The shared primitives are `rtl/amba/shared/sdpram_core.sv` and
`rtl/amba/gaxi/gaxi_fifo_sync.sv`; STREAM and RAPIDS buffers are built on them
(see `sram_controller_unit.sv`). Details and the failure modes:
`vault/handbook/design/sram-and-memories.md`.

---

### Rule #4: TB Location (MANDATORY)

**📖 See:** `/GLOBAL_REQUIREMENTS.md` Section 2.1 for complete requirement

**Projects/Components-Specific Import Pattern:**

```python
# Import framework utilities (PYTHONPATH includes bin/)
import os, sys
from TBClasses.shared.utilities import get_repo_root
from TBClasses.shared.tbbase import TBBase

# Add repo root to Python path using robust git-based method
repo_root = get_repo_root()
sys.path.insert(0, repo_root)

# Import from PROJECT AREA (not framework!)
from projects.components.dmas.stream.dv.tbclasses.scheduler_tb import SchedulerTB

# Shared framework components (CocoTBFramework is editable-installed from RTLDesignSherpa-DV)
from CocoTBFramework.components.axi4.axi4_factories import create_axi4_slave_rd
```

**Examples:**
- `projects/components/dmas/rapids/dv/tbclasses/` - RAPIDS TBs
- `projects/components/dmas/stream/dv/tbclasses/` - STREAM TBs

---

## Common Patterns for New Components

Three sketch modules used to live here: `streaming_engine`, `descriptor_engine`
and `sram_buffer`. Each ended by naming the real module that does the same job
-- which is the one to read. The sketches had already drifted: Pattern 3
instantiated `simple_sram`, which exists nowhere in the repo, and Pattern 2
opened a four-state FSM one section after Pattern 1 said "NO FSM!".

| Shape | Read the real thing | The rule it follows |
|---|---|---|
| Streaming datapath, AXI read/write engine | `dmas/stream/rtl/fub/axi_read_engine.sv`, `axi_write_engine.sv` | no FSM in a streaming path -- `vault/handbook/design/streaming-no-fsm.md`, `valid-ready-contracts.md` |
| Descriptor-driven engine, scheduler | `dmas/stream/rtl/fub/descriptor_engine.sv`, `dmas/rapids/rtl/fub_beats/descriptor_engine_beats.sv` | keep the state count minimal -- `vault/handbook/design/minimal-fsm.md` |
| Buffer over SRAM | `dmas/stream/rtl/fub/sram_controller.sv`, `sram_controller_unit.sv` | the SRAM primitive is shared and takes no reset -- `vault/handbook/design/sram-and-memories.md` |

Paths above are relative to `projects/components/`. The shared primitives they
build on: `rtl/amba/shared/sdpram_core.sv`, `rtl/amba/gaxi/gaxi_fifo_sync.sv`,
`rtl/common/fifo_sync.sv`.

---

## Tools and Automation

### Reset Macro Conversion Script

**Script:** `bin/update_resets.py`

**Purpose:** Automatically convert manual `always_ff` blocks to reset macros

**Usage:**
```bash
# Dry-run to see what would change
python3 bin/update_resets.py projects/components/dmas/stream/rtl/ --dry-run

# Convert files (writes to UPDATED/ directory)
python3 bin/update_resets.py projects/components/dmas/stream/rtl/

# Review changes (UPDATED/ mirrors the tree relative to the source root)
diff -u projects/components/dmas/stream/rtl/fub/scheduler.sv UPDATED/fub/scheduler.sv

# Copy corrected files back
cp UPDATED/fub/*.sv projects/components/dmas/stream/rtl/fub/
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
# Tests go through the area Makefile, never bare pytest -- it supplies the
# level, the derived worker count and the reruns, and cleans first.
cd projects/components/{component}/dv/tests && make clean-all && make run-all-gate

# Lint
verilator --lint-only projects/components/{component}/rtl/*.sv

# Audit: memories missing synthesis hints, resets not yet on macros
grep -rL "ram_style\|ramstyle" projects/components/{component}/rtl/*.sv
grep -rn "always_ff.*negedge" projects/components/{component}/
```

---

## Component-Specific Guides

Each component carries its own CLAUDE.md and PRD.md -- read the one for the
area you are in. Paths relative to `projects/components/`.

| Component | Path | Focus |
|---|---|---|
| STREAM | `dmas/stream/` | streaming datapath engines, AXI masters, SRAM control |
| RAPIDS | `dmas/rapids/` | descriptor-driven accelerators, scheduler groups |
| Retro Legacy Blocks | `retro_legacy_blocks/` | legacy PC peripherals (HPET, PIT 8254, PIC 8259, RTC, ...), APB register maps |
| Bridge | `bridge/` | protocol converters, clock domain crossing |
| misc | `misc/` | reusable utility components: ROM/RAM wrappers, pattern generators |

---

**Version:** 1.0
**Last Updated:** 2025-10-24
**Maintained By:** RTL Design Sherpa Project
